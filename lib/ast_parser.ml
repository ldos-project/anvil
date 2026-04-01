open Ast

let negate_bexpr = function
  | Not inner -> inner
  | other -> Not other

let rec normalize_stmt = function
  | Seq ss ->
      let ss =
        ss
        |> List.map normalize_stmt
        |> List.concat_map (function
             | Seq inner -> inner
             | stmt -> [stmt])
      in
      (match ss with
      | [] -> Skip
      | [stmt] -> stmt
      | _ -> Seq ss)
  | If (c, t, e) -> If (c, normalize_stmt t, normalize_stmt e)
  | While (invariant, c, body) ->
      let body = normalize_stmt body in
      (match invariant with
      | Some loop_invariant when loop_invariant = c && body = Skip ->
          Assume (negate_bexpr c)
      | _ -> While (invariant, c, body))
  | Store (ptr, value) -> Store (ptr, value)
  | Assume _ as stmt -> stmt
  | Assert _ as stmt -> stmt
  | Free ptr -> Free ptr
  | Return _ as stmt -> stmt
  | Skip -> Skip
  | Assign _ as stmt -> stmt

let normalize_function fn = { fn with body = normalize_stmt fn.body }

let normalize_program p =
  {
    p with
    functions = List.map normalize_function p.functions;
    main = normalize_function p.main;
  }

let equal_program p q = normalize_program p = normalize_program q

let assoc_opt key bindings =
  List.find_map
    (fun (name, value) ->
      if String.equal name key then Some value else None)
    bindings

let signature_compatible params_a params_b =
  List.length params_a = List.length params_b
  && List.for_all2
       (fun left right -> left.param_type = right.param_type)
       params_a params_b

let function_compatible
    (fn : function_def)
    (contract_fn : contracted_function) =
  fn.return_type = contract_fn.return_type
  && signature_compatible fn.params contract_fn.params

let build_defined_contract_env source_name (contracts : contracted_function list) =
  let rec loop
      (env : (string * contracted_function) list)
      (contracts : contracted_function list) =
    match contracts with
    | [] -> env
    | (contract_fn : contracted_function) :: rest ->
        (match assoc_opt contract_fn.name env with
        | Some _ ->
            failwith
              (Printf.sprintf
                 "duplicate contracted function definition `%s` in %s"
                 contract_fn.name
                 source_name)
        | None -> loop ((contract_fn.name, contract_fn) :: env) rest)
  in
  loop [] contracts

let attach_contract
    source_name
    (env : (string * contracted_function) list)
    (fn : function_def) =
  match assoc_opt fn.name env with
  | None -> fn
  | Some contract_fn ->
      if function_compatible fn contract_fn then
        { fn with contract = Some contract_fn.contract }
      else
        failwith
          (Printf.sprintf
             "contract signature mismatch for function `%s` in %s"
             fn.name
             source_name)

let position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
  Printf.sprintf "line %d, column %d" pos.Lexing.pos_lnum column

let parse_contract_bexpr context source =
  let lexbuf = Lexing.from_string source in
  try Ok (Parser.contract_bexpr_eof Lexer.read lexbuf) with
  | Lexer.Syntax_error msg ->
      Error (Printf.sprintf "%s in %s at %s" msg context (position lexbuf))
  | Parser.Error ->
      Error (Printf.sprintf "parse error in %s at %s" context (position lexbuf))

let parse_c_bexpr context source =
  let lexbuf = Lexing.from_string source in
  try Ok (Parser.bexpr_eof Lexer.read lexbuf) with
  | Lexer.Syntax_error msg ->
      Error (Printf.sprintf "%s in %s at %s" msg context (position lexbuf))
  | Parser.Error ->
      Error (Printf.sprintf "parse error in %s at %s" context (position lexbuf))

let parse_loop_invariant source_name annotation =
  match
    parse_contract_bexpr
      (Printf.sprintf "@Invariant in %s at line %d" source_name annotation.Loop_annotations.line_number)
      annotation.Loop_annotations.text
  with
  | Ok invariant -> invariant
  | Error _ ->
      (match
         parse_c_bexpr
           (Printf.sprintf "@Invariant in %s at line %d" source_name annotation.Loop_annotations.line_number)
           annotation.Loop_annotations.text
       with
      | Ok invariant -> invariant
      | Error message -> failwith message)

let rec attach_loop_invariants_stmt source_name invariants stmt =
  match stmt with
  | Skip | Assign _ | Store _ | Assume _ | Assert _ | Free _ | Return _ ->
      stmt, invariants
  | Seq stmts ->
      let stmts, invariants =
        List.fold_left
          (fun (stmts_rev, invariants) stmt ->
            let stmt, invariants =
              attach_loop_invariants_stmt source_name invariants stmt
            in
            stmt :: stmts_rev, invariants)
          ([], invariants)
          stmts
      in
      Seq (List.rev stmts), invariants
  | If (cond, then_branch, else_branch) ->
      let then_branch, invariants =
        attach_loop_invariants_stmt source_name invariants then_branch
      in
      let else_branch, invariants =
        attach_loop_invariants_stmt source_name invariants else_branch
      in
      If (cond, then_branch, else_branch), invariants
  | While (_, cond, body) ->
      (match invariants with
      | [] ->
          failwith
            (Printf.sprintf
               "internal error: missing loop annotation slot while attaching invariants in %s"
               source_name)
      | invariant :: invariants ->
          let invariant =
            Option.map (parse_loop_invariant source_name) invariant
          in
          let body, invariants =
            attach_loop_invariants_stmt source_name invariants body
          in
          While (invariant, cond, body), invariants)

let attach_loop_invariants_function source_name invariants fn =
  let body, invariants = attach_loop_invariants_stmt source_name invariants fn.body in
  { fn with body }, invariants

let attach_loop_invariants source_name invariants program =
  let functions_rev, invariants =
    List.fold_left
      (fun (functions_rev, invariants) fn ->
        let fn, invariants =
          attach_loop_invariants_function source_name invariants fn
        in
        fn :: functions_rev, invariants)
      ([], invariants)
      program.functions
  in
  let main, invariants =
    attach_loop_invariants_function source_name invariants program.main
  in
  match invariants with
  | [] -> { program with functions = List.rev functions_rev; main }
  | _ :: _ ->
      failwith
        (Printf.sprintf
           "internal error: unconsumed loop annotations remain after attaching invariants in %s"
           source_name)

let parse_program
    ?(base_dir = Sys.getcwd ())
    ?(source_name = "<input>")
    source =
  let lexbuf = Lexing.from_string source in
  try
    let imports = Header_contracts.load_imports ~base_dir source in
    let defined_contracts =
      Header_contracts.load_defined_contracts ~source_path:source_name source
    in
    let loop_invariants = Loop_annotations.load ~source_path:source_name source in
    let defined_contracts = build_defined_contract_env source_name defined_contracts in
    let program =
      Parser.program Lexer.read lexbuf
      |> attach_loop_invariants source_name loop_invariants
    in
    Ok
      (normalize_program
         {
           program with
           imports;
           functions =
             List.map (attach_contract source_name defined_contracts) program.functions;
           main = attach_contract source_name defined_contracts program.main;
         })
  with
  | Header_contracts.Error msg ->
      Error msg
  | Loop_annotations.Error msg ->
      Error msg
  | Lexer.Syntax_error msg ->
      Error (Printf.sprintf "%s at %s" msg (position lexbuf))
  | Failure msg ->
      Error msg
  | Parser.Error ->
      Error (Printf.sprintf "parse error at %s" (position lexbuf))
