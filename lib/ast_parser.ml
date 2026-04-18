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
  | Block stmts ->
      normalize_stmt (Seq stmts)
  | LocalDecl _ ->
      failwith "internal error: unresolved local declaration reached normalization"
  | If (c, t, e) -> If (c, normalize_stmt t, normalize_stmt e)
  | While (invariant, c, body) ->
      let body = normalize_stmt body in
      (match invariant with
      | Some loop_invariant when loop_invariant = c && body = Skip ->
          Assume (negate_bexpr c)
      | _ -> While (invariant, c, body))
  | ArrayAssign (base, index, value) -> ArrayAssign (base, index, value)
  | FieldAssign (base, field, value) -> FieldAssign (base, field, value)
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

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

type resolved_local_binding = {
  resolved_name : string;
  resolved_type : c_type;
}

type scope = (string * resolved_local_binding) list

type resolve_state = {
  function_name : string;
  next_local : int;
  locals_rev : global_def list;
}

let seq_of_list = function
  | [] -> Skip
  | [stmt] -> stmt
  | stmts -> Seq stmts

let fresh_local_name state source_name =
  let resolved_name =
    Printf.sprintf "__anvil_local_%s_%d_%s"
      state.function_name state.next_local source_name
  in
  resolved_name,
  { state with next_local = state.next_local + 1 }

let resolved_local_prefix function_name =
  "__anvil_local_" ^ function_name ^ "_"

let resolved_local_name_index function_name name =
  let prefix = resolved_local_prefix function_name in
  let prefix_length = String.length prefix in
  if String.length name <= prefix_length || String.sub name 0 prefix_length <> prefix then
    None
  else
    let rest =
      String.sub name prefix_length (String.length name - prefix_length)
    in
    match String.index_opt rest '_' with
    | None -> None
    | Some underscore ->
        let index_text = String.sub rest 0 underscore in
        (try Some (int_of_string index_text) with
        | Failure _ -> None)

let binding_in_current_scope scopes source_name =
  match scopes with
  | [] -> None
  | current_scope :: _ ->
      assoc_opt source_name current_scope

let binding_in_scopes scopes source_name =
  let rec loop = function
    | [] -> None
    | current_scope :: rest ->
        (match assoc_opt source_name current_scope with
        | Some _ as binding -> binding
        | None -> loop rest)
  in
  loop scopes

let add_binding scopes source_name binding =
  match scopes with
  | [] -> failwith "internal error: missing scope while resolving locals"
  | current_scope :: rest ->
      if Option.is_some (assoc_opt source_name current_scope) then
        failwith
          (Printf.sprintf
             "duplicate local declaration `%s` in `%s`"
             source_name
             binding.resolved_name)
      else
        ((source_name, binding) :: current_scope) :: rest

let rec resolve_expr scopes = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr -> expr
  | Var name ->
      (match binding_in_scopes scopes name with
      | Some binding -> Var binding.resolved_name
      | None -> Var name)
  | AddrOf expr -> AddrOf (resolve_expr scopes expr)
  | Index (base, index) ->
      Index (resolve_expr scopes base, resolve_expr scopes index)
  | Deref expr -> Deref (resolve_expr scopes expr)
  | Field (base, field) ->
      Field (resolve_expr scopes base, field)
  | Add (left, right) ->
      Add (resolve_expr scopes left, resolve_expr scopes right)
  | Sub (left, right) ->
      Sub (resolve_expr scopes left, resolve_expr scopes right)
  | Mul (left, right) ->
      Mul (resolve_expr scopes left, resolve_expr scopes right)
  | Div (left, right) ->
      Div (resolve_expr scopes left, resolve_expr scopes right)
  | Mod (left, right) ->
      Mod (resolve_expr scopes left, resolve_expr scopes right)
  | FuncCall (name, args) ->
      FuncCall (name, List.map (resolve_expr scopes) args)

let rec resolve_bexpr scopes = function
  | True -> True
  | False -> False
  | Eq (left, right) ->
      Eq (resolve_expr scopes left, resolve_expr scopes right)
  | Neq (left, right) ->
      Neq (resolve_expr scopes left, resolve_expr scopes right)
  | Lt (left, right) ->
      Lt (resolve_expr scopes left, resolve_expr scopes right)
  | Le (left, right) ->
      Le (resolve_expr scopes left, resolve_expr scopes right)
  | Gt (left, right) ->
      Gt (resolve_expr scopes left, resolve_expr scopes right)
  | Ge (left, right) ->
      Ge (resolve_expr scopes left, resolve_expr scopes right)
  | Not inner -> Not (resolve_bexpr scopes inner)
  | And (left, right) ->
      And (resolve_bexpr scopes left, resolve_bexpr scopes right)
  | Or (left, right) ->
      Or (resolve_bexpr scopes left, resolve_bexpr scopes right)

let resolve_assign_target scopes name =
  match binding_in_scopes scopes name with
  | Some binding -> binding.resolved_name
  | None -> name

let rec resolve_stmt scopes state stmt =
  match stmt with
  | Skip -> Ok (Skip, state, scopes)
  | Block stmts ->
      let* stmts, state =
        resolve_stmt_list ([] :: scopes) state stmts
      in
      Ok (seq_of_list stmts, state, scopes)
  | LocalDecl (local, init) ->
      if Option.is_some (binding_in_current_scope scopes local.global_name) then
        Error
          (Printf.sprintf
             "duplicate local declaration `%s` in `%s`"
             local.global_name
             state.function_name)
      else
        let resolved_name, state =
          match resolved_local_name_index state.function_name local.global_name with
          | Some index ->
              local.global_name,
              { state with next_local = max state.next_local (index + 1) }
          | None ->
              fresh_local_name state local.global_name
        in
        let binding =
          { resolved_name; resolved_type = local.global_type }
        in
        let scopes = add_binding scopes local.global_name binding in
        let local =
          { global_type = local.global_type; global_name = resolved_name }
        in
        let state = { state with locals_rev = local :: state.locals_rev } in
        let* init_stmt =
          match init with
          | None -> Ok (Seq [])
          | Some expr ->
              if is_array_type local.global_type then
                Error
                  (Printf.sprintf
                     "array local initializer for `%s` is unsupported"
                     local.global_name)
              else
                Ok (Assign (resolved_name, resolve_expr scopes expr))
        in
        Ok (init_stmt, state, scopes)
  | Assign (name, expr) ->
      Ok
        ( Assign (resolve_assign_target scopes name, resolve_expr scopes expr)
        , state
        , scopes )
  | Store (ptr, value) ->
      Ok (Store (resolve_expr scopes ptr, resolve_expr scopes value), state, scopes)
  | ArrayAssign (base, index, value) ->
      Ok
        ( ArrayAssign
            ( resolve_expr scopes base
            , resolve_expr scopes index
            , resolve_expr scopes value )
        , state
        , scopes )
  | FieldAssign (base, field, value) ->
      Ok
        ( FieldAssign
            (resolve_expr scopes base, field, resolve_expr scopes value)
        , state
        , scopes )
  | Seq stmts ->
      let* stmts, state = resolve_stmt_list scopes state stmts in
      Ok (seq_of_list stmts, state, scopes)
  | If (cond, then_branch, else_branch) ->
      let* then_branch, state, _ =
        resolve_stmt scopes state then_branch
      in
      let* else_branch, state, _ =
        resolve_stmt scopes state else_branch
      in
      Ok (If (resolve_bexpr scopes cond, then_branch, else_branch), state, scopes)
  | While (invariant, cond, body) ->
      let invariant =
        Option.map (resolve_bexpr scopes) invariant
      in
      let* body, state, _ = resolve_stmt scopes state body in
      Ok (While (invariant, resolve_bexpr scopes cond, body), state, scopes)
  | Assume cond ->
      Ok (Assume (resolve_bexpr scopes cond), state, scopes)
  | Assert (origin, cond) ->
      Ok (Assert (origin, resolve_bexpr scopes cond), state, scopes)
  | Free ptr ->
      Ok (Free (resolve_expr scopes ptr), state, scopes)
  | Return value ->
      Ok (Return (Option.map (resolve_expr scopes) value), state, scopes)

and resolve_stmt_list scopes state stmts =
  match stmts with
  | [] -> Ok ([], state)
  | stmt :: rest ->
      let* stmt, state, scopes' = resolve_stmt scopes state stmt in
      let* rest, state = resolve_stmt_list scopes' state rest in
      (match stmt with
      | Seq [] -> Ok (rest, state)
      | _ -> Ok (stmt :: rest, state))

let initial_scope_for_function (fn : function_def) =
  let scope_from_param param =
    match param.param_name with
    | None -> None
    | Some name ->
        Some (name, { resolved_name = name; resolved_type = param.param_type })
  in
  List.filter_map scope_from_param fn.params

let resolve_function_locals (fn : function_def) =
  let state =
    { function_name = fn.name; next_local = 0; locals_rev = List.rev fn.locals }
  in
  let* body, state, _ =
    resolve_stmt [initial_scope_for_function fn] state fn.body
  in
  Ok { fn with locals = List.rev state.locals_rev; body = normalize_stmt body }

let resolve_program_locals program =
  let* functions =
    let rec loop acc = function
      | [] -> Ok (List.rev acc)
      | fn :: rest ->
          let* fn = resolve_function_locals fn in
          loop (fn :: acc) rest
    in
    loop [] program.functions
  in
  let* main = resolve_function_locals program.main in
  Ok { program with functions; main }

let rec attach_loop_invariants_stmt source_name invariants stmt =
  match stmt with
  | Skip | LocalDecl _ | Assign _ | Store _ | ArrayAssign _ | FieldAssign _ | Assume _ | Assert _ | Free _ | Return _ ->
      stmt, invariants
  | Block stmts ->
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
      Block (List.rev stmts), invariants
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
    let* program = resolve_program_locals program in
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
