open Ast

module Ir = Z3_ir

type query = {
  label : string;
  term : Ir.int_expr;
}

type verification_condition = {
  name : string;
  formula : Ir.formula;
  queries : query list;
}

type counterexample = {
  condition_name : string;
  condition : string;
  bindings : (string * string) list;
}

type inconclusive = {
  condition_name : string;
  reason : string;
}

type outcome =
  | Verified
  | Counterexample of counterexample
  | Inconclusive of inconclusive

type sexp =
  | Atom of string
  | List of sexp list

type sat_result =
  | Sat
  | Unsat
  | Unknown

type vc_state = {
  function_name : string;
  next_loop : int;
  vcs_rev : verification_condition list;
}

let fail fmt = Printf.ksprintf failwith fmt

let read_all in_channel =
  let buffer = Buffer.create 1024 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    match input in_channel chunk 0 (Bytes.length chunk) with
    | 0 -> Buffer.contents buffer
    | n ->
        Buffer.add_subbytes buffer chunk 0 n;
        loop ()
  in
  loop ()

let rec expr_to_ir = function
  | Int n -> Ir.Int_lit n
  | Var name -> Ir.Var name
  | AddrOf _ | Deref _ ->
      failwith "pointer expressions should be lowered before verification"
  | Add (left, right) -> Ir.Add [expr_to_ir left; expr_to_ir right]
  | Sub (left, right) -> Ir.Sub (expr_to_ir left, expr_to_ir right)
  | Mul (left, right) -> Ir.Mul [expr_to_ir left; expr_to_ir right]
  | Div (left, right) -> Ir.Div (expr_to_ir left, expr_to_ir right)
  | Mod (left, right) -> Ir.Mod (expr_to_ir left, expr_to_ir right)
  | FuncCall (name, args) -> Ir.App (name, List.map expr_to_ir args)

let rec bexpr_to_ir = function
  | True -> Ir.True
  | False -> Ir.False
  | Eq (left, right) -> Ir.Eq (expr_to_ir left, expr_to_ir right)
  | Neq (left, right) -> Ir.Neq (expr_to_ir left, expr_to_ir right)
  | Lt (left, right) -> Ir.Lt (expr_to_ir left, expr_to_ir right)
  | Le (left, right) -> Ir.Le (expr_to_ir left, expr_to_ir right)
  | Gt (left, right) -> Ir.Gt (expr_to_ir left, expr_to_ir right)
  | Ge (left, right) -> Ir.Ge (expr_to_ir left, expr_to_ir right)
  | Not inner -> Ir.mk_not (bexpr_to_ir inner)
  | And (left, right) -> Ir.mk_and [bexpr_to_ir left; bexpr_to_ir right]
  | Or (left, right) -> Ir.mk_or [bexpr_to_ir left; bexpr_to_ir right]

let sort_queries queries =
  List.sort
    (fun left right -> String.compare left.label right.label)
    queries

let make_vc name formula =
  let var_queries =
    Ir.collect_vars formula
    |> List.map (fun name -> { label = name; term = Ir.Var name })
  in
  let app_queries =
    Ir.collect_apps formula
    |> List.map (fun (_, term) ->
           { label = Ir.int_expr_to_pretty term; term })
  in
  { name; formula; queries = sort_queries (var_queries @ app_queries) }

let add_vc state name formula =
  { state with vcs_rev = make_vc name formula :: state.vcs_rev }

let rec wp_stmt state stmt post =
  match stmt with
  | Skip -> post, state
  | Assign (name, expr) ->
      Ir.subst_formula name (expr_to_ir expr) post, state
  | Store _ | Free _ ->
      failwith "pointer statements should be lowered before verification"
  | Seq stmts ->
      List.fold_right
        (fun stmt (post, state) -> wp_stmt state stmt post)
        stmts
        (post, state)
  | If (cond, then_branch, else_branch) ->
      let then_pre, state = wp_stmt state then_branch post in
      let else_pre, state = wp_stmt state else_branch post in
      ( Ir.mk_and
          [ Ir.mk_implies (bexpr_to_ir cond) then_pre
          ; Ir.mk_implies (Ir.mk_not (bexpr_to_ir cond)) else_pre
          ]
      , state )
  | While (invariant_opt, cond, body) ->
      let loop_id = state.next_loop in
      let state = { state with next_loop = loop_id + 1 } in
      let invariant =
        match invariant_opt with
        | None -> post
        | Some invariant -> bexpr_to_ir invariant
      in
      let body_pre, state = wp_stmt state body invariant in
      let preservation =
        Ir.mk_implies
          (Ir.mk_and [invariant; bexpr_to_ir cond])
          body_pre
      in
      let preservation_name =
        Printf.sprintf "%s: loop %d preservation" state.function_name loop_id
      in
      let state = add_vc state preservation_name preservation in
      let exit_condition =
        Ir.mk_implies
          (Ir.mk_and [invariant; Ir.mk_not (bexpr_to_ir cond)])
          post
      in
      let exit_name =
        Printf.sprintf "%s: loop %d exit" state.function_name loop_id
      in
      invariant, add_vc state exit_name exit_condition
  | Assume cond ->
      Ir.mk_implies (bexpr_to_ir cond) post, state
  | Assert cond ->
      Ir.mk_and [bexpr_to_ir cond; post], state
  | Return _ -> Ir.True, state

let vcs_for_function (fn : function_def) =
  let state = { function_name = fn.name; next_loop = 0; vcs_rev = [] } in
  let precondition, state = wp_stmt state fn.body Ir.True in
  List.rev (make_vc (fn.name ^ ": entry") precondition :: state.vcs_rev)

let vcs_for_program (program : program) =
  List.concat_map vcs_for_function (program.functions @ [program.main])

let with_temp_file prefix suffix f =
  let path = Filename.temp_file prefix suffix in
  Fun.protect
    ~finally:(fun () ->
      try Sys.remove path with
      | Sys_error _ -> ())
    (fun () -> f path)

let run_z3 commands =
  with_temp_file "anvil-z3" ".smt2" (fun path ->
      let out_channel = open_out_bin path in
      Fun.protect
        ~finally:(fun () -> close_out_noerr out_channel)
        (fun () -> output_string out_channel (Ir.script_to_smt commands));
      let command = "z3 -smt2 " ^ Filename.quote path in
      let stdout_channel, stdin_channel, stderr_channel =
        Unix.open_process_full command (Unix.environment ())
      in
      let stdout =
        Fun.protect
          ~finally:(fun () ->
            close_out_noerr stdin_channel;
            close_in_noerr stdout_channel;
            close_in_noerr stderr_channel)
          (fun () ->
            let stdout = read_all stdout_channel in
            let stderr = read_all stderr_channel in
            stdout, stderr)
      in
      let stdout, stderr = stdout in
      let status =
        match Unix.close_process_full (stdout_channel, stdin_channel, stderr_channel) with
        | Unix.WEXITED 0 -> Ok ()
        | Unix.WEXITED n ->
            Error (Printf.sprintf "z3 exited with status %d" n)
        | Unix.WSIGNALED n ->
            Error (Printf.sprintf "z3 terminated by signal %d" n)
        | Unix.WSTOPPED n ->
            Error (Printf.sprintf "z3 stopped by signal %d" n)
      in
      match status with
      | Error message when stderr <> "" ->
          Error (message ^ ": " ^ String.trim stderr)
      | Error message -> Error message
      | Ok () when stderr <> "" && stdout = "" ->
          Error (String.trim stderr)
      | Ok () -> Ok stdout)

let is_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let parse_sexps text =
  let len = String.length text in
  let rec skip i =
    if i < len && is_space text.[i] then skip (i + 1) else i
  in
  let rec parse_atom i j =
    if j < len && not (is_space text.[j]) && text.[j] <> '(' && text.[j] <> ')' then
      parse_atom i (j + 1)
    else
      Atom (String.sub text i (j - i)), j
  in
  let rec parse_list i =
    let rec loop acc i =
      let i = skip i in
      if i >= len then fail "unterminated s-expression"
      else if text.[i] = ')' then
        List (List.rev acc), i + 1
      else
        let item, i = parse_one i in
        loop (item :: acc) i
    in
    loop [] i
  and parse_one i =
    let i = skip i in
    if i >= len then fail "unexpected end of s-expression"
    else
      match text.[i] with
      | '(' -> parse_list (i + 1)
      | ')' -> fail "unexpected `)` in s-expression"
      | _ -> parse_atom i i
  in
  let rec many acc i =
    let i = skip i in
    if i >= len then List.rev acc
    else
      let sexp, i = parse_one i in
      many (sexp :: acc) i
  in
  many [] 0

let rec sexp_to_string = function
  | Atom text -> text
  | List [Atom "-"; Atom value] -> "-" ^ value
  | List parts ->
      "(" ^ String.concat " " (List.map sexp_to_string parts) ^ ")"

let sat_result_of_output output =
  match parse_sexps output with
  | Atom "sat" :: _ -> Sat
  | Atom "unsat" :: _ -> Unsat
  | Atom "unknown" :: _ -> Unknown
  | sexps ->
      fail
        "unexpected z3 response: %s"
        (String.concat " " (List.map sexp_to_string sexps))

let parse_value_response = function
  | List [List [_term; value]] -> sexp_to_string value
  | sexp ->
      fail "unexpected get-value response: %s" (sexp_to_string sexp)

let declarations_for_vc vc =
  let vars = Ir.collect_vars vc.formula in
  let apps = Ir.collect_apps vc.formula in
  match Ir.collect_function_decls apps with
  | Error message -> Error message
  | Ok functions ->
      let overlaps =
        List.filter
          (fun name -> List.exists (fun (fn, _) -> String.equal fn name) functions)
          vars
      in
      if overlaps <> [] then
        Error
          (Printf.sprintf
             "identifiers used as both variables and functions: %s"
             (String.concat ", " overlaps))
      else
        Ok (Ir.declare_consts vars @ Ir.declare_funs functions)

let sat_query_commands vc declarations =
  declarations
  @ [ Ir.Assert (Ir.mk_not vc.formula); Ir.Check_sat ]

let model_query_commands vc declarations =
  sat_query_commands vc declarations
  @ List.map (fun query -> Ir.Get_value query.term) vc.queries

let query_model vc declarations =
  match run_z3 (Ir.Set_option (":produce-models", "true") :: model_query_commands vc declarations) with
  | Error message -> Error message
  | Ok output ->
      let sexps = parse_sexps output in
      (match sexps with
      | Atom "sat" :: responses ->
          if List.length responses <> List.length vc.queries then
            Error "z3 returned an unexpected number of queried values"
          else
            Ok
              (List.map2
                 (fun query response -> query.label, parse_value_response response)
                 vc.queries responses)
      | Atom "unknown" :: _ ->
          Error "z3 could not produce a model for an unknown result"
      | Atom "unsat" :: _ ->
          Error "z3 unexpectedly reported unsat while querying a model"
      | _ ->
          Error "unexpected z3 model response")

let check_vc vc =
  match declarations_for_vc vc with
  | Error message -> Error message
  | Ok declarations ->
      (match run_z3 (sat_query_commands vc declarations) with
      | Error message -> Error message
      | Ok output ->
          match sat_result_of_output output with
          | Unsat -> Ok None
          | Unknown ->
              Ok
                (Some
                   (Inconclusive
                      {
                        condition_name = vc.name;
                        reason = "z3 returned unknown";
                      }))
          | Sat ->
              (match query_model vc declarations with
              | Error message -> Error message
              | Ok bindings ->
                  Ok
                    (Some
                       (Counterexample
                          {
                            condition_name = vc.name;
                            condition = Ir.formula_to_pretty vc.formula;
                            bindings;
                          }))))

let verify_instrumented_program program =
  let rec loop = function
    | [] -> Ok Verified
    | vc :: rest ->
        (match check_vc vc with
        | Error _ as error -> error
        | Ok None -> loop rest
        | Ok (Some outcome) -> Ok outcome)
  in
  loop (vcs_for_program program)

let verify_program program =
  match Instrument.instrument_program program with
  | Error message -> Error message
  | Ok instrumented -> verify_instrumented_program instrumented

let format_outcome = function
  | Verified -> "Verified."
  | Inconclusive { condition_name; reason } ->
      "Verification inconclusive at " ^ condition_name ^ ":\n" ^ reason
  | Counterexample { condition_name; condition; bindings } ->
      let bindings =
        match bindings with
        | [] -> "  <no symbolic values>"
        | bindings ->
            String.concat "\n"
              (List.map
                 (fun (name, value) -> "  " ^ name ^ " = " ^ value)
                 bindings)
      in
      "Counterexample at " ^ condition_name ^ ":\n"
      ^ "Condition:\n  "
      ^ condition
      ^ "\nCounterexample:\n"
      ^ bindings
