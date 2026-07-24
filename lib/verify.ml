open Ast

module Ir = Z3_ir
module String_map = Map.Make (String)
module String_set = Set.Make (String)

type query = {
  label : string;
  term : Ir.int_expr;
}

type vc_kind =
  | Entry
  | Theorem of int
  | Loop_preservation of int
  | Loop_exit of int

type verification_condition = {
  name : string;
  function_name : string;
  kind : vc_kind;
  formula : Ir.formula;
  queries : query list;
}

type counterexample = {
  condition_name : string;
  location : string option;
  condition : string;
  bindings : (string * string) list;
  program_bindings : (string * string) list;
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

type expr_env = {
  var_types : (string * c_type) list;
  function_sigs : (string * (c_type list * c_type)) list;
}

type replay_state =
  | Replay_continue of (string * Ir.int_expr) list
  | Replay_return
  | Replay_blocked
  | Replay_violation of assert_origin * Ir.formula * (string * Ir.int_expr) list

let fail fmt = Printf.ksprintf failwith fmt

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

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

let lookup_assoc key bindings =
  List.find_map
    (fun (name, value) ->
      if String.equal name key then Some value else None)
    bindings

let strip_float_suffix text =
  if String.length text > 0
     && (text.[String.length text - 1] = 'f' || text.[String.length text - 1] = 'F')
  then
    String.sub text 0 (String.length text - 1)
  else
    text

let sort_of_c_type = function
  | TFloat | TDouble -> Ir.Real
  | TInt | TChar | TBool | TPointer _ -> Ir.Int
  | TRecord _ -> failwith "record values should be lowered before SMT translation"
  | TArray _ -> failwith "array values should be lowered before SMT translation"
  | TVoid -> failwith "void cannot appear in SMT expressions"
  | TReference _ | TConstReference _ ->
      failwith "reference values should be lowered before SMT translation"

let is_queryable_type = function
  | TInt | TFloat | TDouble | TChar | TBool | TPointer _ -> true
  | TVoid | TRecord _ | TArray _ | TReference _ | TConstReference _ -> false

let helper_signature = function
  | "__anvil_load_int" -> Some ([ Ir.Int; Ir.Int ], TInt)
  | "__anvil_load_float" -> Some ([ Ir.Int; Ir.Int ], TFloat)
  | "__anvil_load_double" -> Some ([ Ir.Int; Ir.Int ], TDouble)
  | "__anvil_load_char" -> Some ([ Ir.Int; Ir.Int ], TChar)
  | "__anvil_load_bool" -> Some ([ Ir.Int; Ir.Int ], TBool)
  | "__anvil_load_ptr_block" -> Some ([ Ir.Int; Ir.Int ], TInt)
  | "__anvil_load_ptr_offset" -> Some ([ Ir.Int; Ir.Int ], TInt)
  | _ -> None

let build_function_sigs (program : program) =
  let imported =
    List.concat_map
      (fun (header : header_import) -> header.functions)
      program.imports
    |> List.map (fun (fn : contracted_function) ->
           ( fn.name
           , ( List.map (fun param -> lower_reference_type param.param_type) fn.params
             , lower_reference_type fn.return_type ) ))
  in
  let locals =
    List.map
      (fun (fn : function_def) ->
        ( fn.name
        , ( List.map (fun param -> lower_reference_type param.param_type) fn.params
          , lower_reference_type fn.return_type ) ))
      (program.functions @ [ program.main ])
  in
  imported @ locals

let expr_env_for_function (program : program) (fn : function_def) =
  {
    var_types =
      (List.map (fun global -> global.global_name, global.global_type) program.globals)
      @ List.map (fun local -> local.global_name, local.global_type) fn.locals
      @ List.filter_map
          (fun param ->
            Option.map (fun name -> name, param.param_type) param.param_name)
          fn.params;
    function_sigs = build_function_sigs program;
  }

let extend_expr_env_with_quantified_bindings env bindings =
  {
    env with
    var_types =
      List.fold_left
        (fun var_types (binding : quantified_var) ->
          (binding.quant_name, binding.quant_type) :: var_types)
        env.var_types
        bindings;
  }

let lookup_var_type env name =
  lookup_assoc name env.var_types

let lookup_function_return_type env name =
  match helper_signature name with
  | Some (_, return_type) -> Some return_type
  | None ->
      Option.map snd (lookup_assoc name env.function_sigs)

let rec expr_type env = function
  | Int _ -> TInt
  | FloatLit _ -> TFloat
  | DoubleLit _ -> TDouble
  | CharLit _ -> TChar
  | BoolLit _ -> TBool
  | Var name ->
      Option.value (lookup_var_type env name) ~default:TInt
  | AddrOf _ | Index _ | Deref _ | Field _ ->
      failwith "memory expressions should be lowered before verification"
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right) ->
      if is_real_type (expr_type env left) || is_real_type (expr_type env right) then
        TDouble
      else
        TInt
  | Mod _ -> TInt
  | FuncCall (name, _args) ->
      (match lookup_function_return_type env name with
      | Some return_type -> return_type
      | None -> TInt)

let rec expr_to_ir env = function
  | Int n -> Ir.Int_lit n
  | FloatLit text -> Ir.Real_lit (strip_float_suffix text)
  | DoubleLit text -> Ir.Real_lit text
  | CharLit value -> Ir.Int_lit value
  | BoolLit true -> Ir.Int_lit 1
  | BoolLit false -> Ir.Int_lit 0
  | Var name -> Ir.Var name
  | AddrOf _ | Index _ | Deref _ | Field _ ->
      failwith "memory expressions should be lowered before verification"
  | Add (left, right) -> Ir.Add [expr_to_ir env left; expr_to_ir env right]
  | Sub (left, right) -> Ir.Sub (expr_to_ir env left, expr_to_ir env right)
  | Mul (left, right) -> Ir.Mul [expr_to_ir env left; expr_to_ir env right]
  | Div (left, right) -> Ir.Div (expr_to_ir env left, expr_to_ir env right)
  | Mod (left, right) -> Ir.Mod (expr_to_ir env left, expr_to_ir env right)
  | FuncCall (name, args) -> Ir.App (name, List.map (expr_to_ir env) args)

let rec bexpr_to_ir env = function
  | True -> Ir.True
  | False -> Ir.False
  | Forall (bindings, body) ->
      let env = extend_expr_env_with_quantified_bindings env bindings in
      Ir.mk_forall
        (List.map
           (fun (binding : quantified_var) ->
             binding.quant_name, sort_of_c_type binding.quant_type)
           bindings)
        (bexpr_to_ir env body)
  | Eq (left, right) -> Ir.Eq (expr_to_ir env left, expr_to_ir env right)
  | Neq (left, right) -> Ir.Neq (expr_to_ir env left, expr_to_ir env right)
  | Lt (left, right) -> Ir.Lt (expr_to_ir env left, expr_to_ir env right)
  | Le (left, right) -> Ir.Le (expr_to_ir env left, expr_to_ir env right)
  | Gt (left, right) -> Ir.Gt (expr_to_ir env left, expr_to_ir env right)
  | Ge (left, right) -> Ir.Ge (expr_to_ir env left, expr_to_ir env right)
  | Not inner -> Ir.mk_not (bexpr_to_ir env inner)
  | And (left, right) -> Ir.mk_and [bexpr_to_ir env left; bexpr_to_ir env right]
  | Or (left, right) -> Ir.mk_or [bexpr_to_ir env left; bexpr_to_ir env right]

let sort_queries queries =
  List.sort
    (fun left right -> String.compare left.label right.label)
    queries

let dedup_queries queries =
  let rec loop acc = function
    | [] -> List.rev acc
    | [query] -> List.rev (query :: acc)
    | query :: ((next : query) :: rest) ->
        if String.equal query.label next.label then
          loop acc (next :: rest)
        else
          loop (query :: acc) (next :: rest)
  in
  loop [] (sort_queries queries)

let make_vc name function_name kind formula =
  let var_queries =
    Ir.collect_vars formula
    |> List.map (fun name -> { label = name; term = Ir.Var name })
  in
  let app_queries =
    Ir.collect_queryable_apps formula
    |> List.map (fun (_, term) ->
           { label = Ir.int_expr_to_pretty term; term })
  in
  { name; function_name; kind; formula; queries = dedup_queries (var_queries @ app_queries) }

let add_vc state kind name formula =
  {
    state with
    vcs_rev = make_vc name state.function_name kind formula :: state.vcs_rev;
  }

let synthetic_param_name index =
  Printf.sprintf "__anvil_contract_arg_%d" index

let named_contract_params (contract_fn : contracted_function) =
  List.mapi
    (fun index (param : param) ->
      {
        param with
        param_name =
          Some
            (Option.value
               param.param_name
               ~default:(synthetic_param_name index));
      })
    contract_fn.params

let synthetic_function_for_contract (contract_fn : contracted_function) =
  {
    name = contract_fn.name;
    return_type = contract_fn.return_type;
    params = named_contract_params contract_fn;
    locals = [];
    contract = None;
    body = Skip;
  }

let summary_sort_supported c_type =
  match lower_reference_type c_type with
  | TInt | TFloat | TDouble | TChar | TBool | TPointer _ -> true
  | TVoid -> true
  | TRecord _ | TArray _ | TReference _ | TConstReference _ -> false

let contract_summary_supported (contract_fn : contracted_function) =
  summary_sort_supported contract_fn.return_type
  && List.for_all
       (fun (param : param) -> summary_sort_supported param.param_type)
       contract_fn.params

let quantified_bindings_of_params params =
  List.filter_map
    (fun (param : param) ->
      Option.map
        (fun name ->
          {
            quant_type = lower_reference_type param.param_type;
            quant_name = name;
          })
        param.param_name)
    params

let wrap_formula_with_bindings bindings formula =
  match bindings with
  | [] -> formula
  | _ ->
      Ir.mk_forall
        (List.map
           (fun (binding : quantified_var) ->
             binding.quant_name, sort_of_c_type binding.quant_type)
           bindings)
        formula

let instantiate_summary_clauses
    (program : program)
    malloc_sites
    (contract_fn : contracted_function) =
  if not (contract_summary_supported contract_fn) then
    Ok []
  else
    let synthetic_fn = synthetic_function_for_contract contract_fn in
    let memory_env =
      Memory_safety.function_env_of_program program synthetic_fn malloc_sites
    in
    let* current =
      Instrument.build_current_contract memory_env contract_fn synthetic_fn.params
    in
    let expr_env = expr_env_for_function program synthetic_fn in
    let quantified_bindings =
      quantified_bindings_of_params synthetic_fn.params
    in
    let* clauses =
      match contract_fn.return_type with
      | TVoid ->
          let* guarantee = Instrument.instantiate_void_guarantee current in
          let* safety = Instrument.instantiate_void_safety current in
          Ok (guarantee @ safety)
      | _ ->
          let args =
            List.map
              (fun (param : param) ->
                match param.param_name with
                | Some name -> Var name
                | None -> fail "missing synthetic parameter name")
              synthetic_fn.params
          in
          let result = FuncCall (contract_fn.name, args) in
          let scalar_bindings =
            Instrument.scalar_bindings_with_result current result
          in
          let* guarantee =
            Instrument.instantiate_contracts
              memory_env
              contract_fn
              "@Guarantee"
              contract_fn.contract.guarantee
              scalar_bindings
              current.ghost_env.bool_bindings
              current.ghost_env
          in
          let* safety =
            Instrument.instantiate_contracts
              memory_env
              contract_fn
              "@Safety"
              contract_fn.contract.safety
              scalar_bindings
              current.ghost_env.bool_bindings
              current.ghost_env
          in
          Ok (guarantee @ safety)
    in
    Ok
      (List.map
         (fun clause ->
           contract_fn.name,
           wrap_formula_with_bindings quantified_bindings (bexpr_to_ir expr_env clause))
         clauses)

let theorem_vcs_for_function
    (program : program)
    malloc_sites
    (fn : function_def)
    (contract_fn : contracted_function) =
  if contract_fn.contract.theorem = [] then
    Ok []
  else if not (contract_summary_supported contract_fn) then
    Error
      (Printf.sprintf
         "theorem clauses for `%s` require scalar, pointer, or reference-lowered signatures"
         contract_fn.name)
  else
    let synthetic_fn = synthetic_function_for_contract contract_fn in
    let memory_env =
      Memory_safety.function_env_of_program program synthetic_fn malloc_sites
    in
    let* current =
      Instrument.build_current_contract memory_env contract_fn synthetic_fn.params
    in
    let* clauses =
      Instrument.instantiate_contracts
        memory_env
        contract_fn
        "@Theorem"
        contract_fn.contract.theorem
        (Instrument.entry_scalar_bindings current)
        current.ghost_env.bool_bindings
        current.ghost_env
    in
    if List.exists (Instrument.bexpr_has_var "result") clauses then
      Error
        (Printf.sprintf
           "@Theorem for `%s` references `result`; use @Guarantee for per-call postconditions"
           contract_fn.name)
    else
      let expr_env = expr_env_for_function program synthetic_fn in
      Ok
        (List.mapi
           (fun index clause ->
             make_vc
               (Printf.sprintf "%s: theorem %d" fn.name (index + 1))
               fn.name
               (Theorem (index + 1))
               (bexpr_to_ir expr_env clause))
           clauses)

let theorem_assumptions_for_contract
    (program : program)
    malloc_sites
    (contract_fn : contracted_function) =
  if contract_fn.contract.theorem = [] then
    Ok []
  else if not (contract_summary_supported contract_fn) then
    Error
      (Printf.sprintf
         "theorem clauses for `%s` require scalar, pointer, or reference-lowered signatures"
         contract_fn.name)
  else
    let synthetic_fn = synthetic_function_for_contract contract_fn in
    let memory_env =
      Memory_safety.function_env_of_program program synthetic_fn malloc_sites
    in
    let* current =
      Instrument.build_current_contract memory_env contract_fn synthetic_fn.params
    in
    let* clauses =
      Instrument.instantiate_contracts
        memory_env
        contract_fn
        "@Theorem"
        contract_fn.contract.theorem
        (Instrument.entry_scalar_bindings current)
        current.ghost_env.bool_bindings
        current.ghost_env
    in
    if List.exists (Instrument.bexpr_has_var "result") clauses then
      Error
        (Printf.sprintf
           "@Theorem for `%s` references `result`; use @Guarantee for per-call postconditions"
           contract_fn.name)
    else
      let expr_env = expr_env_for_function program synthetic_fn in
      Ok
        (List.map
           (fun clause ->
             contract_fn.name, bexpr_to_ir expr_env clause)
           clauses)

let defined_function_names (program : program) =
  List.map (fun (fn : function_def) -> fn.name) (program.functions @ [ program.main ])

let contract_summary_for_program (program : program) =
  let* contract_env =
    Instrument.build_contract_env program.imports (program.functions @ [ program.main ])
  in
  let malloc_sites = (Memory_safety.contract_env_of_program program).malloc_sites in
  let defined_names = defined_function_names program in
  let rec summary_loop acc = function
    | [] -> Ok (List.rev acc)
    | (_name, contract_fn) :: rest ->
        let* formulas =
          instantiate_summary_clauses program malloc_sites contract_fn
        in
        summary_loop (List.rev_append formulas acc) rest
  in
  let rec imported_theorem_loop acc = function
    | [] -> Ok (List.rev acc)
    | (header : header_import) :: rest ->
        let imported_functions =
          List.filter
            (fun (fn : imported_function) ->
              not (List.exists (String.equal fn.name) defined_names))
            header.functions
        in
        let rec loop_functions acc = function
          | [] ->
              imported_theorem_loop acc rest
          | contract_fn :: tail ->
              let* formulas =
                theorem_assumptions_for_contract program malloc_sites contract_fn
              in
              loop_functions (List.rev_append formulas acc) tail
        in
        loop_functions acc imported_functions
  in
  let rec theorem_loop acc = function
    | [] -> Ok (List.rev acc)
    | fn :: rest ->
        (match Instrument.effective_contract contract_env fn with
        | Error _ as error -> error
        | Ok None ->
            theorem_loop acc rest
        | Ok (Some contract_fn) ->
            let* vcs =
              theorem_vcs_for_function program malloc_sites fn contract_fn
            in
            theorem_loop (List.rev_append vcs acc) rest)
  in
  let* assumptions = summary_loop [] contract_env in
  let* imported_theorem_assumptions = imported_theorem_loop [] program.imports in
  let* theorem_vcs = theorem_loop [] (program.functions @ [ program.main ]) in
  Ok (assumptions @ imported_theorem_assumptions, theorem_vcs)

let rec wp_stmt env state stmt post =
  match stmt with
  | Skip -> post, state
  | Break | Continue ->
      (* Evolve-block only; modelling them as `Skip` here would be unsound. *)
      failwith "`break`/`continue` reached weakest-precondition generation"
  | Block _ | LocalDecl _ ->
      failwith "unresolved local syntax reached weakest-precondition generation"
  | Assign (name, expr) ->
      Ir.subst_formula name (expr_to_ir env expr) post, state
  | Store _ | ArrayAssign _ | FieldAssign _ | Free _ ->
      failwith "memory statements should be lowered before verification"
  | Seq stmts ->
      List.fold_right
        (fun stmt (post, state) -> wp_stmt env state stmt post)
        stmts
        (post, state)
  | If (cond, then_branch, else_branch) ->
      let then_pre, state = wp_stmt env state then_branch post in
      let else_pre, state = wp_stmt env state else_branch post in
      ( Ir.mk_and
          [ Ir.mk_implies (bexpr_to_ir env cond) then_pre
          ; Ir.mk_implies (Ir.mk_not (bexpr_to_ir env cond)) else_pre
          ]
      , state )
  | While (invariant_opt, cond, body) ->
      let loop_id = state.next_loop in
      let state = { state with next_loop = loop_id + 1 } in
      let invariant =
        match invariant_opt with
        | None -> post
        | Some invariant -> bexpr_to_ir env invariant
      in
      let body_pre, state = wp_stmt env state body invariant in
      let preservation =
        Ir.mk_implies
          (Ir.mk_and [invariant; bexpr_to_ir env cond])
          body_pre
      in
      let preservation_name =
        Printf.sprintf "%s: loop %d preservation" state.function_name loop_id
      in
      let state = add_vc state (Loop_preservation loop_id) preservation_name preservation in
      let exit_condition =
        Ir.mk_implies
          (Ir.mk_and [invariant; Ir.mk_not (bexpr_to_ir env cond)])
          post
      in
      let exit_name =
        Printf.sprintf "%s: loop %d exit" state.function_name loop_id
      in
      invariant, add_vc state (Loop_exit loop_id) exit_name exit_condition
  | Assume cond ->
      Ir.mk_implies (bexpr_to_ir env cond) post, state
  | Assert (_, cond) ->
      Ir.mk_and [bexpr_to_ir env cond; post], state
  | Return _ -> Ir.True, state

let vcs_for_function (program : program) (fn : function_def) =
  let env = expr_env_for_function program fn in
  let state = { function_name = fn.name; next_loop = 0; vcs_rev = [] } in
  let precondition, state = wp_stmt env state fn.body Ir.True in
  List.rev
    (make_vc (fn.name ^ ": entry") fn.name Entry precondition :: state.vcs_rev)

let vcs_for_program (program : program) =
  List.concat_map (vcs_for_function program) (program.functions @ [program.main])

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

let rec vars_in_ir_expr acc = function
  | Ir.Int_lit _ | Ir.Real_lit _ -> acc
  | Ir.Var name -> String_set.add name acc
  | Ir.Add exprs
  | Ir.Mul exprs ->
      List.fold_left vars_in_ir_expr acc exprs
  | Ir.Sub (left, right)
  | Ir.Div (left, right)
  | Ir.Mod (left, right) ->
      vars_in_ir_expr (vars_in_ir_expr acc left) right
  | Ir.App (_, args) ->
      List.fold_left vars_in_ir_expr acc args

let rec apps_in_ir_expr acc = function
  | Ir.Int_lit _ | Ir.Real_lit _ | Ir.Var _ -> acc
  | Ir.Add exprs
  | Ir.Mul exprs ->
      List.fold_left apps_in_ir_expr acc exprs
  | Ir.Sub (left, right)
  | Ir.Div (left, right)
  | Ir.Mod (left, right) ->
      apps_in_ir_expr (apps_in_ir_expr acc left) right
  | Ir.App (name, args) as expr ->
      let acc =
        List.fold_left apps_in_ir_expr acc args
      in
      String_map.add (Ir.int_expr_to_pretty expr) (name, expr) acc

let find_function_in_program (program : program) name =
  if String.equal program.main.name name then Some program.main
  else List.find_opt (fun (fn : function_def) -> String.equal fn.name name) program.functions

let lookup_param_type (fn : function_def) name =
  List.find_map
    (fun param ->
      match param.param_name with
      | Some param_name when String.equal param_name name -> Some param.param_type
      | Some _ | None -> None)
    fn.params

let lookup_vc_var_type (program : program) function_name name =
  match lookup_global_type program.globals name with
  | Some c_type -> Some c_type
  | None ->
      (match find_function_in_program program function_name with
      | Some fn -> lookup_param_type fn name
      | None -> None)

let signature_sorts_of_name (program : program) name arity =
  match helper_signature name with
  | Some (arg_sorts, return_type) ->
      if List.length arg_sorts = arity then
        Ok (arg_sorts, sort_of_c_type return_type)
      else
        Error
          (Printf.sprintf
             "helper `%s` expected arity %d but saw %d"
             name
             (List.length arg_sorts)
             arity)
  | None ->
      (match lookup_assoc name (build_function_sigs program) with
      | Some (param_types, return_type) ->
          if List.length param_types = arity then
            Ok (List.map sort_of_c_type param_types, sort_of_c_type return_type)
          else
            Error
              (Printf.sprintf
                 "function `%s` expected arity %d but saw %d"
                 name
                 (List.length param_types)
                 arity)
      | None ->
          Ok (List.init arity (fun _ -> Ir.Int), Ir.Int))

let declarations_for_vc program assumptions vc extra_queries =
  let ( let* ) result f =
    match result with
    | Ok value -> f value
    | Error _ as error -> error
  in
  let vars =
    List.fold_left
      (fun acc query -> vars_in_ir_expr acc query.term)
      (List.fold_left
         (fun acc assumption ->
           Ir.collect_vars assumption
           |> List.fold_left (fun acc name -> String_set.add name acc) acc)
         (Ir.collect_vars vc.formula
          |> List.fold_left (fun acc name -> String_set.add name acc) String_set.empty)
         assumptions)
      extra_queries
    |> String_set.elements
  in
  let apps =
    List.fold_left
      (fun acc query -> apps_in_ir_expr acc query.term)
      (List.fold_left
         (fun acc assumption ->
           Ir.collect_apps assumption
           |> List.fold_left
                (fun acc (name, expr) ->
                  String_map.add (Ir.int_expr_to_pretty expr) (name, expr) acc)
                acc)
         (Ir.collect_apps vc.formula
          |> List.fold_left
               (fun acc (name, expr) ->
                 String_map.add (Ir.int_expr_to_pretty expr) (name, expr) acc)
               String_map.empty)
         assumptions)
      extra_queries
    |> String_map.bindings
    |> List.map snd
  in
  let rec collect_typed_functions decls = function
    | [] -> Ok (String_map.bindings decls)
    | (name, Ir.App (_, args)) :: rest ->
        let* arg_sorts, ret_sort =
          signature_sorts_of_name program name (List.length args)
        in
        (match String_map.find_opt name decls with
        | None ->
            collect_typed_functions
              (String_map.add name (arg_sorts, ret_sort) decls)
              rest
        | Some (existing_args, existing_ret)
          when existing_args = arg_sorts && existing_ret = ret_sort ->
            collect_typed_functions decls rest
        | Some _ ->
            Error
              (Printf.sprintf
                 "function `%s` used with inconsistent signatures in Z3 translation"
                 name))
    | _ :: rest -> collect_typed_functions decls rest
  in
  let* functions = collect_typed_functions String_map.empty apps in
      let overlaps =
        List.filter
          (fun name ->
            List.exists (fun (fn, _) -> String.equal fn name) functions)
          vars
      in
      if overlaps <> [] then
        Error
          (Printf.sprintf
             "identifiers used as both variables and functions: %s"
             (String.concat ", " overlaps))
      else
        let consts =
          List.map
            (fun name ->
              let sort =
                match lookup_vc_var_type program vc.function_name name with
                | Some c_type -> sort_of_c_type c_type
                | None -> Ir.Int
              in
              Ir.Declare_const (name, sort))
            vars
        in
        let funs =
          List.map
            (fun (name, (arg_sorts, ret_sort)) ->
              Ir.Declare_fun (name, arg_sorts, ret_sort))
            functions
        in
        Ok (consts @ funs)

let sat_query_commands assumptions vc declarations =
  declarations
  @ List.map (fun formula -> Ir.Assert formula) assumptions
  @ [ Ir.Assert (Ir.mk_not vc.formula); Ir.Check_sat ]

let model_query_commands assumptions vc declarations queries =
  sat_query_commands assumptions vc declarations
  @ List.map (fun query -> Ir.Get_value query.term) queries

let query_model assumptions vc declarations queries =
  match
    run_z3
      (Ir.Set_option (":produce-models", "true")
      :: model_query_commands assumptions vc declarations queries)
  with
  | Error message -> Error message
  | Ok output ->
      let sexps = parse_sexps output in
      (match sexps with
      | Atom "sat" :: responses ->
          if List.length responses <> List.length queries then
            Error "z3 returned an unexpected number of queried values"
          else
            Ok
              (List.map2
                 (fun query response -> query.label, parse_value_response response)
                 queries responses)
      | Atom "unknown" :: _ ->
          Error "z3 could not produce a model for an unknown result"
      | Atom "unsat" :: _ ->
          Error "z3 unexpectedly reported unsat while querying a model"
      | _ ->
          Error "unexpected z3 model response")

let rec assoc_opt key bindings =
  match bindings with
  | [] -> None
  | (name, value) :: rest ->
      if String.equal key name then Some value else assoc_opt key rest

let find_function (program : program) name =
  find_function_in_program program name

let param_names params =
  List.filter_map (fun param -> param.param_name) params

let rec apps_in_expr env acc = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ -> acc
  | AddrOf inner -> apps_in_expr env acc inner
  | Index (base, index) ->
      apps_in_expr env (apps_in_expr env acc base) index
  | Deref inner ->
      apps_in_expr env acc inner
  | Field (base, _) ->
      apps_in_expr env acc base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      apps_in_expr env (apps_in_expr env acc left) right
  | FuncCall (name, args) as expr ->
      let acc =
        List.fold_left (apps_in_expr env) acc args
      in
      let ir_expr = expr_to_ir env expr in
      String_map.add (Ir.int_expr_to_pretty ir_expr) (name, ir_expr) acc

let rec apps_in_bexpr env acc = function
  | True | False -> acc
  | Forall (bindings, body) ->
      apps_in_bexpr (extend_expr_env_with_quantified_bindings env bindings) acc body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      apps_in_expr env (apps_in_expr env acc left) right
  | Not inner -> apps_in_bexpr env acc inner
  | And (left, right)
  | Or (left, right) ->
      apps_in_bexpr env (apps_in_bexpr env acc left) right

let rec apps_in_stmt env acc = function
  | Skip | Break | Continue -> acc
  | Block stmts ->
      List.fold_left (apps_in_stmt env) acc stmts
  | LocalDecl (_, init) ->
      (match init with
      | None -> acc
      | Some expr -> apps_in_expr env acc expr)
  | Assign (_, expr) -> apps_in_expr env acc expr
  | Store (ptr, value) -> apps_in_expr env (apps_in_expr env acc ptr) value
  | ArrayAssign (base, index, value) ->
      apps_in_expr env (apps_in_expr env (apps_in_expr env acc base) index) value
  | FieldAssign (base, _, value) ->
      apps_in_expr env (apps_in_expr env acc base) value
  | Seq stmts ->
      List.fold_left (apps_in_stmt env) acc stmts
  | If (cond, then_branch, else_branch) ->
      apps_in_stmt env
        (apps_in_stmt env (apps_in_bexpr env acc cond) then_branch)
        else_branch
  | While (invariant, cond, body) ->
      let acc =
        match invariant with
        | None -> acc
        | Some invariant -> apps_in_bexpr env acc invariant
      in
      apps_in_stmt env (apps_in_bexpr env acc cond) body
  | Assume cond -> apps_in_bexpr env acc cond
  | Assert (_, cond) -> apps_in_bexpr env acc cond
  | Free ptr -> apps_in_expr env acc ptr
  | Return None -> acc
  | Return (Some value) -> apps_in_expr env acc value

let queries_for_vc (program : program) (vc : verification_condition) =
  match find_function program vc.function_name with
  | None -> vc.queries
  | Some fn ->
      let env = expr_env_for_function program fn in
      let queryable_globals =
        List.filter_map
          (fun global ->
            if is_queryable_type global.global_type then Some global.global_name
            else None)
          program.globals
      in
      let queryable_locals =
        List.filter_map
          (fun local ->
            if is_queryable_type local.global_type then Some local.global_name
            else None)
          fn.locals
      in
      let extra_var_queries =
        List.map
          (fun name -> { label = name; term = Ir.Var name })
          ( queryable_globals
          @ queryable_locals
          @ List.filter_map
              (fun param ->
                match param.param_name with
                | Some name when is_queryable_type param.param_type -> Some name
                | Some _ | None -> None)
              fn.params )
      in
      let extra_app_queries =
        apps_in_stmt env String_map.empty fn.body
        |> String_map.bindings
        |> List.map (fun (_, (_, term)) ->
               { label = Ir.int_expr_to_pretty term; term })
      in
      dedup_queries (vc.queries @ extra_var_queries @ extra_app_queries)

let model_map_of_bindings bindings =
  List.fold_left
    (fun acc (name, value) -> String_map.add name value acc)
    String_map.empty
    bindings

let int_of_model_value value =
  try Some (int_of_string value) with
  | Failure _ -> None

let rec lookup_env env name =
  match env with
  | [] -> None
  | (current, value) :: rest ->
      if String.equal current name then Some value else lookup_env rest name

let rec symbolic_expr env = function
  | Int n -> Ir.Int_lit n
  | FloatLit text -> Ir.Real_lit (strip_float_suffix text)
  | DoubleLit text -> Ir.Real_lit text
  | CharLit value -> Ir.Int_lit value
  | BoolLit true -> Ir.Int_lit 1
  | BoolLit false -> Ir.Int_lit 0
  | Var name ->
      (match lookup_env env name with
      | Some value -> value
      | None -> Ir.Var name)
  | AddrOf _ | Index _ | Deref _ | Field _ ->
      failwith "memory expressions should be lowered before replay"
  | Add (left, right) ->
      Ir.Add [ symbolic_expr env left; symbolic_expr env right ]
  | Sub (left, right) ->
      Ir.Sub (symbolic_expr env left, symbolic_expr env right)
  | Mul (left, right) ->
      Ir.Mul [ symbolic_expr env left; symbolic_expr env right ]
  | Div (left, right) ->
      Ir.Div (symbolic_expr env left, symbolic_expr env right)
  | Mod (left, right) ->
      Ir.Mod (symbolic_expr env left, symbolic_expr env right)
  | FuncCall (name, args) ->
      Ir.App (name, List.map (symbolic_expr env) args)

let rec symbolic_bexpr env = function
  | True -> Ir.True
  | False -> Ir.False
  | Forall (bindings, body) ->
      let env =
        List.filter
          (fun (name, _value) ->
            not
              (List.exists
                 (fun (binding : quantified_var) -> String.equal name binding.quant_name)
                 bindings))
          env
      in
      Ir.mk_forall
        (List.map
           (fun (binding : quantified_var) ->
             binding.quant_name, sort_of_c_type binding.quant_type)
           bindings)
        (symbolic_bexpr env body)
  | Eq (left, right) ->
      Ir.Eq (symbolic_expr env left, symbolic_expr env right)
  | Neq (left, right) ->
      Ir.Neq (symbolic_expr env left, symbolic_expr env right)
  | Lt (left, right) ->
      Ir.Lt (symbolic_expr env left, symbolic_expr env right)
  | Le (left, right) ->
      Ir.Le (symbolic_expr env left, symbolic_expr env right)
  | Gt (left, right) ->
      Ir.Gt (symbolic_expr env left, symbolic_expr env right)
  | Ge (left, right) ->
      Ir.Ge (symbolic_expr env left, symbolic_expr env right)
  | Not inner -> Ir.mk_not (symbolic_bexpr env inner)
  | And (left, right) ->
      Ir.mk_and [ symbolic_bexpr env left; symbolic_bexpr env right ]
  | Or (left, right) ->
      Ir.mk_or [ symbolic_bexpr env left; symbolic_bexpr env right ]

let rec eval_int_expr model = function
  | Ir.Int_lit n -> Some n
  | Ir.Real_lit _ -> None
  | Ir.Var name ->
      (match String_map.find_opt name model with
      | None -> None
      | Some value -> int_of_model_value value)
  | Ir.Add exprs ->
      let rec loop acc = function
        | [] -> Some acc
        | expr :: rest ->
            (match eval_int_expr model expr with
            | None -> None
            | Some value -> loop (acc + value) rest)
      in
      loop 0 exprs
  | Ir.Sub (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left - right)
      | _ -> None)
  | Ir.Mul exprs ->
      let rec loop acc = function
        | [] -> Some acc
        | expr :: rest ->
            (match eval_int_expr model expr with
            | None -> None
            | Some value -> loop (acc * value) rest)
      in
      loop 1 exprs
  | Ir.Div (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some _left, Some 0 -> None
      | Some left, Some right -> Some (left / right)
      | _ -> None)
  | Ir.Mod (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some _left, Some 0 -> None
      | Some left, Some right -> Some (left mod right)
      | _ -> None)
  | Ir.App _ as expr ->
      let label = Ir.int_expr_to_pretty expr in
      (match String_map.find_opt label model with
      | None -> None
      | Some value -> int_of_model_value value)

let rec eval_formula model = function
  | Ir.True -> Some true
  | Ir.False -> Some false
  | Ir.Not inner ->
      (match eval_formula model inner with
      | Some value -> Some (not value)
      | None -> None)
  | Ir.And formulas ->
      let rec loop = function
        | [] -> Some true
        | formula :: rest ->
            (match eval_formula model formula with
            | Some true -> loop rest
            | Some false -> Some false
            | None -> None)
      in
      loop formulas
  | Ir.Or formulas ->
      let rec loop = function
        | [] -> Some false
        | formula :: rest ->
            (match eval_formula model formula with
            | Some true -> Some true
            | Some false -> loop rest
            | None -> None)
      in
      loop formulas
  | Ir.Implies (left, right) ->
      (match eval_formula model left, eval_formula model right with
      | Some left, Some right -> Some ((not left) || right)
      | _ -> None)
  | Ir.Forall _ ->
      None
  | Ir.Eq (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left = right)
      | _ -> None)
  | Ir.Neq (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left <> right)
      | _ -> None)
  | Ir.Lt (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left < right)
      | _ -> None)
  | Ir.Le (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left <= right)
      | _ -> None)
  | Ir.Gt (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left > right)
      | _ -> None)
  | Ir.Ge (left, right) ->
      (match eval_int_expr model left, eval_int_expr model right with
      | Some left, Some right -> Some (left >= right)
      | _ -> None)

let bind_env env name value =
  (name, value) :: List.remove_assoc name env

let rec replay_stmt model env fuel stmt =
  if fuel <= 0 then
    Replay_blocked
  else
    match stmt with
    | Skip -> Replay_continue env
    | Block _ | LocalDecl _ | Break | Continue ->
        Replay_blocked
    | Assign (name, expr) ->
        Replay_continue (bind_env env name (symbolic_expr env expr))
    | Store _ | ArrayAssign _ | FieldAssign _ | Free _ ->
        Replay_blocked
    | Seq stmts ->
        replay_stmt_list model env fuel stmts
    | If (cond, then_branch, else_branch) ->
        (match eval_formula model (symbolic_bexpr env cond) with
        | Some true -> replay_stmt model env (fuel - 1) then_branch
        | Some false -> replay_stmt model env (fuel - 1) else_branch
        | None -> Replay_blocked)
    | While (_, cond, body) ->
        (match eval_formula model (symbolic_bexpr env cond) with
        | Some false -> Replay_continue env
        | Some true ->
            (match replay_stmt model env (fuel - 1) body with
            | Replay_continue env -> replay_stmt model env (fuel - 1) stmt
            | other -> other)
        | None -> Replay_blocked)
    | Assume cond ->
        (match eval_formula model (symbolic_bexpr env cond) with
        | Some true -> Replay_continue env
        | Some false | None -> Replay_blocked)
    | Assert (origin, cond) ->
        let condition = symbolic_bexpr env cond in
        (match eval_formula model condition with
        | Some true -> Replay_continue env
        | Some false -> Replay_violation (origin, condition, env)
        | None -> Replay_blocked)
    | Return _ -> Replay_return

and replay_stmt_list model env fuel = function
  | [] -> Replay_continue env
  | stmt :: rest ->
      (match replay_stmt model env fuel stmt with
      | Replay_continue env -> replay_stmt_list model env fuel rest
      | other -> other)

let describe_assert_origin = function
  | Source_assert -> "a source assertion was violated"
  | Call_require callee ->
      Printf.sprintf "`%s`'s @Require was violated" callee
  | Function_guarantee function_name ->
      Printf.sprintf "`%s` could not prove its @Guarantee" function_name
  | Function_safety function_name ->
      Printf.sprintf "`%s` could not prove its @Safety" function_name

let describe_vc (vc : verification_condition) =
  match vc.kind with
  | Entry -> None
  | Theorem theorem_id ->
      Some
        (Printf.sprintf
           "`%s` could not prove @Theorem %d"
           vc.function_name
           theorem_id)
  | Loop_preservation loop_id ->
      Some
        (Printf.sprintf
           "`%s` could not prove loop invariant preservation for loop %d"
           vc.function_name
           loop_id)
  | Loop_exit loop_id ->
      Some
        (Printf.sprintf
           "`%s` could not prove the loop exit obligation for loop %d"
           vc.function_name
           loop_id)

let locate_violation (program : program) (vc : verification_condition) model =
  match vc.kind, find_function program vc.function_name with
  | Entry, Some fn ->
      (match replay_stmt model [] 256 fn.body with
      | Replay_violation (origin, condition, env) ->
          Some (describe_assert_origin origin, Ir.formula_to_pretty condition, env)
      | _ -> None)
  | Entry, None
  | Theorem _, _
  | Loop_preservation _, _
  | Loop_exit _, _ ->
      None

let current_var_expr env name =
  match lookup_env env name with
  | Some value -> value
  | None -> Ir.Var name

let string_of_runtime_int env model name =
  match eval_int_expr model (current_var_expr env name) with
  | Some value -> string_of_int value
  | None ->
      (match String_map.find_opt name model with
      | Some value -> value
      | None -> "<unknown>")

let string_of_runtime_scalar env model c_type name =
  if is_real_type c_type then
    match String_map.find_opt name model with
    | Some value -> value
    | None -> "<unknown>"
  else if is_array_type c_type then
    Printf.sprintf "&%s[0]" name
  else if is_record_type c_type then
    "&" ^ name
  else
    string_of_runtime_int env model name

let pointer_value_string original_program env model name =
  let block_name = Memory_safety.ptr_block_name name in
  let offset_name = Memory_safety.ptr_offset_name name in
  let block = eval_int_expr model (current_var_expr env block_name) in
  let offset = eval_int_expr model (current_var_expr env offset_name) in
  match block, offset with
  | Some 0, Some 0 -> "0"
  | Some block, Some offset ->
      let scalar_globals = scalar_globals original_program.globals in
      if block >= 1 && block <= List.length scalar_globals then
        let global = List.nth scalar_globals (block - 1) in
        let global_name = global.global_name in
        (match global.global_type with
        | TArray (element_type, _) ->
            let element_size = Memory_safety.scalar_byte_size element_type in
            if offset = 0 then
              Printf.sprintf "&%s[0]" global_name
            else if offset mod element_size = 0 then
              Printf.sprintf "&%s[%d]" global_name (offset / element_size)
            else
              Printf.sprintf "&%s[0] + %d" global_name offset
        | _ ->
            if offset = 0 then
              "&" ^ global_name
            else
              Printf.sprintf "&%s + %d" global_name offset)
      else
        let site = block - List.length scalar_globals in
        let malloc_sites =
          (Memory_safety.contract_env_of_program original_program).malloc_sites
        in
        if site >= 1 && site <= malloc_sites then
          if offset = 0 then
            Printf.sprintf "malloc_site_%d" site
          else
            Printf.sprintf "malloc_site_%d + %d" site offset
        else
          Printf.sprintf "ptr(block=%d, offset=%d)" block offset
  | _ -> "<unknown>"

let program_bindings_for_counterexample
    (original_program : program)
    (vc : verification_condition)
    env
    model =
  match find_function original_program vc.function_name with
  | None -> []
  | Some fn ->
      let params =
        List.filter_map
          (fun param ->
            Option.map
              (fun name ->
                name,
                string_of_runtime_scalar env model param.param_type name)
              param.param_name)
          fn.params
      in
      let scalar_locals =
        List.map
          (fun local ->
            ( local.global_name
            , string_of_runtime_scalar env model local.global_type local.global_name ))
          (List.filter (fun local -> not (is_pointer_type local.global_type)) fn.locals)
      in
      let pointer_locals =
        List.map
          (fun local ->
            local.global_name,
            pointer_value_string original_program env model local.global_name)
          (List.filter (fun local -> is_pointer_type local.global_type) fn.locals)
      in
      let scalar_globals =
        List.map
          (fun global ->
            ( global.global_name
            , string_of_runtime_scalar env model global.global_type global.global_name ))
          (scalar_globals original_program.globals)
      in
      let pointer_globals =
        List.map
          (fun global ->
            global.global_name,
            pointer_value_string original_program env model global.global_name)
          (pointer_globals original_program.globals)
      in
      params @ scalar_locals @ pointer_locals @ scalar_globals @ pointer_globals
      (*
       Keep pointer snapshots separate because the source-level pointer value is reconstructed
       from its shadow block/offset variables rather than read directly from the model.
      *)

let check_vc
    (original_program : program)
    (instrumented_program : program)
    assumptions
    (vc : verification_condition) =
  let assumptions =
    match vc.kind with
    | Theorem _ ->
        List.map snd assumptions
    | Entry | Loop_preservation _ | Loop_exit _ ->
        List.filter_map
          (fun (owner, formula) ->
            if String.equal owner vc.function_name then None else Some formula)
          assumptions
  in
  let queries = queries_for_vc instrumented_program vc in
  match declarations_for_vc instrumented_program assumptions vc queries with
  | Error message -> Error message
  | Ok declarations ->
      (match run_z3 (sat_query_commands assumptions vc declarations) with
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
              (match query_model assumptions vc declarations queries with
              | Error message -> Error message
              | Ok bindings ->
                  let model = model_map_of_bindings bindings in
                  let location, condition, replay_env =
                    match locate_violation instrumented_program vc model with
                    | Some (location, condition, env) -> Some location, condition, env
                    | None ->
                        describe_vc vc,
                        Ir.formula_to_pretty vc.formula,
                        []
                  in
                  let symbolic_bindings =
                    List.filter
                      (fun (name, _) ->
                        List.exists (fun query -> String.equal query.label name) vc.queries)
                      bindings
                  in
                  Ok
                    (Some
                       (Counterexample
                          {
                            condition_name = vc.name;
                            location;
                            condition;
                            bindings = symbolic_bindings;
                            program_bindings =
                              program_bindings_for_counterexample
                                original_program vc replay_env model;
                          }))))

let verify_instrumented_program original_program program =
  let* assumptions, theorem_vcs =
    contract_summary_for_program original_program
  in
  let rec loop = function
    | [] -> Ok Verified
    | vc :: rest ->
        (match check_vc original_program program assumptions vc with
        | Error _ as error -> error
        | Ok None -> loop rest
        | Ok (Some outcome) -> Ok outcome)
  in
  loop (vcs_for_program program @ theorem_vcs)

let verify_program program =
  match Instrument.instrument_program program with
  | Error message -> Error message
  | Ok instrumented -> verify_instrumented_program program instrumented

let format_outcome = function
  | Verified -> "Verified."
  | Inconclusive { condition_name; reason } ->
      "Verification inconclusive at " ^ condition_name ^ ":\n" ^ reason
  | Counterexample { condition_name; location; condition; bindings; program_bindings } ->
      let bindings =
        match bindings with
        | [] -> "  <no symbolic values>"
        | bindings ->
            String.concat "\n"
              (List.map
                 (fun (name, value) -> "  " ^ name ^ " = " ^ value)
                 bindings)
      in
      let program_bindings =
        match program_bindings with
        | [] -> "  <no program variables>"
        | bindings ->
            String.concat "\n"
              (List.map
                 (fun (name, value) -> "  " ^ name ^ " = " ^ value)
                 bindings)
      in
      let location =
        match location with
        | None -> ""
        | Some location -> "Violation:\n  " ^ location ^ "\n"
      in
      "Counterexample at " ^ condition_name ^ ":\n"
      ^ location
      ^ "Condition:\n  "
      ^ condition
      ^ "\nModel:\n"
      ^ bindings
      ^ "\nProgram Variables:\n"
      ^ program_bindings
