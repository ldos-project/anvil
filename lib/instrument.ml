open Ast

exception Instrumentation_error of string

let fail fmt = Printf.ksprintf (fun msg -> raise (Instrumentation_error msg)) fmt

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

let parse_contract_expr context source =
  let lexbuf = Lexing.from_string source in
  try Ok (Parser.contract_expr_eof Lexer.read lexbuf) with
  | Lexer.Syntax_error msg ->
      Error (Printf.sprintf "%s in %s at %s" msg context (position lexbuf))
  | Parser.Error ->
      Error (Printf.sprintf "parse error in %s at %s" context (position lexbuf))

let rec seq_of_list = function
  | [] -> Skip
  | [stmt] -> stmt
  | stmts ->
      let stmts =
        List.concat_map
          (function
            | Seq inner -> inner
            | stmt -> [stmt])
          stmts
      in
      (match stmts with
      | [] -> Skip
      | [stmt] -> stmt
      | _ -> Seq stmts)

let assoc_opt key bindings =
  List.find_map
    (fun (name, value) ->
      if String.equal name key then Some value else None)
    bindings

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

let rec substitute_expr bindings = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr -> expr
  | Var name -> Option.value (assoc_opt name bindings) ~default:(Var name)
  | AddrOf inner -> AddrOf (substitute_expr bindings inner)
  | Index (base, index) ->
      Index (substitute_expr bindings base, substitute_expr bindings index)
  | Deref inner -> Deref (substitute_expr bindings inner)
  | Field (base, field) ->
      Field (substitute_expr bindings base, field)
  | Add (left, right) ->
      Add (substitute_expr bindings left, substitute_expr bindings right)
  | Sub (left, right) ->
      Sub (substitute_expr bindings left, substitute_expr bindings right)
  | Mul (left, right) ->
      Mul (substitute_expr bindings left, substitute_expr bindings right)
  | Div (left, right) ->
      Div (substitute_expr bindings left, substitute_expr bindings right)
  | Mod (left, right) ->
      Mod (substitute_expr bindings left, substitute_expr bindings right)
  | FuncCall (name, args) ->
      FuncCall (name, List.map (substitute_expr bindings) args)

let rec substitute_bexpr bindings = function
  | True -> True
  | False -> False
  | Forall (quantified, body) ->
      let bindings =
        List.filter
          (fun (name, _value) ->
            not
              (List.exists
                 (fun (binding : quantified_var) -> String.equal name binding.quant_name)
                 quantified))
          bindings
      in
      Forall (quantified, substitute_bexpr bindings body)
  | Eq (left, right) ->
      Eq (substitute_expr bindings left, substitute_expr bindings right)
  | Neq (left, right) ->
      Neq (substitute_expr bindings left, substitute_expr bindings right)
  | Lt (left, right) ->
      Lt (substitute_expr bindings left, substitute_expr bindings right)
  | Le (left, right) ->
      Le (substitute_expr bindings left, substitute_expr bindings right)
  | Gt (left, right) ->
      Gt (substitute_expr bindings left, substitute_expr bindings right)
  | Ge (left, right) ->
      Ge (substitute_expr bindings left, substitute_expr bindings right)
  | Not inner -> Not (substitute_bexpr bindings inner)
  | And (left, right) ->
      And (substitute_bexpr bindings left, substitute_bexpr bindings right)
  | Or (left, right) ->
      Or (substitute_bexpr bindings left, substitute_bexpr bindings right)

let rec expr_has_var target = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ -> false
  | Var name -> String.equal name target
  | AddrOf inner -> expr_has_var target inner
  | Index (base, index) ->
      expr_has_var target base || expr_has_var target index
  | Deref inner -> expr_has_var target inner
  | Field (base, _) -> expr_has_var target base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      expr_has_var target left || expr_has_var target right
  | FuncCall (_, args) -> List.exists (expr_has_var target) args

let rec bexpr_has_var target = function
  | True | False -> false
  | Forall (bindings, body) ->
      if List.exists (fun (binding : quantified_var) -> String.equal binding.quant_name target) bindings
      then false
      else bexpr_has_var target body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      expr_has_var target left || expr_has_var target right
  | Not inner -> bexpr_has_var target inner
  | And (left, right) | Or (left, right) ->
      bexpr_has_var target left || bexpr_has_var target right

type ghost_env = {
  scalar_bindings : (string * expr) list;
  bool_bindings : (string * bexpr) list;
  ghost_names : string list;
}

let empty_ghost_env ghost_names = {
  scalar_bindings = [];
  bool_bindings = [];
  ghost_names;
}

let rec substitute_expr_with_ghosts scalar_bindings bool_bindings = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr -> Ok expr
  | Var name ->
      (match assoc_opt name scalar_bindings with
      | Some value -> Ok value
      | None ->
          (match assoc_opt name bool_bindings with
          | Some _ ->
              Error
                (Printf.sprintf
                   "boolean ghost `%s` was used where a scalar expression was expected"
                   name)
          | None -> Ok (Var name)))
  | AddrOf inner ->
      let* inner = substitute_expr_with_ghosts scalar_bindings bool_bindings inner in
      Ok (AddrOf inner)
  | Index (base, index) ->
      let* base = substitute_expr_with_ghosts scalar_bindings bool_bindings base in
      let* index =
        substitute_expr_with_ghosts scalar_bindings bool_bindings index
      in
      Ok (Index (base, index))
  | Deref inner ->
      let* inner = substitute_expr_with_ghosts scalar_bindings bool_bindings inner in
      Ok (Deref inner)
  | Field (base, field) ->
      let* base = substitute_expr_with_ghosts scalar_bindings bool_bindings base in
      Ok (Field (base, field))
  | Add (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_expr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Add (left, right))
  | Sub (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_expr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Sub (left, right))
  | Mul (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_expr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Mul (left, right))
  | Div (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_expr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Div (left, right))
  | Mod (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_expr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Mod (left, right))
  | FuncCall (name, args) ->
      let rec loop acc = function
        | [] -> Ok (List.rev acc)
        | arg :: rest ->
            let* arg =
              substitute_expr_with_ghosts scalar_bindings bool_bindings arg
            in
            loop (arg :: acc) rest
      in
      let* args = loop [] args in
      Ok (FuncCall (name, args))

let bool_truthiness_binding bool_bindings positive left right =
  let matched_name =
    match left, right with
    | Var name, Int 0
    | Int 0, Var name ->
        Some name
    | _ ->
        None
  in
  match matched_name with
  | None -> None
  | Some name ->
      Option.map
        (fun binding -> if positive then binding else Not binding)
        (assoc_opt name bool_bindings)

let remove_shadowed_bindings names bindings =
  List.filter
    (fun (name, _value) ->
      not (List.exists (fun shadowed -> String.equal name shadowed) names))
    bindings

let rec substitute_bexpr_with_ghosts scalar_bindings bool_bindings = function
  | True -> Ok True
  | False -> Ok False
  | Forall (bindings, body) ->
      let bound_names =
        List.map (fun (binding : quantified_var) -> binding.quant_name) bindings
      in
      let scalar_bindings = remove_shadowed_bindings bound_names scalar_bindings in
      let bool_bindings = remove_shadowed_bindings bound_names bool_bindings in
      let* body = substitute_bexpr_with_ghosts scalar_bindings bool_bindings body in
      Ok (Forall (bindings, body))
  | Eq (left, right) ->
      (match bool_truthiness_binding bool_bindings false left right with
      | Some binding -> Ok binding
      | None ->
          let* left =
            substitute_expr_with_ghosts scalar_bindings bool_bindings left
          in
          let* right =
            substitute_expr_with_ghosts scalar_bindings bool_bindings right
          in
          Ok (Eq (left, right)))
  | Neq (left, right) ->
      (match bool_truthiness_binding bool_bindings true left right with
      | Some binding -> Ok binding
      | None ->
          let* left =
            substitute_expr_with_ghosts scalar_bindings bool_bindings left
          in
          let* right =
            substitute_expr_with_ghosts scalar_bindings bool_bindings right
          in
          Ok (Neq (left, right)))
  | Lt (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right = substitute_expr_with_ghosts scalar_bindings bool_bindings right in
      Ok (Lt (left, right))
  | Le (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right = substitute_expr_with_ghosts scalar_bindings bool_bindings right in
      Ok (Le (left, right))
  | Gt (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right = substitute_expr_with_ghosts scalar_bindings bool_bindings right in
      Ok (Gt (left, right))
  | Ge (left, right) ->
      let* left = substitute_expr_with_ghosts scalar_bindings bool_bindings left in
      let* right = substitute_expr_with_ghosts scalar_bindings bool_bindings right in
      Ok (Ge (left, right))
  | Not inner ->
      let* inner = substitute_bexpr_with_ghosts scalar_bindings bool_bindings inner in
      Ok (Not inner)
  | And (left, right) ->
      let* left = substitute_bexpr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_bexpr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (And (left, right))
  | Or (left, right) ->
      let* left = substitute_bexpr_with_ghosts scalar_bindings bool_bindings left in
      let* right =
        substitute_bexpr_with_ghosts scalar_bindings bool_bindings right
      in
      Ok (Or (left, right))

let unresolved_ghost_name_in_expr ghost_env expr =
  List.find_opt (fun name -> expr_has_var name expr) ghost_env.ghost_names

let unresolved_ghost_name_in_bexpr ghost_env bexpr =
  List.find_opt (fun name -> bexpr_has_var name bexpr) ghost_env.ghost_names

let ghost_context (contract_fn : contracted_function) (ghost : ghost_binding) =
  Printf.sprintf "@Ghost `%s` for `%s`" ghost.ghost_name contract_fn.name

let instantiate_ghost_binding
    (contract_fn : contracted_function)
    base_scalar_bindings
    ghost_env
    (ghost : ghost_binding) =
  if String.equal ghost.ghost_name "result" then
    Error
      (Printf.sprintf
         "@Ghost for `%s` cannot use the reserved name `result`"
         contract_fn.name)
  else if Option.is_some (assoc_opt ghost.ghost_name base_scalar_bindings) then
    Error
      (Printf.sprintf
         "@Ghost `%s` for `%s` conflicts with an existing binding"
         ghost.ghost_name
         contract_fn.name)
  else if Option.is_some (assoc_opt ghost.ghost_name ghost_env.scalar_bindings)
          || Option.is_some (assoc_opt ghost.ghost_name ghost_env.bool_bindings)
  then
    Error
      (Printf.sprintf
         "duplicate @Ghost `%s` for `%s`"
         ghost.ghost_name
         contract_fn.name)
  else
    let scalar_bindings = base_scalar_bindings @ ghost_env.scalar_bindings in
    match ghost.ghost_type with
    | TBool ->
        let* bexpr =
          parse_contract_bexpr (ghost_context contract_fn ghost) ghost.ghost_value
        in
        let* bexpr =
          substitute_bexpr_with_ghosts
            scalar_bindings
            ghost_env.bool_bindings
            bexpr
        in
        if bexpr_has_var "result" bexpr then
          Error
            (Printf.sprintf
               "@Ghost `%s` for `%s` references `result`, but ghosts are evaluated at function entry"
               ghost.ghost_name
               contract_fn.name)
        else
          (match unresolved_ghost_name_in_bexpr ghost_env bexpr with
          | Some name ->
              Error
                (Printf.sprintf
                   "@Ghost `%s` for `%s` references unresolved ghost `%s`"
                   ghost.ghost_name
                   contract_fn.name
                   name)
          | None ->
              Ok
                {
                  ghost_env with
                  bool_bindings =
                    ghost_env.bool_bindings @ [ ghost.ghost_name, bexpr ];
                })
    | TInt | TFloat | TDouble | TChar ->
        let* expr =
          parse_contract_expr (ghost_context contract_fn ghost) ghost.ghost_value
        in
        let* expr =
          substitute_expr_with_ghosts scalar_bindings ghost_env.bool_bindings expr
        in
        if expr_has_var "result" expr then
          Error
            (Printf.sprintf
               "@Ghost `%s` for `%s` references `result`, but ghosts are evaluated at function entry"
               ghost.ghost_name
               contract_fn.name)
        else
          (match unresolved_ghost_name_in_expr ghost_env expr with
          | Some name ->
              Error
                (Printf.sprintf
                   "@Ghost `%s` for `%s` references unresolved ghost `%s`"
                   ghost.ghost_name
                   contract_fn.name
                   name)
          | None ->
              Ok
                {
                  ghost_env with
                  scalar_bindings =
                    ghost_env.scalar_bindings @ [ ghost.ghost_name, expr ];
                })
    | TVoid | TRecord _ | TPointer _ | TArray _ | TReference _ | TConstReference _ ->
        Error
          (Printf.sprintf
             "unsupported @Ghost type `%s` for `%s`; only scalar ghost types are supported"
             (c_type_to_c ghost.ghost_type)
             contract_fn.name)

let instantiate_ghost_bindings
    (contract_fn : contracted_function)
    base_scalar_bindings =
  let ghost_names =
    List.map (fun (ghost : ghost_binding) -> ghost.ghost_name) contract_fn.contract.ghosts
  in
  let rec loop ghost_env = function
    | [] -> Ok ghost_env
    | ghost :: rest ->
        let* ghost_env =
          instantiate_ghost_binding contract_fn base_scalar_bindings ghost_env ghost
        in
        loop ghost_env rest
  in
  loop (empty_ghost_env ghost_names) contract_fn.contract.ghosts

let flatten_imports (imports : header_import list) : contracted_function list =
  List.concat_map
    (fun (imported_header : header_import) -> imported_header.functions)
    imports

let flatten_local_contracts (functions : function_def list) : contracted_function list =
  List.filter_map
    (fun (fn : function_def) ->
      Option.map
        (fun contract ->
          ({ name = fn.name; return_type = fn.return_type; params = fn.params; contract }
            : contracted_function))
        fn.contract)
    functions

let build_unique_env ~kind (functions : contracted_function list) =
  let rec loop
      (env : (string * contracted_function) list)
      (functions : contracted_function list) =
    match functions with
    | [] -> Ok env
    | fn :: rest ->
        (match assoc_opt fn.name env with
        | Some _ ->
            Error
              (Printf.sprintf "duplicate %s contract for function `%s`" kind fn.name)
        | None -> loop ((fn.name, fn) :: env) rest)
  in
  loop [] functions

let merge_env ~preferred ~fallback =
  preferred
  @ List.filter
      (fun (name, _) -> Option.is_none (assoc_opt name preferred))
      fallback

let build_contract_env
    (imports : header_import list)
    (functions : function_def list) =
  let ( let* ) result f =
    match result with
    | Ok value -> f value
    | Error _ as error -> error
  in
  let* imported = build_unique_env ~kind:"imported" (flatten_imports imports) in
  let* local = build_unique_env ~kind:"local" (flatten_local_contracts functions) in
  Ok (merge_env ~preferred:local ~fallback:imported)

type state = {
  next_temp : int;
  fresh_globals_rev : global_def list;
  used_names : var list;
}

let make_state (program : program) =
  let imported_names =
    flatten_imports program.imports
    |> List.map (fun (fn : contracted_function) -> fn.name)
  in
  let function_names =
    List.map (fun (fn : function_def) -> fn.name) program.functions
  in
  let local_names =
    List.concat_map
      (fun (fn : function_def) ->
        List.map (fun local -> local.global_name) fn.locals)
      (program.main :: program.functions)
  in
  {
    next_temp = 0;
    fresh_globals_rev = [];
    used_names =
      global_names program.globals
      @ local_names
      @ function_names
      @ [ program.main.name ]
      @ imported_names;
  }

let fresh_name global_type state =
  let rec pick next_temp =
    let candidate = Printf.sprintf "__anvil_contract_result_%d" next_temp in
    if List.exists (String.equal candidate) state.used_names then
      pick (next_temp + 1)
    else
      candidate, next_temp + 1
  in
  let name, next_temp = pick state.next_temp in
  name,
  {
    next_temp;
    fresh_globals_rev =
      { global_type; global_name = name } :: state.fresh_globals_rev;
    used_names = name :: state.used_names;
  }

let bind_params
    (contract_fn : contracted_function)
    (args : expr list) =
  let rec loop params args bindings =
    match params, args with
    | [], [] -> Ok (List.rev bindings)
    | param :: rest_params, arg :: rest_args ->
        let arg =
          match param.param_type with
          | TReference _ | TConstReference _ -> Deref arg
          | _ -> arg
        in
        let bindings =
          match param.param_name with
          | None -> bindings
          | Some name -> (name, arg) :: bindings
        in
        loop rest_params rest_args bindings
    | _ ->
        Error
          (Printf.sprintf
             "arity mismatch for contracted function `%s`"
             contract_fn.name)
  in
  loop contract_fn.params args []

let bind_definition_params
    (contract_fn : contracted_function)
    (params : param list) =
  let rec loop contract_params params bindings =
    match contract_params, params with
    | [], [] -> Ok (List.rev bindings)
    | contract_param :: rest_contract, param :: rest_params ->
        let bound_expr param_name =
          match contract_param.param_type with
          | TReference _ | TConstReference _ -> Deref (Var param_name)
          | _ -> Var param_name
        in
        let bindings =
          match contract_param.param_name, param.param_name with
          | Some contract_name, Some param_name ->
              (contract_name, bound_expr param_name) :: bindings
          | _ -> bindings
        in
        loop rest_contract rest_params bindings
    | _ ->
        Error
          (Printf.sprintf
             "arity mismatch for function definition `%s`"
             contract_fn.name)
  in
  loop contract_fn.params params []

let instantiate_contract_clause
    (memory_env : Memory_safety.contract_env)
    (contract_fn : contracted_function)
    kind
    text
    scalar_bindings
    bool_bindings
    ghost_env =
  match
    parse_contract_bexpr
      (Printf.sprintf "%s contract for `%s`" kind contract_fn.name)
      text
  with
  | Error msg -> Error msg
  | Ok bexpr ->
      let* bexpr =
        substitute_bexpr_with_ghosts scalar_bindings bool_bindings bexpr
      in
      (match unresolved_ghost_name_in_bexpr ghost_env bexpr with
      | Some name ->
          Error
            (Printf.sprintf
               "%s contract for `%s` references unresolved ghost `%s`"
               kind
               contract_fn.name
               name)
      | None ->
          Memory_safety.lower_contract_bexpr memory_env bexpr)

let rec instantiate_contracts
    (memory_env : Memory_safety.contract_env)
    (contract_fn : contracted_function)
    kind
    texts
    scalar_bindings
    bool_bindings
    ghost_env =
  match texts with
  | [] -> Ok []
  | text :: rest ->
      (match
         instantiate_contract_clause
           memory_env
           contract_fn
           kind
           text
           scalar_bindings
           bool_bindings
           ghost_env
       with
      | Error _ as error -> error
      | Ok clause ->
          (match
             instantiate_contracts
               memory_env
               contract_fn
               kind
               rest
               scalar_bindings
               bool_bindings
               ghost_env
           with
          | Error _ as error -> error
          | Ok rest -> Ok (clause :: rest)))

type current_contract = {
  memory_env : Memory_safety.contract_env;
  contract_fn : contracted_function;
  param_bindings : (string * expr) list;
  ghost_env : ghost_env;
}

let build_current_contract
    (memory_env : Memory_safety.contract_env)
    (contract_fn : contracted_function)
    (params : param list) =
  let* param_bindings = bind_definition_params contract_fn params in
  let* ghost_env = instantiate_ghost_bindings contract_fn param_bindings in
  Ok { memory_env; contract_fn; param_bindings; ghost_env }

let entry_scalar_bindings current =
  current.param_bindings @ current.ghost_env.scalar_bindings

let scalar_bindings_with_result current result =
  ("result", result) :: entry_scalar_bindings current

let substitute_current_expr current expr =
  let* expr =
    substitute_expr_with_ghosts
      (entry_scalar_bindings current)
      current.ghost_env.bool_bindings
      expr
  in
  match unresolved_ghost_name_in_expr current.ghost_env expr with
  | Some name ->
      Error
        (Printf.sprintf
           "expression in `%s` references unresolved ghost `%s`"
           current.contract_fn.name
           name)
  | None ->
      Ok expr

let substitute_current_bexpr current bexpr =
  let* bexpr =
    substitute_bexpr_with_ghosts
      (entry_scalar_bindings current)
      current.ghost_env.bool_bindings
      bexpr
  in
  match unresolved_ghost_name_in_bexpr current.ghost_env bexpr with
  | Some name ->
      Error
        (Printf.sprintf
           "condition in `%s` references unresolved ghost `%s`"
           current.contract_fn.name
           name)
  | None ->
      Ok bexpr

let param_types params =
  List.map (fun param -> param.param_type) params

let compatible_signature
    (fn : function_def)
    (contract_fn : contracted_function) =
  let expected_param_types =
    contract_fn.params
    |> List.map (fun (param : param) -> lower_reference_type param.param_type)
  in
  fn.return_type = contract_fn.return_type
  && param_types fn.params = expected_param_types

let effective_contract
    (env : (string * contracted_function) list)
    (fn : function_def) =
  match assoc_opt fn.name env with
  | None -> Ok None
  | Some contract_fn ->
      if compatible_signature fn contract_fn then
        Ok (Some contract_fn)
      else
        Error
          (Printf.sprintf
             "contract signature mismatch for function `%s`"
             fn.name)

let instantiate_void_guarantee current =
  let* guarantees =
    instantiate_contracts current.memory_env current.contract_fn "@Guarantee"
      current.contract_fn.contract.guarantee
      (entry_scalar_bindings current)
      current.ghost_env.bool_bindings
      current.ghost_env
  in
  if List.exists (bexpr_has_var "result") guarantees then
    Error
      (Printf.sprintf
         "@Guarantee for `%s` references `result` on a void return"
       current.contract_fn.name)
  else
    Ok guarantees

let instantiate_current_safety current =
  instantiate_contracts current.memory_env current.contract_fn "@Safety"
    current.contract_fn.contract.safety
    (entry_scalar_bindings current)
    current.ghost_env.bool_bindings
    current.ghost_env

let instantiate_step_safety current =
  let* safety = instantiate_current_safety current in
  if List.exists (bexpr_has_var "result") safety then
    Error
      (Printf.sprintf
         "@Safety for `%s` references `result` before return"
         current.contract_fn.name)
  else
    Ok safety

let instantiate_void_safety current =
  let* safety = instantiate_current_safety current in
  if List.exists (bexpr_has_var "result") safety then
    Error
      (Printf.sprintf
         "@Safety for `%s` references `result` on a void return"
         current.contract_fn.name)
  else
    Ok safety

let instantiate_current_safety_with_result current result =
  instantiate_contracts current.memory_env current.contract_fn "@Safety"
    current.contract_fn.contract.safety
    (scalar_bindings_with_result current result)
    current.ghost_env.bool_bindings
    current.ghost_env

let assert_clauses origin clauses =
  List.map (fun clause -> Assert (origin, clause)) clauses

let assume_clauses clauses =
  List.map (fun clause -> Assume clause) clauses

let append_safety_assert current stmts =
  let* safety = instantiate_step_safety current in
  Ok (seq_of_list (stmts @ assert_clauses (Function_safety current.contract_fn.name) safety))

let rec instrument_expr
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ ->
      Ok ([], expr, state)
  | AddrOf inner ->
      let* prefix, inner, state = instrument_expr memory_env env state inner in
      Ok (prefix, AddrOf inner, state)
  | Index (base, index) ->
      let* base_prefix, base, state = instrument_expr memory_env env state base in
      let* index_prefix, index, state = instrument_expr memory_env env state index in
      Ok (base_prefix @ index_prefix, Index (base, index), state)
  | Deref inner ->
      let* prefix, inner, state = instrument_expr memory_env env state inner in
      Ok (prefix, Deref inner, state)
  | Field (base, field) ->
      let* prefix, base, state = instrument_expr memory_env env state base in
      Ok (prefix, Field (base, field), state)
  | Add (left, right) ->
      instrument_binary_expr memory_env env state left right (fun l r -> Add (l, r))
  | Sub (left, right) ->
      instrument_binary_expr memory_env env state left right (fun l r -> Sub (l, r))
  | Mul (left, right) ->
      instrument_binary_expr memory_env env state left right (fun l r -> Mul (l, r))
  | Div (left, right) ->
      instrument_binary_expr memory_env env state left right (fun l r -> Div (l, r))
  | Mod (left, right) ->
      instrument_binary_expr memory_env env state left right (fun l r -> Mod (l, r))
  | FuncCall (name, args) ->
      let* prefix, args, state = instrument_expr_list memory_env env state args in
      (match assoc_opt name env with
      | None -> Ok (prefix, FuncCall (name, args), state)
      | Some contract_fn ->
          (match contract_fn.return_type with
          | TVoid ->
              Error
                (Printf.sprintf
                   "instrumentation of contracted void function `%s` is unsupported"
                   contract_fn.name)
          | _ ->
              let* bindings = bind_params contract_fn args in
              let* ghost_env = instantiate_ghost_bindings contract_fn bindings in
              let result_name, state = fresh_name contract_fn.return_type state in
              let result_expr = Var result_name in
              let* require =
                instantiate_contracts memory_env contract_fn "@Require"
                  contract_fn.contract.require
                  (bindings @ ghost_env.scalar_bindings)
                  ghost_env.bool_bindings
                  ghost_env
              in
              let* safety =
                instantiate_contracts memory_env contract_fn "@Safety"
                  contract_fn.contract.safety
                  ([ ("result", result_expr) ] @ bindings @ ghost_env.scalar_bindings)
                  ghost_env.bool_bindings
                  ghost_env
              in
              let* guarantee =
                instantiate_contracts memory_env contract_fn "@Guarantee"
                  contract_fn.contract.guarantee
                  ([ ("result", result_expr) ] @ bindings @ ghost_env.scalar_bindings)
                  ghost_env.bool_bindings
                  ghost_env
              in
              Ok
                ( prefix
                  @ assert_clauses (Call_require contract_fn.name) require
                  @ [ Assign (result_name, FuncCall (name, args)) ]
                  @ assume_clauses guarantee
                  @ assume_clauses safety
                , result_expr
                , state )))

and instrument_binary_expr
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    left
    right
    mk =
  let* left_prefix, left, state = instrument_expr memory_env env state left in
  let* right_prefix, right, state = instrument_expr memory_env env state right in
  Ok (left_prefix @ right_prefix, mk left right, state)

and instrument_expr_list
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    exprs =
  match exprs with
  | [] -> Ok ([], [], state)
  | expr :: rest ->
      let* prefix, expr, state = instrument_expr memory_env env state expr in
      let* rest_prefix, rest, state = instrument_expr_list memory_env env state rest in
      Ok (prefix @ rest_prefix, expr :: rest, state)

and instrument_bexpr
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    bexpr =
  match bexpr with
  | True | False -> Ok ([], bexpr, state)
  | Forall (bindings, body) ->
      let* prefix, body, state = instrument_bexpr memory_env env state body in
      if prefix <> [] then
        Error "instrumented calls inside quantified formulas are unsupported"
      else
        Ok ([], Forall (bindings, body), state)
  | Eq (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Eq (l, r))
  | Neq (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Neq (l, r))
  | Lt (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Lt (l, r))
  | Le (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Le (l, r))
  | Gt (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Gt (l, r))
  | Ge (left, right) ->
      instrument_expr_comparison memory_env env state left right (fun l r -> Ge (l, r))
  | Not inner ->
      let* prefix, inner, state = instrument_bexpr memory_env env state inner in
      Ok (prefix, Not inner, state)
  | And (left, right) ->
      let* left_prefix, left, state = instrument_bexpr memory_env env state left in
      let* right_prefix, right, state = instrument_bexpr memory_env env state right in
      if left_prefix <> [] || right_prefix <> [] then
        Error "instrumented calls inside `&&` conditions are unsupported"
      else
        Ok ([], And (left, right), state)
  | Or (left, right) ->
      let* left_prefix, left, state = instrument_bexpr memory_env env state left in
      let* right_prefix, right, state = instrument_bexpr memory_env env state right in
      if left_prefix <> [] || right_prefix <> [] then
        Error "instrumented calls inside `||` conditions are unsupported"
      else
        Ok ([], Or (left, right), state)

and instrument_stmt
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    (current_contract : current_contract option)
    state
    stmt =
  match stmt with
  | Skip ->
      (match current_contract with
      | None -> Ok (Skip, state)
      | Some current ->
          let* stmt = append_safety_assert current [ Skip ] in
          Ok (stmt, state))
  | Break | Continue ->
      fail "`break`/`continue` reached contract instrumentation"
  | Block _ | LocalDecl _ ->
      Error "unresolved local syntax reached contract instrumentation"
  | Assign (name, expr) ->
      let* expr =
        match current_contract with
        | None -> Ok expr
        | Some current -> substitute_current_expr current expr
      in
      let* prefix, expr, state = instrument_expr memory_env env state expr in
      (match current_contract with
      | None -> Ok (seq_of_list (prefix @ [ Assign (name, expr) ]), state)
      | Some current ->
          let* stmt = append_safety_assert current (prefix @ [ Assign (name, expr) ]) in
          Ok (stmt, state))
  | Store (ptr, value) ->
      let* ptr =
        match current_contract with
        | None -> Ok ptr
        | Some current -> substitute_current_expr current ptr
      in
      let* value =
        match current_contract with
        | None -> Ok value
        | Some current -> substitute_current_expr current value
      in
      let* ptr_prefix, ptr, state = instrument_expr memory_env env state ptr in
      let* value_prefix, value, state = instrument_expr memory_env env state value in
      (match current_contract with
      | None -> Ok (seq_of_list (ptr_prefix @ value_prefix @ [ Store (ptr, value) ]), state)
      | Some current ->
          let* stmt =
            append_safety_assert current (ptr_prefix @ value_prefix @ [ Store (ptr, value) ])
          in
          Ok (stmt, state))
  | ArrayAssign (base, index, value) ->
      let* base =
        match current_contract with
        | None -> Ok base
        | Some current -> substitute_current_expr current base
      in
      let* index =
        match current_contract with
        | None -> Ok index
        | Some current -> substitute_current_expr current index
      in
      let* value =
        match current_contract with
        | None -> Ok value
        | Some current -> substitute_current_expr current value
      in
      let* base_prefix, base, state = instrument_expr memory_env env state base in
      let* index_prefix, index, state = instrument_expr memory_env env state index in
      let* value_prefix, value, state = instrument_expr memory_env env state value in
      (match current_contract with
      | None ->
          Ok
            ( seq_of_list
                (base_prefix @ index_prefix @ value_prefix @ [ ArrayAssign (base, index, value) ])
            , state )
      | Some current ->
          let* stmt =
            append_safety_assert current
              (base_prefix @ index_prefix @ value_prefix @ [ ArrayAssign (base, index, value) ])
          in
          Ok (stmt, state))
  | FieldAssign (base, field, value) ->
      let* base =
        match current_contract with
        | None -> Ok base
        | Some current -> substitute_current_expr current base
      in
      let* value =
        match current_contract with
        | None -> Ok value
        | Some current -> substitute_current_expr current value
      in
      let* base_prefix, base, state = instrument_expr memory_env env state base in
      let* value_prefix, value, state = instrument_expr memory_env env state value in
      (match current_contract with
      | None ->
          Ok (seq_of_list (base_prefix @ value_prefix @ [ FieldAssign (base, field, value) ]), state)
      | Some current ->
          let* stmt =
            append_safety_assert current
              (base_prefix @ value_prefix @ [ FieldAssign (base, field, value) ])
          in
          Ok (stmt, state))
  | Assume cond ->
      let* cond =
        match current_contract with
        | None -> Ok cond
        | Some current -> substitute_current_bexpr current cond
      in
      let* prefix, cond, state = instrument_bexpr memory_env env state cond in
      (match current_contract with
      | None -> Ok (seq_of_list (prefix @ [ Assume cond ]), state)
      | Some current ->
          let* stmt = append_safety_assert current (prefix @ [ Assume cond ]) in
          Ok (stmt, state))
  | Assert (origin, cond) ->
      let* cond =
        match current_contract with
        | None -> Ok cond
        | Some current -> substitute_current_bexpr current cond
      in
      let* prefix, cond, state = instrument_bexpr memory_env env state cond in
      (match current_contract with
      | None -> Ok (seq_of_list (prefix @ [ Assert (origin, cond) ]), state)
      | Some current ->
          let* stmt =
            append_safety_assert current (prefix @ [ Assert (origin, cond) ])
          in
          Ok (stmt, state))
  | Return value ->
      let* prefix, value, state =
        match value with
        | None -> Ok ([], None, state)
        | Some expr ->
            let* expr =
              match current_contract with
              | None -> Ok expr
              | Some current -> substitute_current_expr current expr
            in
            let* prefix, expr, state = instrument_expr memory_env env state expr in
            Ok (prefix, Some expr, state)
      in
      (match current_contract with
      | None -> Ok (seq_of_list (prefix @ [ Return value ]), state)
      | Some current ->
          let* safety =
            match value with
            | Some result -> instantiate_current_safety_with_result current result
            | None -> instantiate_void_safety current
          in
          let* guarantee =
            match value with
            | Some result ->
                instantiate_contracts current.memory_env current.contract_fn "@Guarantee"
                  current.contract_fn.contract.guarantee
                  (scalar_bindings_with_result current result)
                  current.ghost_env.bool_bindings
                  current.ghost_env
            | None -> instantiate_void_guarantee current
          in
          Ok
            ( seq_of_list
                ( prefix
                @ assert_clauses (Function_safety current.contract_fn.name) safety
                @ assert_clauses (Function_guarantee current.contract_fn.name) guarantee
                @ [ Return value ] )
            , state ))
  | Seq stmts ->
      let* stmts, state =
        instrument_stmt_list memory_env env current_contract state stmts
      in
      Ok (seq_of_list stmts, state)
  | If (cond, then_branch, else_branch) ->
      let* cond =
        match current_contract with
        | None -> Ok cond
        | Some current -> substitute_current_bexpr current cond
      in
      let* prefix, cond, state = instrument_bexpr memory_env env state cond in
      let* then_branch, state =
        instrument_stmt memory_env env current_contract state then_branch
      in
      let* else_branch, state =
        instrument_stmt memory_env env current_contract state else_branch
      in
      (match current_contract with
      | None ->
          Ok (seq_of_list (prefix @ [ If (cond, then_branch, else_branch) ]), state)
      | Some current ->
          let* stmt =
            append_safety_assert current (prefix @ [ If (cond, then_branch, else_branch) ])
          in
          Ok (stmt, state))
  | While (invariant, cond, body) ->
      let* invariant =
        match current_contract, invariant with
        | _, None -> Ok None
        | None, Some invariant -> Ok (Some invariant)
        | Some current, Some invariant ->
            let* invariant = substitute_current_bexpr current invariant in
            Ok (Some invariant)
      in
      let* cond =
        match current_contract with
        | None -> Ok cond
        | Some current -> substitute_current_bexpr current cond
      in
      let* prefix, cond, state = instrument_bexpr memory_env env state cond in
      if prefix <> [] then
        Error "instrumented calls inside `while` conditions are unsupported"
      else
        let* body, state = instrument_stmt memory_env env current_contract state body in
        (match current_contract with
        | None -> Ok (While (invariant, cond, body), state)
        | Some current ->
            let* stmt = append_safety_assert current [ While (invariant, cond, body) ] in
            Ok (stmt, state))
  | Free ptr ->
      let* ptr =
        match current_contract with
        | None -> Ok ptr
        | Some current -> substitute_current_expr current ptr
      in
      let* prefix, ptr, state = instrument_expr memory_env env state ptr in
      (match current_contract with
      | None -> Ok (seq_of_list (prefix @ [ Free ptr ]), state)
      | Some current ->
          let* stmt = append_safety_assert current (prefix @ [ Free ptr ]) in
          Ok (stmt, state))

and instrument_expr_comparison
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    left
    right
    mk =
  let* left_prefix, left, state = instrument_expr memory_env env state left in
  let* right_prefix, right, state = instrument_expr memory_env env state right in
  Ok (left_prefix @ right_prefix, mk left right, state)

and instrument_stmt_list
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    (current_contract : current_contract option)
    state
    stmts =
  match stmts with
  | [] -> Ok ([], state)
  | stmt :: rest ->
      let* stmt, state = instrument_stmt memory_env env current_contract state stmt in
      let* rest, state =
        instrument_stmt_list memory_env env current_contract state rest
      in
      Ok (stmt :: rest, state)

let instrument_function
    (program : program)
    (memory_env : Memory_safety.contract_env)
    (env : (string * contracted_function) list)
    state
    (fn : function_def) =
  let memory_env =
    Memory_safety.function_env_of_program program fn memory_env.malloc_sites
  in
  let* contract = effective_contract env fn in
  match contract with
  | None ->
      let* body, state = instrument_stmt memory_env env None state fn.body in
      Ok ({ fn with body }, state)
  | Some contract_fn ->
      let* current = build_current_contract memory_env contract_fn fn.params in
      let* body, state =
        instrument_stmt memory_env env (Some current) state fn.body
      in
      let* require =
        instantiate_contracts
          memory_env
          contract_fn
          "@Require"
          contract_fn.contract.require
          (entry_scalar_bindings current)
          current.ghost_env.bool_bindings
          current.ghost_env
      in
      let body = seq_of_list (assume_clauses require @ [ body ]) in
      let* body =
        match fn.return_type with
        | TVoid ->
            let* safety = instantiate_void_safety current in
            let* guarantee = instantiate_void_guarantee current in
            Ok
              (seq_of_list
                 ([ body ]
                 @ assert_clauses (Function_safety current.contract_fn.name) safety
                 @ assert_clauses (Function_guarantee current.contract_fn.name) guarantee))
        | _ -> Ok body
      in
      Ok ({ fn with body }, state)

let rec instrument_functions_for_program program memory_env env state functions =
  match functions with
  | [] -> Ok ([], state)
  | fn :: rest ->
      let* fn, state = instrument_function program memory_env env state fn in
      let* rest, state =
        instrument_functions_for_program program memory_env env state rest
      in
      Ok (fn :: rest, state)

let instrument_program program =
  let* env =
    build_contract_env program.imports (program.functions @ [ program.main ])
  in
  let* program = Memory_safety.lower_references_program program in
  let memory_env = Memory_safety.contract_env_of_program program in
  let* functions, state =
    instrument_functions_for_program
      program
      memory_env
      env
      (make_state program)
      program.functions
  in
  let* main, state =
    instrument_function program memory_env env state program.main
  in
  let instrumented =
    {
      program with
      globals = program.globals @ List.rev state.fresh_globals_rev;
      functions;
      main;
    }
  in
  Memory_safety.lower_program instrumented
