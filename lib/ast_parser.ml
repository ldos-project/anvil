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

let has_mangled_namespace name =
  contains_substring ~sub:namespace_separator name

let rec drop_last = function
  | [] -> []
  | [ _ ] -> []
  | first :: rest -> first :: drop_last rest

let rec namespace_search_paths = function
  | [] -> [ [] ]
  | namespace_path as current ->
      current :: namespace_search_paths (drop_last namespace_path)

let name_in_env names target =
  List.exists (String.equal target) names

let namespace_reference_candidates ~current_namespace name =
  if has_mangled_namespace name then
    [ name ]
  else
    let components =
      if has_raw_namespace name then
        split_on_substring ~sep:raw_namespace_separator name
      else
        [ name ]
    in
    namespace_search_paths current_namespace
    |> List.map (fun namespace_path ->
           mangle_namespace_path (namespace_path @ components))

let resolve_namespace_reference ~available ~current_namespace name =
  namespace_reference_candidates ~current_namespace name
  |> List.find_opt (name_in_env available)
  |> Option.value
       ~default:
         (if has_raw_namespace name then mangle_raw_namespace_name name else name)

let rec resolve_type_names ~records ~current_namespace = function
  | TInt | TFloat | TDouble | TChar | TBool | TVoid as c_type -> c_type
  | TRecord name ->
      TRecord
        (resolve_namespace_reference
           ~available:records
           ~current_namespace
           name)
  | TPointer inner ->
      TPointer (resolve_type_names ~records ~current_namespace inner)
  | TArray (inner, size) ->
      TArray (resolve_type_names ~records ~current_namespace inner, size)

let resolve_field_type_names records record =
  let current_namespace = namespace_path_of_name record.record_name in
  {
    record with
    fields =
      List.map
        (fun field ->
          {
            field with
            field_type =
              resolve_type_names
                ~records
                ~current_namespace
                field.field_type;
          })
        record.fields;
  }

let resolve_global_type_names records global =
  let current_namespace = namespace_path_of_name global.global_name in
  {
    global with
    global_type =
      resolve_type_names
        ~records
        ~current_namespace
        global.global_type;
  }

let resolve_param_type_names records current_namespace param =
  {
    param with
    param_type =
      resolve_type_names
        ~records
        ~current_namespace
        param.param_type;
  }

let resolve_function_type_names records fn =
  let current_namespace = namespace_path_of_name fn.name in
  {
    fn with
    return_type =
      resolve_type_names
        ~records
        ~current_namespace
        fn.return_type;
    params =
      List.map (resolve_param_type_names records current_namespace) fn.params;
    locals =
      List.map
        (fun local ->
          {
            local with
            global_type =
              resolve_type_names
                ~records
                ~current_namespace
                local.global_type;
          })
        fn.locals;
  }

let resolve_program_type_names program =
  let records =
    List.map (fun (record : record_def) -> record.record_name) program.records
  in
  {
    program with
    records = List.map (resolve_field_type_names records) program.records;
    globals = List.map (resolve_global_type_names records) program.globals;
    functions = List.map (resolve_function_type_names records) program.functions;
    main =
      {
        (resolve_function_type_names records program.main) with
        name = program.main.name;
      };
  }

type class_info = {
  class_name : string;
  field_names : string list;
  method_names : string list;
}

type desugar_env = {
  records : record_def list;
  vars : (string * c_type) list;
  function_sigs : (string * (c_type list * c_type)) list;
  classes : (string * class_info) list;
}

let generated_method_info (fn : function_def) =
  match fn.params with
  | { param_type = TPointer (TRecord class_name); param_name = Some receiver } :: _
    when String.equal receiver method_this_name ->
      (match parse_class_method_name fn.name with
      | Some (name_class, method_name) when String.equal class_name name_class ->
          Some (class_name, method_name)
      | Some _ | None ->
          None)
  | _ ->
      None

let build_class_infos (program : program) =
  let add_method class_name method_name classes =
    let existing =
      Option.value
        (assoc_opt class_name classes)
        ~default:
          {
            class_name;
            field_names =
              (match lookup_record program.records class_name with
              | Some record ->
                  List.map (fun field -> field.field_name) record.fields
              | None ->
                  []);
            method_names = [];
          }
    in
    let updated =
      {
        existing with
        method_names =
          List.sort_uniq String.compare (method_name :: existing.method_names);
      }
    in
    (class_name, updated)
    :: List.filter (fun (name, _) -> not (String.equal name class_name)) classes
  in
  List.fold_left
    (fun classes fn ->
      match generated_method_info fn with
      | Some (class_name, method_name) ->
          add_method class_name method_name classes
      | None ->
          classes)
    []
    program.functions

let build_function_sigs (program : program) =
  let imported =
    List.concat_map
      (fun (imported_header : header_import) -> imported_header.functions)
      program.imports
    |> List.map (fun (fn : contracted_function) ->
           fn.name,
           ( List.map (fun param -> param.param_type) fn.params
           , fn.return_type ))
  in
  let locals =
    List.map
      (fun (fn : function_def) ->
        fn.name,
        ( List.map (fun param -> param.param_type) fn.params
        , fn.return_type ))
      (program.functions @ [ program.main ])
  in
  imported @ locals

let lookup_var_type env name =
  assoc_opt name env.vars

let lookup_function_sig env name =
  assoc_opt name env.function_sigs

let lookup_class_info env class_name =
  assoc_opt class_name env.classes

let rec desugar_addressable_type env = function
  | Var name ->
      lookup_var_type env name
  | Field (base, field) ->
      (match desugar_record_receiver_type env base with
      | Some record_name -> record_field_type env.records record_name field
      | None -> None)
  | Index (base, _) ->
      (match desugar_expr_type env base with
      | Some (TPointer pointee) -> Some pointee
      | Some (TArray (element_type, _)) -> Some element_type
      | Some _ | None -> None)
  | Deref expr ->
      (match desugar_expr_type env expr with
      | Some (TPointer pointee) -> Some pointee
      | Some _ | None -> None)
  | Int _
  | FloatLit _
  | DoubleLit _
  | CharLit _
  | BoolLit _
  | AddrOf _
  | Add _
  | Sub _
  | Mul _
  | Div _
  | Mod _
  | FuncCall _ ->
      None

and desugar_record_receiver_type env expr =
  match desugar_addressable_type env expr with
  | Some (TRecord record_name) -> Some record_name
  | Some _ | None -> None

and desugar_expr_type env = function
  | Int _ -> Some TInt
  | FloatLit _ -> Some TFloat
  | DoubleLit _ -> Some TDouble
  | CharLit _ -> Some TChar
  | BoolLit _ -> Some TBool
  | Var name ->
      lookup_var_type env name
  | AddrOf expr ->
      Option.map (fun c_type -> TPointer c_type) (desugar_addressable_type env expr)
  | Index (base, _) ->
      (match desugar_expr_type env base with
      | Some (TPointer pointee) -> Some pointee
      | Some (TArray (element_type, _)) -> Some element_type
      | Some _ | None -> None)
  | Deref expr ->
      (match desugar_expr_type env expr with
      | Some (TPointer pointee) -> Some pointee
      | Some _ | None -> None)
  | Field (base, field) ->
      (match desugar_record_receiver_type env base with
      | Some record_name -> record_field_type env.records record_name field
      | None -> None)
  | Add (left, right) ->
      (match desugar_expr_type env left, desugar_expr_type env right with
      | Some (TPointer pointee), Some right_type when is_integer_like_type right_type ->
          Some (TPointer pointee)
      | Some left_type, Some (TPointer pointee) when is_integer_like_type left_type ->
          Some (TPointer pointee)
      | Some left_type, Some right_type ->
          if is_real_type left_type || is_real_type right_type then Some TDouble else Some TInt
      | (Some _ | None), (Some _ | None) ->
          None)
  | Sub (left, right) ->
      (match desugar_expr_type env left, desugar_expr_type env right with
      | Some (TPointer pointee), Some right_type when is_integer_like_type right_type ->
          Some (TPointer pointee)
      | Some left_type, Some right_type ->
          if is_real_type left_type || is_real_type right_type then Some TDouble else Some TInt
      | (Some _ | None), (Some _ | None) ->
          None)
  | Mul (left, right)
  | Div (left, right) ->
      (match desugar_expr_type env left, desugar_expr_type env right with
      | Some left_type, Some right_type ->
          if is_real_type left_type || is_real_type right_type then Some TDouble else Some TInt
      | (Some _ | None), (Some _ | None) ->
          None)
  | Mod _ ->
      Some TInt
  | FuncCall (name, args) ->
      (match parse_method_call_name name, args with
      | Some (Method_dot, method_name), receiver :: _ ->
          (match desugar_expr_type env receiver with
          | Some (TRecord class_name) ->
              (match lookup_class_info env class_name with
              | Some class_info when List.mem method_name class_info.method_names ->
                  (match
                     lookup_function_sig env (class_method_name class_name method_name)
                   with
                  | Some (_, return_type) -> Some return_type
                  | None -> None)
              | Some _ | None -> None)
          | Some _ | None ->
              None)
      | Some (Method_arrow, method_name), receiver :: _ ->
          (match desugar_expr_type env receiver with
          | Some (TPointer (TRecord class_name)) ->
              (match lookup_class_info env class_name with
              | Some class_info when List.mem method_name class_info.method_names ->
                  (match
                     lookup_function_sig env (class_method_name class_name method_name)
                   with
                  | Some (_, return_type) -> Some return_type
                  | None -> None)
              | Some _ | None -> None)
          | Some _ | None ->
              None)
      | Some _, [] ->
          None
      | None, _ ->
          Option.map snd (lookup_function_sig env name))

let desugar_env_for_function (program : program) classes fn =
  {
    records = program.records;
    vars =
      (List.map (fun global -> global.global_name, global.global_type) program.globals)
      @ List.map (fun local -> local.global_name, local.global_type) fn.locals
      @ List.filter_map
          (fun param ->
            Option.map (fun name -> name, param.param_type) param.param_name)
          fn.params;
    function_sigs = build_function_sigs program;
    classes;
  }

let desugar_receiver_method_call env kind method_name receiver args =
  let receiver_type = desugar_expr_type env receiver in
  let class_name, receiver_arg =
    match kind, receiver_type with
    | Method_dot, Some (TRecord class_name) ->
        class_name, AddrOf receiver
    | Method_arrow, Some (TPointer (TRecord class_name)) ->
        class_name, receiver
    | Method_dot, Some other ->
        failwith
          (Printf.sprintf
             "`.` method call `%s` requires an object receiver, got `%s`"
             method_name
             (c_type_to_c other))
    | Method_arrow, Some other ->
        failwith
          (Printf.sprintf
             "`->` method call `%s` requires a pointer receiver, got `%s`"
             method_name
             (c_type_to_c other))
    | _, None ->
        failwith
          (Printf.sprintf
             "could not infer the receiver type for method `%s`"
             method_name)
  in
  match lookup_class_info env class_name with
  | Some class_info when List.mem method_name class_info.method_names ->
      FuncCall (class_method_name class_name method_name, receiver_arg :: args)
  | Some _ | None ->
      failwith
        (Printf.sprintf
           "unknown method `%s` on class `%s`"
           method_name
           class_name)

let rec desugar_method_expr env current_class = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr ->
      expr
  | Var name ->
      (match current_class with
      | Some class_info when List.mem name class_info.field_names ->
          Field (Deref (Var method_this_name), name)
      | Some _ | None ->
          Var name)
  | AddrOf expr ->
      AddrOf (desugar_method_expr env current_class expr)
  | Index (base, index) ->
      Index
        (desugar_method_expr env current_class base, desugar_method_expr env current_class index)
  | Deref expr ->
      Deref (desugar_method_expr env current_class expr)
  | Field (base, field) ->
      Field (desugar_method_expr env current_class base, field)
  | Add (left, right) ->
      Add
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Sub (left, right) ->
      Sub
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Mul (left, right) ->
      Mul
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Div (left, right) ->
      Div
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Mod (left, right) ->
      Mod
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | FuncCall (name, args) ->
      let args = List.map (desugar_method_expr env current_class) args in
      (match parse_method_call_name name, args with
      | Some (kind, method_name), receiver :: method_args ->
          desugar_receiver_method_call env kind method_name receiver method_args
      | Some _, [] ->
          failwith
            (Printf.sprintf
               "internal error: missing receiver while desugaring `%s`"
               name)
      | None, _ ->
          (match current_class with
          | Some class_info when List.mem name class_info.method_names ->
              FuncCall
                (class_method_name class_info.class_name name, Var method_this_name :: args)
          | Some _ | None ->
              FuncCall (name, args)))

let rec desugar_method_bexpr env current_class = function
  | True -> True
  | False -> False
  | Eq (left, right) ->
      Eq
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Neq (left, right) ->
      Neq
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Lt (left, right) ->
      Lt
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Le (left, right) ->
      Le
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Gt (left, right) ->
      Gt
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Ge (left, right) ->
      Ge
        (desugar_method_expr env current_class left, desugar_method_expr env current_class right)
  | Not inner ->
      Not (desugar_method_bexpr env current_class inner)
  | And (left, right) ->
      And
        ( desugar_method_bexpr env current_class left
        , desugar_method_bexpr env current_class right )
  | Or (left, right) ->
      Or
        ( desugar_method_bexpr env current_class left
        , desugar_method_bexpr env current_class right )

let rec desugar_method_stmt env current_class = function
  | Skip -> Skip
  | Block stmts ->
      Block (List.map (desugar_method_stmt env current_class) stmts)
  | LocalDecl _ ->
      failwith "internal error: unresolved local declaration reached class desugaring"
  | Assign (name, rhs) ->
      let rhs = desugar_method_expr env current_class rhs in
      (match current_class with
      | Some class_info when List.mem name class_info.field_names ->
          FieldAssign (Deref (Var method_this_name), name, rhs)
      | Some _ | None ->
          Assign (name, rhs))
  | Store (ptr, value) ->
      Store
        ( desugar_method_expr env current_class ptr
        , desugar_method_expr env current_class value )
  | ArrayAssign (base, index, value) ->
      ArrayAssign
        ( desugar_method_expr env current_class base
        , desugar_method_expr env current_class index
        , desugar_method_expr env current_class value )
  | FieldAssign (base, field, value) ->
      FieldAssign
        ( desugar_method_expr env current_class base
        , field
        , desugar_method_expr env current_class value )
  | Seq stmts ->
      Seq (List.map (desugar_method_stmt env current_class) stmts)
  | If (cond, then_branch, else_branch) ->
      If
        ( desugar_method_bexpr env current_class cond
        , desugar_method_stmt env current_class then_branch
        , desugar_method_stmt env current_class else_branch )
  | While (invariant, cond, body) ->
      While
        ( Option.map (desugar_method_bexpr env current_class) invariant
        , desugar_method_bexpr env current_class cond
        , desugar_method_stmt env current_class body )
  | Assume cond ->
      Assume (desugar_method_bexpr env current_class cond)
  | Assert (origin, cond) ->
      Assert (origin, desugar_method_bexpr env current_class cond)
  | Free ptr ->
      Free (desugar_method_expr env current_class ptr)
  | Return value ->
      Return (Option.map (desugar_method_expr env current_class) value)

let desugar_class_function program classes fn =
  let env = desugar_env_for_function program classes fn in
  let current_class =
    match generated_method_info fn with
    | Some (class_name, _method_name) ->
        lookup_class_info env class_name
    | None ->
        None
  in
  { fn with body = normalize_stmt (desugar_method_stmt env current_class fn.body) }

let desugar_classes program =
  let classes = build_class_infos program in
  {
    program with
    functions = List.map (desugar_class_function program classes) program.functions;
    main = desugar_class_function program classes program.main;
  }

type value_resolve_env = {
  current_namespace : string list;
  global_names : string list;
  function_names : string list;
  protected_names : string list;
}

let protected_name env name =
  name_in_env env.protected_names name

let resolve_global_name env name =
  if protected_name env name then name
  else
    resolve_namespace_reference
      ~available:env.global_names
      ~current_namespace:env.current_namespace
      name

let resolve_function_name env name =
  resolve_namespace_reference
    ~available:env.function_names
    ~current_namespace:env.current_namespace
    name

let rec resolve_value_expr env = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr -> expr
  | Var name ->
      Var (resolve_global_name env name)
  | AddrOf expr ->
      AddrOf (resolve_value_expr env expr)
  | Index (base, index) ->
      Index (resolve_value_expr env base, resolve_value_expr env index)
  | Deref expr ->
      Deref (resolve_value_expr env expr)
  | Field (base, field) ->
      Field (resolve_value_expr env base, field)
  | Add (left, right) ->
      Add (resolve_value_expr env left, resolve_value_expr env right)
  | Sub (left, right) ->
      Sub (resolve_value_expr env left, resolve_value_expr env right)
  | Mul (left, right) ->
      Mul (resolve_value_expr env left, resolve_value_expr env right)
  | Div (left, right) ->
      Div (resolve_value_expr env left, resolve_value_expr env right)
  | Mod (left, right) ->
      Mod (resolve_value_expr env left, resolve_value_expr env right)
  | FuncCall (name, args) ->
      FuncCall
        (resolve_function_name env name, List.map (resolve_value_expr env) args)

let rec resolve_value_bexpr env = function
  | True -> True
  | False -> False
  | Eq (left, right) ->
      Eq (resolve_value_expr env left, resolve_value_expr env right)
  | Neq (left, right) ->
      Neq (resolve_value_expr env left, resolve_value_expr env right)
  | Lt (left, right) ->
      Lt (resolve_value_expr env left, resolve_value_expr env right)
  | Le (left, right) ->
      Le (resolve_value_expr env left, resolve_value_expr env right)
  | Gt (left, right) ->
      Gt (resolve_value_expr env left, resolve_value_expr env right)
  | Ge (left, right) ->
      Ge (resolve_value_expr env left, resolve_value_expr env right)
  | Not inner ->
      Not (resolve_value_bexpr env inner)
  | And (left, right) ->
      And (resolve_value_bexpr env left, resolve_value_bexpr env right)
  | Or (left, right) ->
      Or (resolve_value_bexpr env left, resolve_value_bexpr env right)

let rec resolve_value_stmt env = function
  | Skip -> Skip
  | Block stmts ->
      Block (List.map (resolve_value_stmt env) stmts)
  | LocalDecl _ ->
      failwith "internal error: unresolved local declaration reached namespace resolution"
  | Assign (name, value) ->
      Assign (resolve_global_name env name, resolve_value_expr env value)
  | Store (ptr, value) ->
      Store (resolve_value_expr env ptr, resolve_value_expr env value)
  | ArrayAssign (base, index, value) ->
      ArrayAssign
        ( resolve_value_expr env base
        , resolve_value_expr env index
        , resolve_value_expr env value )
  | FieldAssign (base, field, value) ->
      FieldAssign
        (resolve_value_expr env base, field, resolve_value_expr env value)
  | Seq stmts ->
      Seq (List.map (resolve_value_stmt env) stmts)
  | If (cond, then_branch, else_branch) ->
      If
        ( resolve_value_bexpr env cond
        , resolve_value_stmt env then_branch
        , resolve_value_stmt env else_branch )
  | While (invariant, cond, body) ->
      While
        ( Option.map (resolve_value_bexpr env) invariant
        , resolve_value_bexpr env cond
        , resolve_value_stmt env body )
  | Assume cond ->
      Assume (resolve_value_bexpr env cond)
  | Assert (origin, cond) ->
      Assert (origin, resolve_value_bexpr env cond)
  | Free ptr ->
      Free (resolve_value_expr env ptr)
  | Return value ->
      Return (Option.map (resolve_value_expr env) value)

let protected_names_for_function fn =
  List.filter_map (fun param -> param.param_name) fn.params
  @ List.map (fun local -> local.global_name) fn.locals

let resolve_function_values global_names function_names fn =
  let env =
    {
      current_namespace = namespace_path_of_name fn.name;
      global_names;
      function_names;
      protected_names = protected_names_for_function fn;
    }
  in
  { fn with body = normalize_stmt (resolve_value_stmt env fn.body) }

let resolve_program_values program =
  let global_names = List.map (fun global -> global.global_name) program.globals in
  let imported_function_names =
    List.concat_map
      (fun (imported_header : header_import) ->
        List.map (fun (fn : contracted_function) -> fn.name) imported_header.functions)
      program.imports
  in
  let function_names =
    imported_function_names
    @ List.map (fun fn -> fn.name) program.functions
    @ [ program.main.name ]
  in
  {
    program with
    functions =
      List.map (resolve_function_values global_names function_names) program.functions;
    main = resolve_function_values global_names function_names program.main;
  }

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
    let program = resolve_program_type_names program in
    let program = desugar_classes program in
    let program = resolve_program_values program in
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
