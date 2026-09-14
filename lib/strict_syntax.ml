open Ast

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

let errorf fmt = Printf.ksprintf (fun msg -> Error msg) fmt

let rec validate_list f = function
  | [] -> Ok ()
  | value :: rest ->
      let* () = f value in
      validate_list f rest

type env = {
  function_params : (string * c_type list) list;
}

let build_env (program : program) =
  let imported =
    List.concat_map (fun (header : header_import) -> header.functions) program.imports
    |> List.map (fun (fn : imported_function) ->
           fn.name, List.map (fun param -> param.param_type) fn.params)
  in
  let locals =
    List.map
      (fun (fn : function_def) ->
        fn.name, List.map (fun param -> param.param_type) fn.params)
      (program.functions @ [ program.main ])
  in
  { function_params = imported @ locals }

let lookup_function_params env name =
  List.find_map
    (fun (candidate, params) ->
      if String.equal candidate name then Some params else None)
    env.function_params

let validate_type ~context c_type =
  match c_type with
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ ->
      Ok ()
  | TReference _
  | TConstReference _ ->
      errorf
        "strict mode forbids reference type `%s` in %s"
        (c_type_to_c c_type)
        context
  | TPointer _ ->
      errorf
        "strict mode forbids pointer type `%s` in %s"
        (c_type_to_c c_type)
        context
  | TArray _ ->
      errorf
        "strict mode forbids array type `%s` in %s"
        (c_type_to_c c_type)
        context

let validate_global (global : global_def) =
  errorf
    "strict mode requires global `%s` to be initialized, but top-level initializers are unsupported"
    global.global_name

let rec validate_source_initialization_stmt fn_name = function
  | Skip | ExprStmt _ | Assign _ | Store _ | ArrayAssign _ | FieldAssign _ | Assume _
  | Assert _ | Free _ | Return _ ->
      Ok ()
  | Block stmts
  | Seq stmts ->
      validate_list (validate_source_initialization_stmt fn_name) stmts
  | LocalDecl (local, init) ->
      (match init with
      | Some _ -> Ok ()
      | None ->
          errorf
            "strict mode requires local `%s` in `%s` to be initialized"
            local.global_name
            fn_name)
  | If (_cond, then_branch, else_branch) ->
      let* () = validate_source_initialization_stmt fn_name then_branch in
      validate_source_initialization_stmt fn_name else_branch
  | While (_invariant, _cond, body) ->
      validate_source_initialization_stmt fn_name body

let validate_source_initialization_function (fn : function_def) =
  validate_source_initialization_stmt fn.name fn.body

let validate_source_program (program : program) =
  let* () = validate_list validate_global program.globals in
  let* () = validate_list validate_source_initialization_function program.functions in
  validate_source_initialization_function program.main

let validate_field record_name (field : field_def) =
  validate_type
    ~context:
      (Printf.sprintf "field `%s.%s`" record_name field.field_name)
    field.field_type

let validate_param fn_name (param : param) =
  let context =
    match param.param_name with
    | Some name ->
        Printf.sprintf "parameter `%s` of `%s`" name fn_name
    | None ->
        Printf.sprintf "anonymous parameter of `%s`" fn_name
  in
  validate_type ~context param.param_type

let rec validate_expr env fn_name expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ ->
      Ok ()
  | AddrOf _ ->
      errorf
        "strict mode forbids address-of `&` in `%s`"
        fn_name
  | Index (base, index) ->
      let* () = validate_expr env fn_name base in
      let* () = validate_expr env fn_name index in
      errorf
        "strict mode forbids array indexing in `%s`"
        fn_name
  | Deref inner ->
      let _ = inner in
      errorf
        "strict mode forbids dereference `*` in `%s`"
        fn_name
  | Conditional (cond, then_branch, else_branch) ->
      let* () = validate_bexpr env fn_name cond in
      let* () = validate_expr env fn_name then_branch in
      validate_expr env fn_name else_branch
  | Field (Deref _, _) ->
      errorf
        "strict mode forbids pointer field access `->` in `%s`"
        fn_name
  | Field (base, _) ->
      validate_expr env fn_name base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      let* () = validate_expr env fn_name left in
      validate_expr env fn_name right
  | FuncCall (name, args) ->
      let validate_args =
        match lookup_function_params env name with
        | Some param_types ->
            let rec loop param_types args =
              match param_types, args with
              | _ :: rest_params, arg :: rest_args ->
                  let* () = validate_expr env fn_name arg in
                  loop rest_params rest_args
              | [], [] ->
                  Ok ()
              | _, _ ->
                  validate_list (validate_expr env fn_name) args
            in
            loop param_types args
        | None ->
            validate_list (validate_expr env fn_name) args
      in
      let* () = validate_args in
      (match parse_method_call_name name with
      | Some (Method_arrow, method_name) ->
          errorf
            "strict mode forbids pointer method call `->%s(...)` in `%s`"
            method_name
            fn_name
      | Some (Method_dot, _) | None ->
          Ok ())

and validate_bexpr env fn_name bexpr =
  match bexpr with
  | True | False -> Ok ()
  | Forall (bindings, body) ->
      let* () =
        validate_list
          (fun (binding : quantified_var) ->
            validate_type
              ~context:
                (Printf.sprintf
                   "quantified variable `%s` in `%s`"
              binding.quant_name
                   fn_name)
              binding.quant_type)
          bindings
      in
      validate_bexpr env fn_name body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      let* () = validate_expr env fn_name left in
      validate_expr env fn_name right
  | Not inner ->
      validate_bexpr env fn_name inner
  | And (left, right)
  | Or (left, right) ->
      let* () = validate_bexpr env fn_name left in
      validate_bexpr env fn_name right

and validate_stmt env fn_name stmt =
  match stmt with
  | Skip -> Ok ()
  | Block stmts
  | Seq stmts ->
      validate_list (validate_stmt env fn_name) stmts
  | LocalDecl (local, init) ->
      let* () =
        validate_type
          ~context:
            (Printf.sprintf "local `%s` in `%s`" local.global_name fn_name)
          local.global_type
      in
      (match init with
      | None ->
          errorf
            "strict mode requires local `%s` in `%s` to be initialized"
            local.global_name
            fn_name
      | Some expr ->
          validate_expr env fn_name expr)
  | ExprStmt expr ->
      validate_expr env fn_name expr
  | Assign (_, expr) ->
      validate_expr env fn_name expr
  | Store _ ->
      errorf
        "strict mode forbids pointer store `*p = ...` in `%s`"
        fn_name
  | ArrayAssign _ ->
      errorf
        "strict mode forbids array assignment in `%s`"
        fn_name
  | FieldAssign (Deref _, _, _) ->
      errorf
        "strict mode forbids pointer field assignment `->` in `%s`"
        fn_name
  | FieldAssign (base, _, value) ->
      let* () = validate_expr env fn_name base in
      validate_expr env fn_name value
  | If (cond, then_branch, else_branch) ->
      let* () = validate_bexpr env fn_name cond in
      let* () = validate_stmt env fn_name then_branch in
      validate_stmt env fn_name else_branch
  | While (invariant, cond, body) ->
      let* () = validate_list (validate_bexpr env fn_name) (Option.to_list invariant) in
      let* () = validate_bexpr env fn_name cond in
      validate_stmt env fn_name body
  | Assume cond
  | Assert (_, cond) ->
      validate_bexpr env fn_name cond
  | Free _ ->
      errorf
        "strict mode forbids `free` in `%s`"
        fn_name
  | Return None ->
      Ok ()
  | Return (Some expr) ->
      validate_expr env fn_name expr

let validate_function env (fn : function_def) =
  let* () =
    validate_type
      ~context:(Printf.sprintf "return type of `%s`" fn.name)
      fn.return_type
  in
  let* () = validate_list (validate_param fn.name) fn.params in
  let* () =
    validate_list
      (fun local ->
        validate_type
          ~context:
            (Printf.sprintf "local `%s` in `%s`" local.global_name fn.name)
          local.global_type)
      fn.locals
  in
  validate_stmt env fn.name fn.body

let validate_import (imported : imported_function) =
  let* () =
    validate_type
      ~context:(Printf.sprintf "return type of imported function `%s`" imported.name)
      imported.return_type
  in
  validate_list (validate_param imported.name) imported.params

let validate_header_import (header : header_import) =
  validate_list validate_import header.functions

let validate_program (program : program) =
  let env = build_env program in
  let user_imports =
    List.filter (fun (header : header_import) -> header.include_path <> "") program.imports
  in
  let* () = validate_list validate_header_import user_imports in
  let* () =
    validate_list
      (fun (record : record_def) ->
        validate_list (validate_field record.record_name) record.fields)
      program.records
  in
  let* () = validate_list validate_global program.globals in
  let* () = validate_list (validate_function env) program.functions in
  validate_function env program.main
