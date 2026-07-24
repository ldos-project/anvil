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

let validate_type ~context c_type =
  match c_type with
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ ->
      Ok ()
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
  | TReference _ ->
      errorf
        "strict mode forbids reference type `%s` in %s"
        (c_type_to_c c_type)
        context
  | TConstReference _ ->
      errorf
        "strict mode forbids const-reference type `%s` in %s"
        (c_type_to_c c_type)
        context

let validate_global (global : global_def) =
  errorf
    "strict mode requires global `%s` to be initialized, but top-level initializers are unsupported"
    global.global_name

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

let rec validate_expr fn_name expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ ->
      Ok ()
  | AddrOf inner ->
      let _ = inner in
      errorf
        "strict mode forbids address-of `&` in `%s`"
        fn_name
  | Index (base, index) ->
      let* () = validate_expr fn_name base in
      let* () = validate_expr fn_name index in
      errorf
        "strict mode forbids array indexing in `%s`"
        fn_name
  | Deref inner ->
      let _ = inner in
      errorf
        "strict mode forbids dereference `*` in `%s`"
        fn_name
  | Field (Deref _, _) ->
      errorf
        "strict mode forbids pointer field access `->` in `%s`"
        fn_name
  | Field (base, _) ->
      validate_expr fn_name base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      let* () = validate_expr fn_name left in
      validate_expr fn_name right
  | FuncCall (name, args) ->
      let* () = validate_list (validate_expr fn_name) args in
      (match parse_method_call_name name with
      | Some (Method_arrow, method_name) ->
          errorf
            "strict mode forbids pointer method call `->%s(...)` in `%s`"
            method_name
            fn_name
      | Some (Method_dot, _) | None ->
          Ok ())

and validate_bexpr fn_name bexpr =
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
      validate_bexpr fn_name body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      let* () = validate_expr fn_name left in
      validate_expr fn_name right
  | Not inner ->
      validate_bexpr fn_name inner
  | And (left, right)
  | Or (left, right) ->
      let* () = validate_bexpr fn_name left in
      validate_bexpr fn_name right

and validate_stmt fn_name stmt =
  match stmt with
  | Skip | Break | Continue -> Ok ()
  | Block stmts
  | Seq stmts ->
      validate_list (validate_stmt fn_name) stmts
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
          validate_expr fn_name expr)
  | Assign (_, expr) ->
      validate_expr fn_name expr
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
      let* () = validate_expr fn_name base in
      validate_expr fn_name value
  | If (cond, then_branch, else_branch) ->
      let* () = validate_bexpr fn_name cond in
      let* () = validate_stmt fn_name then_branch in
      validate_stmt fn_name else_branch
  | While (invariant, cond, body) ->
      let* () = validate_list (validate_bexpr fn_name) (Option.to_list invariant) in
      let* () = validate_bexpr fn_name cond in
      validate_stmt fn_name body
  | Assume cond
  | Assert (_, cond) ->
      validate_bexpr fn_name cond
  | Free _ ->
      errorf
        "strict mode forbids `free` in `%s`"
        fn_name
  | Return None ->
      Ok ()
  | Return (Some expr) ->
      validate_expr fn_name expr

let validate_function (fn : function_def) =
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
  validate_stmt fn.name fn.body

let validate_import (imported : imported_function) =
  let* () =
    validate_type
      ~context:(Printf.sprintf "return type of imported function `%s`" imported.name)
      imported.return_type
  in
  validate_list (validate_param imported.name) imported.params

let validate_header_import (header : header_import) =
  validate_list validate_import header.functions

(* With loops restricted to counted `for`s, an acyclic call graph is what is
   left to rule out non-termination. Only functions defined in the program can
   form a cycle, so unresolved callees (externs, `__anvil_*` intrinsics) are
   skipped. *)

let rec calls_in_expr acc expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ -> acc
  | AddrOf inner | Deref inner | Field (inner, _) -> calls_in_expr acc inner
  | Index (left, right)
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      calls_in_expr (calls_in_expr acc left) right
  | FuncCall (name, args) -> List.fold_left calls_in_expr (name :: acc) args

and calls_in_bexpr acc bexpr =
  match bexpr with
  | True | False -> acc
  | Forall (_, body) | Not body -> calls_in_bexpr acc body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      calls_in_expr (calls_in_expr acc left) right
  | And (left, right) | Or (left, right) ->
      calls_in_bexpr (calls_in_bexpr acc left) right

and calls_in_stmt acc stmt =
  match stmt with
  | Skip | Break | Continue -> acc
  | Block stmts | Seq stmts -> List.fold_left calls_in_stmt acc stmts
  | LocalDecl (_, None) | Return None -> acc
  | LocalDecl (_, Some expr) | Assign (_, expr) | Free expr | Return (Some expr)
    ->
      calls_in_expr acc expr
  | Store (left, right) | FieldAssign (left, _, right) ->
      calls_in_expr (calls_in_expr acc left) right
  | ArrayAssign (base, index, value) ->
      calls_in_expr (calls_in_expr (calls_in_expr acc base) index) value
  | If (cond, then_branch, else_branch) ->
      calls_in_stmt (calls_in_stmt (calls_in_bexpr acc cond) then_branch)
        else_branch
  | While (invariant, cond, body) ->
      let acc =
        match invariant with
        | None -> acc
        | Some invariant -> calls_in_bexpr acc invariant
      in
      calls_in_stmt (calls_in_bexpr acc cond) body
  | Assume cond | Assert (_, cond) -> calls_in_bexpr acc cond

(* `break`/`continue` outside a loop is not valid C++, and the evolve grammar
   admits them in any statement position, so the loop context is checked here
   instead. Inside a counted `for` both are inert for termination: `break`
   only exits sooner, and `continue` still runs the step. *)
let validate_loop_control (program : program) =
  let rec walk ~in_loop stmt =
    match stmt with
    | Break -> if in_loop then Ok () else errorf "`break` outside a loop"
    | Continue -> if in_loop then Ok () else errorf "`continue` outside a loop"
    | Block stmts | Seq stmts -> validate_list (walk ~in_loop) stmts
    | If (_, then_branch, else_branch) ->
        let* () = walk ~in_loop then_branch in
        walk ~in_loop else_branch
    | While (_, _, body) -> walk ~in_loop:true body
    | Skip | LocalDecl _ | Assign _ | Store _ | ArrayAssign _ | FieldAssign _
    | Assume _ | Assert _ | Free _ | Return _ ->
        Ok ()
  in
  validate_list
    (fun fn -> walk ~in_loop:false fn.body)
    (program.main :: program.functions)

let validate_no_recursion (program : program) =
  let defined = program.main :: program.functions in
  let callees_of fn =
    let names = calls_in_stmt [] fn.body in
    List.filter
      (fun name -> List.exists (fun f -> String.equal f.name name) defined)
      names
  in
  let body_of name =
    List.find_opt (fun f -> String.equal f.name name) defined
  in
  (* Depth-first search for a back edge. `visiting` is the current call chain;
     `acyclic` memoises names already proven to reach no cycle. Without the
     memo a branching call graph is re-walked once per path, so a candidate
     with a few dozen fanning-out helpers takes exponential time to gate. *)
  let acyclic = ref [] in
  let rec walk visiting name =
    if List.exists (String.equal name) visiting then
      errorf "evolve blocks forbid recursion: `%s` is reachable from itself (%s)"
        name
        (String.concat " -> " (List.rev (name :: visiting)))
    else if List.exists (String.equal name) !acyclic then Ok ()
    else
      match body_of name with
      | None -> Ok ()
      | Some fn ->
          let* () = validate_list (walk (name :: visiting)) (callees_of fn) in
          acyclic := name :: !acyclic;
          Ok ()
  in
  validate_list (fun fn -> walk [] fn.name) defined

let validate_program (program : program) =
  let* () = validate_list validate_header_import program.imports in
  let* () =
    validate_list
      (fun (record : record_def) ->
        validate_list (validate_field record.record_name) record.fields)
      program.records
  in
  let* () = validate_list validate_global program.globals in
  let* () = validate_list validate_function program.functions in
  validate_function program.main
