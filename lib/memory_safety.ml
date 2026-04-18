open Ast

let fail fmt = Printf.ksprintf (fun msg -> Error msg) fmt

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

let seq_of_list = function
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

let mk_and = function
  | [] -> True
  | [formula] -> formula
  | formula :: rest ->
      List.fold_left (fun acc next -> And (acc, next)) formula rest

let mk_or = function
  | [] -> False
  | [formula] -> formula
  | formula :: rest ->
      List.fold_left (fun acc next -> Or (acc, next)) formula rest

let int_eq left right = Eq (left, right)

let int_ge left right = Ge (left, right)

let int_le left right = Le (left, right)

let int_lt left right = Lt (left, right)

let assoc_opt key bindings =
  List.find_map
    (fun (name, value) ->
      if String.equal name key then Some value else None)
    bindings

let scalar_byte_size = function
  | TInt -> 4
  | TFloat -> 4
  | TDouble -> 8
  | TChar -> 1
  | TBool -> 1
  | TVoid -> failwith "void has no byte size"
  | TRecord _ -> failwith "record is not a scalar byte-sized type"
  | TPointer _ -> failwith "pointer byte size is not modeled directly"
  | TArray _ -> failwith "array is not a scalar byte-sized type"
  | TReference _ | TConstReference _ ->
      failwith "reference types should be lowered before byte-size queries"

let scalar_byte_size_expr c_type =
  Int (scalar_byte_size c_type)

let object_byte_size records c_type =
  c_type_object_byte_size records c_type

let object_byte_size_expr records c_type =
  Int (object_byte_size records c_type)

let add_expr left right =
  match left, right with
  | Int 0, expr
  | expr, Int 0 ->
      expr
  | Int left, Int right ->
      Int (left + right)
  | _ ->
      Add (left, right)

let sub_expr left right =
  match left, right with
  | expr, Int 0 ->
      expr
  | Int left, Int right ->
      Int (left - right)
  | _ ->
      Sub (left, right)

let mul_expr left right =
  match left, right with
  | Int 0, _
  | _, Int 0 ->
      Int 0
  | Int 1, expr
  | expr, Int 1 ->
      expr
  | Int left, Int right ->
      Int (left * right)
  | _ ->
      Mul (left, right)

let ptr_block_name name = "__anvil_ptr_block_" ^ name

let ptr_offset_name name = "__anvil_ptr_offset_" ^ name

let alloc_live_name site = "__anvil_alloc_live_" ^ string_of_int site

let alloc_size_name site = "__anvil_alloc_size_" ^ string_of_int site

let memory_sink_name = "__anvil_memory_sink"

let heap_ok_name = "__anvil_heap_ok"

let ghost_heap_predicates =
  [ "heap_ok"
  ; "valid_read"
  ; "valid_write"
  ; "allocated"
  ; "live"
  ; "can_free"
  ; "same_block"
  ; "is_null"
  ]

let rec count_malloc_expr = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ ->
      0
  | AddrOf inner -> count_malloc_expr inner
  | Index (base, index) ->
      count_malloc_expr base + count_malloc_expr index
  | Deref inner -> count_malloc_expr inner
  | Field (base, _) -> count_malloc_expr base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      count_malloc_expr left + count_malloc_expr right
  | FuncCall (name, args) ->
      let here =
        if String.equal name "malloc" then 1 else 0
      in
      here + List.fold_left (fun acc arg -> acc + count_malloc_expr arg) 0 args

let rec uses_memory_expr = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ -> false
  | AddrOf _ | Index _ | Deref _ | Field _ -> true
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      uses_memory_expr left || uses_memory_expr right
  | FuncCall (name, args) ->
      String.equal name "malloc" || List.exists uses_memory_expr args

let rec count_malloc_bexpr = function
  | True | False -> 0
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      count_malloc_expr left + count_malloc_expr right
  | Not inner -> count_malloc_bexpr inner
  | And (left, right)
  | Or (left, right) ->
      count_malloc_bexpr left + count_malloc_bexpr right

let rec count_malloc_stmt = function
  | Skip -> 0
  | Block stmts ->
      List.fold_left (fun acc stmt -> acc + count_malloc_stmt stmt) 0 stmts
  | LocalDecl (_, init) ->
      (match init with
      | None -> 0
      | Some expr -> count_malloc_expr expr)
  | Assign (_, expr) -> count_malloc_expr expr
  | Store (ptr, value) -> count_malloc_expr ptr + count_malloc_expr value
  | ArrayAssign (base, index, value) ->
      count_malloc_expr base + count_malloc_expr index + count_malloc_expr value
  | FieldAssign (base, _, value) ->
      count_malloc_expr base + count_malloc_expr value
  | Seq stmts ->
      List.fold_left (fun acc stmt -> acc + count_malloc_stmt stmt) 0 stmts
  | If (cond, then_branch, else_branch) ->
      count_malloc_bexpr cond
      + count_malloc_stmt then_branch
      + count_malloc_stmt else_branch
  | While (invariant, cond, body) ->
      let invariant =
        match invariant with
        | None -> 0
        | Some invariant -> count_malloc_bexpr invariant
      in
      invariant + count_malloc_bexpr cond + count_malloc_stmt body
  | Assume cond
  | Assert (_, cond) ->
      count_malloc_bexpr cond
  | Free ptr -> count_malloc_expr ptr
  | Return None -> 0
  | Return (Some value) -> count_malloc_expr value

let rec uses_memory_stmt = function
  | Skip -> false
  | Block stmts ->
      List.exists uses_memory_stmt stmts
  | LocalDecl (_, init) ->
      (match init with
      | None -> false
      | Some expr -> uses_memory_expr expr)
  | Assign (_, expr) -> uses_memory_expr expr
  | Store _ | ArrayAssign _ | FieldAssign _ | Free _ -> true
  | Seq stmts -> List.exists uses_memory_stmt stmts
  | If (cond, then_branch, else_branch) ->
      uses_memory_bexpr cond
      || uses_memory_stmt then_branch
      || uses_memory_stmt else_branch
  | While (invariant, cond, body) ->
      (match invariant with
      | None -> false
      | Some invariant -> uses_memory_bexpr invariant)
      || uses_memory_bexpr cond
      || uses_memory_stmt body
  | Assume cond | Assert (_, cond) -> uses_memory_bexpr cond
  | Return None -> false
  | Return (Some value) -> uses_memory_expr value

and uses_memory_bexpr = function
  | True | False -> false
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      uses_memory_expr left || uses_memory_expr right
  | Not inner -> uses_memory_bexpr inner
  | And (left, right)
  | Or (left, right) ->
      uses_memory_bexpr left || uses_memory_bexpr right

let count_malloc_program program =
  List.fold_left
    (fun acc fn -> acc + count_malloc_stmt fn.body)
    (count_malloc_stmt program.main.body)
    program.functions

let contract_mentions_memory_predicates contract =
  List.exists
    (fun predicate ->
      List.exists
        (fun text ->
          let pattern = predicate ^ "(" in
          let text = String.trim text in
          String.contains_from text 0 pattern.[0]
          && (
            let rec loop i =
              if i + String.length pattern > String.length text then false
              else if String.sub text i (String.length pattern) = pattern then true
              else loop (i + 1)
            in
            loop 0))
        [ contract.require; contract.guarantee; contract.safety ])
    ghost_heap_predicates

let function_mentions_memory_contract fn =
  match fn.contract with
  | None -> false
  | Some contract -> contract_mentions_memory_predicates contract

let imported_function_mentions_memory_contract (fn : contracted_function) =
  contract_mentions_memory_predicates fn.contract

type reference_binding = {
  inner_type : c_type;
  is_const : bool;
}

type reference_lower_env = {
  reference_bindings : (var * reference_binding) list;
  function_params : (func_name * c_type list) list;
}

let supported_reference_inner_type = function
  | TInt | TFloat | TDouble | TChar | TBool | TRecord _ -> true
  | TVoid | TPointer _ | TArray _ | TReference _ | TConstReference _ -> false

let lower_reference_param_type = function
  | TReference inner | TConstReference inner ->
      if supported_reference_inner_type inner then
        Ok (TPointer inner)
      else
        fail
          "unsupported reference type `%s`; only scalar and record references are supported"
          (c_type_to_c (TReference inner))
  | c_type ->
      Ok c_type

let lower_reference_param (param : param) =
  let* param_type = lower_reference_param_type param.param_type in
  Ok { param with param_type }

let reference_binding_of_param (param : param) =
  match param.param_type, param.param_name with
  | TReference inner, Some name ->
      Some (name, { inner_type = inner; is_const = false })
  | TConstReference inner, Some name ->
      Some (name, { inner_type = inner; is_const = true })
  | (TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _ | TArray _), _
    ->
      None
  | (TReference _ | TConstReference _), None ->
      None

let build_reference_function_params (program : program) =
  let imported =
    List.concat_map
      (fun (header : header_import) -> header.functions)
      program.imports
    |> List.map (fun (fn : contracted_function) ->
           fn.name, List.map (fun param -> param.param_type) fn.params)
  in
  let locals =
    List.map
      (fun (fn : function_def) ->
        fn.name, List.map (fun param -> param.param_type) fn.params)
      (program.functions @ [ program.main ])
  in
  imported @ locals

let lookup_reference_binding env name =
  assoc_opt name env.reference_bindings

let lookup_reference_function_params env name =
  assoc_opt name env.function_params

let is_reference_var env name =
  Option.is_some (lookup_reference_binding env name)

let is_const_reference_var env name =
  match lookup_reference_binding env name with
  | Some binding -> binding.is_const
  | None -> false

let expr_is_addressable = function
  | Var _ | Field _ | Index _ | Deref _ -> true
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | AddrOf _ | Add _ | Sub _
  | Mul _ | Div _ | Mod _ | FuncCall _ ->
      false

let rec direct_const_reference_lvalue env = function
  | Var name -> is_const_reference_var env name
  | Field (base, _) -> direct_const_reference_lvalue env base
  | Index (base, _) -> direct_const_reference_lvalue env base
  | Deref _ -> false
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | AddrOf _ | Add _ | Sub _
  | Mul _ | Div _ | Mod _ | FuncCall _ ->
      false

let rec lower_reference_addressable_expr env = function
  | Var name when is_reference_var env name ->
      Ok (Deref (Var name))
  | Var name ->
      Ok (Var name)
  | Field (base, field) ->
      let* base = lower_reference_expr env base in
      Ok (Field (base, field))
  | Index (base, index) ->
      let* base = lower_reference_expr env base in
      let* index = lower_reference_expr env index in
      Ok (Index (base, index))
  | Deref expr ->
      let* expr = lower_reference_expr env expr in
      Ok (Deref expr)
  | expr ->
      fail "non-addressable expression `%s` cannot be bound to a reference" (expr_to_c expr)

and lower_reference_arg env param_type arg =
  match param_type with
  | TReference inner ->
      if direct_const_reference_lvalue env arg then
        fail
          "cannot bind mutable reference `%s` to const reference expression `%s`"
          (c_type_to_c (TReference inner))
          (expr_to_c arg)
      else
        lower_reference_binding_arg env arg
  | TConstReference _ ->
      lower_reference_binding_arg env arg
  | _ ->
      lower_reference_expr env arg

and lower_reference_binding_arg env arg =
  match arg with
  | Var name when is_reference_var env name ->
      Ok (Var name)
  | _ when expr_is_addressable arg ->
      let* arg = lower_reference_addressable_expr env arg in
      Ok (AddrOf arg)
  | _ ->
      fail
        "reference arguments must be addressable lvalues; temporary `%s` is unsupported"
        (expr_to_c arg)

and lower_reference_call env name args =
  match lookup_reference_function_params env name with
  | None ->
      let* args = lower_reference_expr_list env args in
      Ok (FuncCall (name, args))
  | Some param_types ->
      let rec loop param_types args =
        match param_types, args with
        | [], [] ->
            Ok []
        | param_type :: rest_params, arg :: rest_args ->
            let* arg = lower_reference_arg env param_type arg in
            let* rest = loop rest_params rest_args in
            Ok (arg :: rest)
        | _, _ ->
            fail "arity mismatch while lowering references for `%s`" name
      in
      let* args = loop param_types args in
      Ok (FuncCall (name, args))

and lower_reference_expr env = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr ->
      Ok expr
  | Var name when is_reference_var env name ->
      Ok (Deref (Var name))
  | Var name ->
      Ok (Var name)
  | AddrOf (Var name) when is_reference_var env name ->
      Ok (Var name)
  | AddrOf expr ->
      let* expr = lower_reference_addressable_expr env expr in
      Ok (AddrOf expr)
  | Index (base, index) ->
      let* base = lower_reference_expr env base in
      let* index = lower_reference_expr env index in
      Ok (Index (base, index))
  | Deref expr ->
      let* expr = lower_reference_expr env expr in
      Ok (Deref expr)
  | Field (base, field) ->
      let* base = lower_reference_expr env base in
      Ok (Field (base, field))
  | Add (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Add (left, right))
  | Sub (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Sub (left, right))
  | Mul (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Mul (left, right))
  | Div (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Div (left, right))
  | Mod (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Mod (left, right))
  | FuncCall (name, args) ->
      lower_reference_call env name args

and lower_reference_expr_list env = function
  | [] -> Ok []
  | expr :: rest ->
      let* expr = lower_reference_expr env expr in
      let* rest = lower_reference_expr_list env rest in
      Ok (expr :: rest)

let rec lower_reference_bexpr env = function
  | True -> Ok True
  | False -> Ok False
  | Eq (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Eq (left, right))
  | Neq (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Neq (left, right))
  | Lt (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Lt (left, right))
  | Le (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Le (left, right))
  | Gt (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Gt (left, right))
  | Ge (left, right) ->
      let* left = lower_reference_expr env left in
      let* right = lower_reference_expr env right in
      Ok (Ge (left, right))
  | Not inner ->
      let* inner = lower_reference_bexpr env inner in
      Ok (Not inner)
  | And (left, right) ->
      let* left = lower_reference_bexpr env left in
      let* right = lower_reference_bexpr env right in
      Ok (And (left, right))
  | Or (left, right) ->
      let* left = lower_reference_bexpr env left in
      let* right = lower_reference_bexpr env right in
      Ok (Or (left, right))

let rec lower_reference_stmt env = function
  | Skip -> Ok Skip
  | Block _ | LocalDecl _ ->
      fail "unresolved local syntax reached reference lowering"
  | Assign (name, rhs) ->
      let* rhs = lower_reference_expr env rhs in
      (match lookup_reference_binding env name with
      | Some { is_const = true; _ } ->
          fail "cannot assign through const reference `%s`" name
      | Some _ ->
          Ok (Store (Var name, rhs))
      | None ->
          Ok (Assign (name, rhs)))
  | Store (ptr, value) ->
      let* ptr = lower_reference_expr env ptr in
      let* value = lower_reference_expr env value in
      Ok (Store (ptr, value))
  | ArrayAssign (base, index, value) ->
      let* base = lower_reference_expr env base in
      let* index = lower_reference_expr env index in
      let* value = lower_reference_expr env value in
      Ok (ArrayAssign (base, index, value))
  | FieldAssign (base, field, value) ->
      if direct_const_reference_lvalue env base then
        fail "cannot assign field `%s` through a const reference" field
      else
        let* base = lower_reference_expr env base in
        let* value = lower_reference_expr env value in
        Ok (FieldAssign (base, field, value))
  | Seq stmts ->
      let* stmts = lower_reference_stmt_list env stmts in
      Ok (Seq stmts)
  | If (cond, then_branch, else_branch) ->
      let* cond = lower_reference_bexpr env cond in
      let* then_branch = lower_reference_stmt env then_branch in
      let* else_branch = lower_reference_stmt env else_branch in
      Ok (If (cond, then_branch, else_branch))
  | While (invariant, cond, body) ->
      let* invariant =
        match invariant with
        | None -> Ok None
        | Some invariant ->
            let* invariant = lower_reference_bexpr env invariant in
            Ok (Some invariant)
      in
      let* cond = lower_reference_bexpr env cond in
      let* body = lower_reference_stmt env body in
      Ok (While (invariant, cond, body))
  | Assume cond ->
      let* cond = lower_reference_bexpr env cond in
      Ok (Assume cond)
  | Assert (origin, cond) ->
      let* cond = lower_reference_bexpr env cond in
      Ok (Assert (origin, cond))
  | Free ptr ->
      let* ptr = lower_reference_expr env ptr in
      Ok (Free ptr)
  | Return value ->
      let* value =
        match value with
        | None -> Ok None
        | Some value ->
            let* value = lower_reference_expr env value in
            Ok (Some value)
      in
      Ok (Return value)

and lower_reference_stmt_list env = function
  | [] -> Ok []
  | stmt :: rest ->
      let* stmt = lower_reference_stmt env stmt in
      let* rest = lower_reference_stmt_list env rest in
      Ok (stmt :: rest)

let lower_reference_function_params params =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | param :: rest ->
        let* param = lower_reference_param param in
        loop (param :: acc) rest
  in
  loop [] params

let lower_reference_function function_params (fn : function_def) =
  if is_reference_type fn.return_type then
    fail "reference return type in function `%s` is unsupported" fn.name
  else
    let env =
      {
        reference_bindings = List.filter_map reference_binding_of_param fn.params;
        function_params;
      }
    in
    let* params = lower_reference_function_params fn.params in
    let* body = lower_reference_stmt env fn.body in
    Ok { fn with params; body }

let lower_reference_imported_function (fn : contracted_function) =
  if is_reference_type fn.return_type then
    fail "reference return type in imported function `%s` is unsupported" fn.name
  else
    let* params = lower_reference_function_params fn.params in
    Ok { fn with params }

let lower_reference_imports imports =
  let rec loop_headers acc = function
    | [] -> Ok (List.rev acc)
    | (header : header_import) :: rest ->
        let rec loop_functions (functions_acc : imported_function list) = function
          | [] ->
              loop_headers
                ({ header with functions = List.rev functions_acc } :: acc)
                rest
          | (fn : imported_function) :: tail ->
              let* fn = lower_reference_imported_function fn in
              loop_functions (fn :: functions_acc) tail
        in
        loop_functions [] header.functions
  in
  loop_headers [] imports

let lower_references_program (program : program) =
  let function_params = build_reference_function_params program in
  let* imports = lower_reference_imports program.imports in
  let rec loop_functions acc = function
    | [] -> Ok (List.rev acc)
    | fn :: rest ->
        let* fn = lower_reference_function function_params fn in
        loop_functions (fn :: acc) rest
  in
  let* functions = loop_functions [] program.functions in
  let* main = lower_reference_function function_params program.main in
  Ok { program with imports; functions; main }

let locals_need_memory locals =
  List.exists
    (fun local ->
      is_pointer_type local.global_type || is_array_type local.global_type)
    locals

let uses_memory_program program =
  pointer_globals program.globals <> []
  || List.exists (fun global -> is_array_type global.global_type) program.globals
  || List.exists (fun fn -> locals_need_memory fn.locals) (program.main :: program.functions)
  || List.exists uses_memory_stmt (program.main.body :: List.map (fun fn -> fn.body) program.functions)
  || List.exists function_mentions_memory_contract (program.main :: program.functions)
  || List.exists
       (fun (imported_header : header_import) ->
         List.exists imported_function_mentions_memory_contract imported_header.functions)
       program.imports

type expr_kind =
  | Scalar_kind
  | Pointer_kind of c_type

type env = {
  records : record_def list;
  scalar_globals : global_def list;
  pointer_globals : (var * c_type) list;
  function_sigs : (string * (c_type list * c_type)) list;
  malloc_sites : int;
}

type contract_env = env

type concrete_pointer = {
  block_id : int;
  offset : int;
  pointee : c_type option;
}

type shadow_location = {
  block_id : int;
  offset : int;
}

type shadow_cell =
  | Shadow_scalar of {
      location : shadow_location;
      c_type : c_type;
      value : expr;
    }
  | Shadow_pointer of {
      location : shadow_location;
      pointee : c_type;
      value : concrete_pointer;
    }

type lower_state = {
  next_malloc_site : int;
  next_shadow_temp : int;
  temp_globals_rev : global_def list;
  shadow_cells : shadow_cell list;
  known_pointers : (var * concrete_pointer) list;
}

let shadow_value_temp_prefix = "__anvil_shadow_value_"

let shadow_value_temp_name id =
  shadow_value_temp_prefix ^ string_of_int id

let is_shadow_value_temp name =
  String.length name >= String.length shadow_value_temp_prefix
  && String.sub name 0 (String.length shadow_value_temp_prefix)
     = shadow_value_temp_prefix

let rec expr_is_stable = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ ->
      true
  | Var name ->
      is_shadow_value_temp name
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      expr_is_stable left && expr_is_stable right
  | AddrOf _ | Index _ | Deref _ | Field _ | FuncCall _ ->
      false

let extract_int = function
  | Int value -> Some value
  | _ -> None

let clear_shadow_cells state =
  { state with shadow_cells = [] }

let clear_semantic_state state =
  { state with shadow_cells = []; known_pointers = [] }

let replace_assoc key value bindings =
  (key, value)
  :: List.filter (fun (name, _) -> not (String.equal name key)) bindings

let lookup_known_pointer state name =
  assoc_opt name state.known_pointers

let remember_known_pointer state name pointer =
  { state with known_pointers = replace_assoc name pointer state.known_pointers }

let forget_known_pointer state name =
  {
    state with
    known_pointers =
      List.filter (fun (current, _) -> not (String.equal current name)) state.known_pointers;
  }

let shadow_location_equal (left : shadow_location) (right : shadow_location) =
  left.block_id = right.block_id && left.offset = right.offset

let shadow_cell_location = function
  | Shadow_scalar { location; _ }
  | Shadow_pointer { location; _ } ->
      location

let remove_shadow_location cells location =
  List.filter
    (fun cell -> not (shadow_location_equal (shadow_cell_location cell) location))
    cells

let update_shadow_scalar state location c_type value =
  {
    state with
    shadow_cells =
      Shadow_scalar { location; c_type; value }
      :: remove_shadow_location state.shadow_cells location;
  }

let update_shadow_pointer state location pointee value =
  {
    state with
    shadow_cells =
      Shadow_pointer { location; pointee; value }
      :: remove_shadow_location state.shadow_cells location;
  }

let forget_shadow_location state location =
  { state with shadow_cells = remove_shadow_location state.shadow_cells location }

let lookup_shadow_scalar state location c_type =
  List.find_map
    (function
      | Shadow_scalar { location = current; c_type = current_type; value }
        when shadow_location_equal current location && current_type = c_type ->
          Some value
      | _ ->
          None)
    state.shadow_cells

let lookup_shadow_pointer state location pointee =
  List.find_map
    (function
      | Shadow_pointer { location = current; pointee = current_pointee; value }
        when shadow_location_equal current location && current_pointee = pointee ->
          Some value
      | _ ->
          None)
    state.shadow_cells

let merge_pointer_facts left right =
  List.filter_map
    (fun (name, pointer) ->
      match assoc_opt name right with
      | Some right_pointer when right_pointer = pointer ->
          Some (name, pointer)
      | Some _ | None ->
          None)
    left

let merge_shadow_cells left right =
  List.filter (fun cell -> List.mem cell right) left

let merge_semantic_state state left right =
  {
    state with
    shadow_cells = merge_shadow_cells left.shadow_cells right.shadow_cells;
    known_pointers = merge_pointer_facts left.known_pointers right.known_pointers;
  }

let fresh_shadow_temp state c_type =
  let name = shadow_value_temp_name state.next_shadow_temp in
  let state =
    {
      state with
      next_shadow_temp = state.next_shadow_temp + 1;
      temp_globals_rev =
        { global_type = c_type; global_name = name } :: state.temp_globals_rev;
    }
  in
  name, state

let freeze_scalar_value state c_type value =
  if expr_is_stable value then
    [], value, state
  else
    let name, state = fresh_shadow_temp state c_type in
    [ Assign (name, value) ], Var name, state

let global_block_id env name =
  let rec loop index = function
    | [] -> None
    | current :: rest ->
        if String.equal current.global_name name then Some index
        else loop (index + 1) rest
  in
  loop 1 env.scalar_globals

let alloc_block_id env site =
  List.length env.scalar_globals + site

let global_by_block_id env block_id =
  let rec loop index = function
    | [] -> None
    | global :: rest ->
        if index = block_id then Some global else loop (index + 1) rest
  in
  if block_id <= 0 then None else loop 1 env.scalar_globals

let shadowable_location env block_id offset width =
  match global_by_block_id env block_id with
  | None ->
      None
  | Some global ->
      let object_size = object_byte_size env.records global.global_type in
      if offset < 0 || offset + width > object_size then None
      else Some { block_id; offset }

let is_pointer_name env name =
  Option.is_some (assoc_opt name env.pointer_globals)

let pointer_pointee_type env name =
  assoc_opt name env.pointer_globals

let global_scalar_type env name =
  List.find_map
    (fun global ->
      if String.equal global.global_name name then Some global.global_type else None)
    env.scalar_globals

let global_decay_pointee_type env name =
  match global_scalar_type env name with
  | Some (TArray (element_type, _)) -> Some element_type
  | Some c_type -> Some c_type
  | None -> None

let param_as_global (param : param) =
  match param.param_type, param.param_name with
  | TPointer _, _ | _, None -> None
  | global_type, Some global_name ->
      Some { global_type; global_name }

let pointer_bindings_of_defs defs =
  List.filter_map
    (fun def ->
      match def.global_type with
      | TPointer inner -> Some (def.global_name, inner)
      | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TArray _
      | TReference _ | TConstReference _ ->
          None)
    defs

let pointer_bindings_of_params params =
  List.filter_map
    (fun (param : param) ->
      match param.param_type, param.param_name with
      | TPointer inner, Some name -> Some (name, inner)
      | TPointer _, None -> None
      | (TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TArray _
        | TReference _ | TConstReference _), _ ->
          None)
    params

let pointer_globals_of_program (program : program) =
  pointer_bindings_of_defs (pointer_globals program.globals)

let build_function_sigs (program : program) =
  let imported =
    List.concat_map
      (fun (header : header_import) -> header.functions)
      program.imports
    |> List.map (fun (fn : contracted_function) ->
           fn.name, (List.map (fun param -> param.param_type) fn.params, fn.return_type))
  in
  let locals =
    List.map
      (fun (fn : function_def) ->
        fn.name, (List.map (fun param -> param.param_type) fn.params, fn.return_type))
      (program.functions @ [ program.main ])
  in
  imported @ locals

let function_env_of_program (program : program) fn malloc_sites =
  {
    records = program.records;
    scalar_globals =
      scalar_globals program.globals
      @ List.filter_map param_as_global fn.params
      @ List.filter (fun local -> not (is_pointer_type local.global_type)) fn.locals;
    pointer_globals =
      pointer_globals_of_program program
      @ pointer_bindings_of_params fn.params
      @ pointer_bindings_of_defs (pointer_globals fn.locals);
    function_sigs = build_function_sigs program;
    malloc_sites;
  }

let lookup_field_type env record_name field_name =
  record_field_type env.records record_name field_name

let lookup_field_offset env record_name field_name =
  record_field_offset env.records record_name field_name

let lookup_function_sig env name =
  assoc_opt name env.function_sigs

let lower_function_params (params : param list) =
  let expand_param (param : param) =
    match param.param_type, param.param_name with
    | TPointer _, None ->
        failwith "pointer parameters must be named after class desugaring"
    | TPointer _, Some name ->
        [ { param_type = TInt; param_name = Some (ptr_block_name name) }
        ; { param_type = TInt; param_name = Some (ptr_offset_name name) }
        ]
    | (TReference _ | TConstReference _), _ ->
        failwith "reference parameters should be lowered before memory lowering"
    | _, _ ->
        [ param ]
  in
  List.concat_map expand_param params

let rec expr_kind env = function
  | Int _
  | FloatLit _
  | DoubleLit _
  | CharLit _
  | BoolLit _ ->
      Scalar_kind
  | Var name ->
      (match pointer_pointee_type env name with
      | Some pointee -> Pointer_kind pointee
      | None ->
          (match global_scalar_type env name with
          | Some (TArray (element_type, _)) -> Pointer_kind element_type
          | Some _ | None -> Scalar_kind))
  | AddrOf expr ->
      (match expr with
      | Var name ->
          (match global_decay_pointee_type env name with
          | Some pointee -> Pointer_kind pointee
          | None -> Scalar_kind)
      | Index (base, _) ->
          (match expr_kind env base with
          | Pointer_kind pointee -> Pointer_kind pointee
          | Scalar_kind -> Scalar_kind)
      | Field (base, field) ->
          (match record_receiver_type env base with
          | Some record_name ->
              (match lookup_field_type env record_name field with
              | Some field_type -> Pointer_kind field_type
              | None -> Scalar_kind)
          | None -> Scalar_kind)
      | Deref ptr ->
          (match expr_kind env ptr with
          | Pointer_kind pointee -> Pointer_kind pointee
          | Scalar_kind -> Scalar_kind)
      | _ -> Scalar_kind)
  | Index _ as expr ->
      (match addressable_type env expr with
      | Some (TPointer pointee) -> Pointer_kind pointee
      | Some (TArray (element_type, _)) -> Pointer_kind element_type
      | Some _ | None -> Scalar_kind)
  | Deref _ as expr ->
      (match addressable_type env expr with
      | Some (TPointer pointee) -> Pointer_kind pointee
      | Some _ | None -> Scalar_kind)
  | Field (base, field) ->
      (match record_receiver_type env base with
      | Some record_name ->
          (match lookup_field_type env record_name field with
          | Some (TPointer pointee) -> Pointer_kind pointee
          | Some (TArray (element_type, _)) -> Pointer_kind element_type
          | Some _ | None -> Scalar_kind)
      | None -> Scalar_kind)
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind pointee, Scalar_kind
      | Scalar_kind, Pointer_kind pointee ->
          Pointer_kind pointee
      | Scalar_kind, Scalar_kind -> Scalar_kind
      | Pointer_kind _, Pointer_kind _ -> Scalar_kind)
  | Sub _ | Mul _ | Div _ | Mod _ -> Scalar_kind
  | FuncCall (name, args) ->
      if String.equal name "malloc" && List.length args = 1 then
        Pointer_kind TInt
      else
        Scalar_kind

and addressable_type env = function
  | Var name ->
      (match pointer_pointee_type env name with
      | Some pointee -> Some (TPointer pointee)
      | None -> global_scalar_type env name)
  | Field (base, field) ->
      (match record_receiver_type env base with
      | Some record_name -> lookup_field_type env record_name field
      | None -> None)
  | Index (base, _) ->
      (match expr_kind env base with
      | Pointer_kind pointee -> Some pointee
      | Scalar_kind -> None)
  | Deref ptr ->
      (match expr_kind env ptr with
      | Pointer_kind pointee -> Some pointee
      | Scalar_kind -> None)
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

and record_receiver_type env expr =
  match addressable_type env expr with
  | Some (TRecord record_name) -> Some record_name
  | Some _ | None -> None

let valid_access_formula env block offset width =
  let global_cases =
    List.filter_map
      (fun global ->
        Option.map
          (fun block_id ->
            mk_and
              [ int_eq block (Int block_id)
              ; int_ge offset (Int 0)
              ; int_le
                  (Add (offset, width))
                  (object_byte_size_expr env.records global.global_type)
              ])
          (global_block_id env global.global_name))
      env.scalar_globals
  in
  let alloc_cases =
    List.init env.malloc_sites (fun index -> index + 1)
    |> List.map (fun site ->
           mk_and
             [ int_eq block (Int (alloc_block_id env site))
             ; int_eq (Var (alloc_live_name site)) (Int 1)
             ; int_ge offset (Int 0)
             ; int_le (Add (offset, width)) (Var (alloc_size_name site))
             ])
  in
  mk_or (global_cases @ alloc_cases)

let can_free_formula env block offset =
  let null_case =
    mk_and [ int_eq block (Int 0); int_eq offset (Int 0) ]
  in
  let alloc_cases =
    List.init env.malloc_sites (fun index -> index + 1)
    |> List.map (fun site ->
           mk_and
             [ int_eq block (Int (alloc_block_id env site))
             ; int_eq offset (Int 0)
             ; int_eq (Var (alloc_live_name site)) (Int 1)
             ])
  in
  mk_or (null_case :: alloc_cases)

let pointer_shadow_globals pointer_globals =
  List.concat_map
    (fun name -> [ ptr_block_name name; ptr_offset_name name ])
    pointer_globals

let alloc_globals malloc_sites =
  List.init malloc_sites (fun index -> index + 1)
  |> List.concat_map (fun site -> [ alloc_live_name site; alloc_size_name site ])

let init_alloc_stmt site =
  Seq
    [ Assign (alloc_live_name site, Int 0)
    ; Assign (alloc_size_name site, Int 0)
    ]

let alloc_init_stmts malloc_sites =
  List.init malloc_sites (fun index -> index + 1)
  |> List.map init_alloc_stmt

let mark_heap_failure_stmt =
  Assign (heap_ok_name, Int 0)

let heap_guard_stmt condition success_stmts =
  If (condition, seq_of_list success_stmts, mark_heap_failure_stmt)

let pointer_object_byte_size_expr =
  Int pointer_object_byte_size

let concrete_pointer_expr (pointer : concrete_pointer) =
  Int pointer.block_id, Int pointer.offset

let scalar_shadow_location env block offset c_type =
  match extract_int block, extract_int offset with
  | Some block_id, Some offset ->
      shadowable_location env block_id offset (scalar_byte_size c_type)
  | _ ->
      None

let pointer_shadow_location env block offset =
  match extract_int block, extract_int offset with
  | Some block_id, Some offset ->
      shadowable_location env block_id offset pointer_object_byte_size
  | _ ->
      None

let pointer_load_prefix env block offset =
  [ heap_guard_stmt (valid_access_formula env block offset pointer_object_byte_size_expr) [] ]

let pointer_load_value block offset =
  FuncCall (load_ptr_block_helper_name, [ block; offset ]),
  FuncCall (load_ptr_offset_helper_name, [ block; offset ])

let pointer_load_from_address env block offset pointee =
  let loaded_block, loaded_offset = pointer_load_value block offset in
  pointer_load_prefix env block offset, loaded_block, loaded_offset, Some pointee

let scale_pointer_delta records pointee delta =
  mul_expr delta (object_byte_size_expr records pointee)

let int_expr_of_char value =
  Int value

let int_expr_of_bool = function
  | true -> Int 1
  | false -> Int 0

let concrete_pointer_of_exprs ?pointee block offset =
  match extract_int block, extract_int offset with
  | Some block_id, Some offset ->
      Some { block_id; offset; pointee }
  | _ ->
      None

let rec lower_addressable_expr env state = function
  | Var name ->
      if is_pointer_name env name then
        fail "pointer variable `%s` is not an addressable object in this memory model" name
      else
        (match global_block_id env name, global_scalar_type env name with
        | Some block_id, Some c_type -> Ok ([], Int block_id, Int 0, c_type, state)
        | None, Some _ ->
            fail "missing object `%s` in memory environment" name
        | _, None ->
            fail "unknown addressable object `%s`" name)
  | Field (base, field) ->
      let* prefix, block, offset, base_type, state =
        lower_addressable_expr env state base
      in
      let* record_name =
        match base_type with
        | TRecord record_name -> Ok record_name
        | _ ->
            fail "expected a record receiver in `%s`" (expr_to_c (Field (base, field)))
      in
      let* field_type =
        match lookup_field_type env record_name field with
        | Some field_type -> Ok field_type
        | None ->
            fail "unknown field `%s` on `struct %s`" field record_name
      in
      let* field_offset =
        match lookup_field_offset env record_name field with
        | Some field_offset -> Ok field_offset
        | None ->
            fail "unknown field `%s` on `struct %s`" field record_name
      in
      Ok (prefix, block, add_expr offset (Int field_offset), field_type, state)
  | Index (base, index) ->
      let* prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state (Add (base, index))
      in
      (match pointee_opt with
      | Some pointee -> Ok (prefix, block, offset, pointee, state)
      | None ->
          fail "could not infer the element type for indexed access")
  | Deref ptr ->
      let* prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state ptr
      in
      (match pointee_opt with
      | Some pointee -> Ok (prefix, block, offset, pointee, state)
      | None ->
          fail "could not infer the pointee type for dereference")
  | expr ->
      fail "unsupported addressable expression `%s`" (expr_to_c expr)

and lower_scalar_expr env state expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr ->
      Ok ([], expr, state)
  | Var name ->
      if is_pointer_name env name then
        fail "pointer variable `%s` used where a scalar was expected" name
      else
        (match global_scalar_type env name with
        | Some (TArray _) ->
            fail "array `%s` used where a scalar was expected" name
        | Some (TRecord _) ->
            fail "record `%s` used where a scalar was expected" name
        | Some _ | None ->
            Ok ([], Var name, state))
  | AddrOf _ ->
      fail "address-of expression used where a scalar was expected"
  | Index (base, index) ->
      let* prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state (Add (base, index))
      in
      let* pointee =
        match pointee_opt with
        | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
            Ok pointee
        | Some TVoid ->
            fail "cannot index into `void*` in this proof-of-concept"
        | Some (TRecord _) ->
            fail "record indexing is unsupported in this proof-of-concept"
        | Some (TPointer _) ->
            fail "pointer-to-pointer indexing is unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array indexing is unsupported in this proof-of-concept"
        | Some (TReference _) | Some (TConstReference _) ->
            fail "reference indexing is unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the element type for indexed access"
      in
      (match scalar_shadow_location env block offset pointee with
      | Some location ->
          (match lookup_shadow_scalar state location pointee with
          | Some value ->
              Ok (prefix, value, state)
          | None ->
              Ok
                ( prefix
                  @ [ heap_guard_stmt
                        (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                        [] ]
                , FuncCall (load_helper_name pointee, [ block; offset ])
                , state ))
      | None ->
          Ok
            ( prefix
              @ [ heap_guard_stmt
                    (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                    [] ]
            , FuncCall (load_helper_name pointee, [ block; offset ])
            , state ))
  | Deref ptr ->
      let* prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state ptr
      in
      let* pointee =
        match pointee_opt with
        | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
            Ok pointee
        | Some TVoid ->
            fail "cannot dereference `void*` in this proof-of-concept"
        | Some (TRecord _) ->
            fail "record dereference is unsupported in this proof-of-concept"
        | Some (TPointer _) ->
            fail "pointer-to-pointer operations are unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array operations are unsupported in this proof-of-concept"
        | Some (TReference _) | Some (TConstReference _) ->
            fail "reference dereference is unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the pointee type for dereference"
      in
      (match scalar_shadow_location env block offset pointee with
      | Some location ->
          (match lookup_shadow_scalar state location pointee with
          | Some value ->
              Ok (prefix, value, state)
          | None ->
              Ok
                ( prefix
                  @ [ heap_guard_stmt
                        (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                        [] ]
                , FuncCall (load_helper_name pointee, [ block; offset ])
                , state ))
      | None ->
          Ok
            ( prefix
              @ [ heap_guard_stmt
                    (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                    [] ]
            , FuncCall (load_helper_name pointee, [ block; offset ])
            , state ))
  | Field (base, field) ->
      let* prefix, block, offset, field_type, state =
        lower_field_address env state base field
      in
      let* field_type =
        match field_type with
        | TInt | TFloat | TDouble | TChar | TBool as field_type ->
            Ok field_type
        | TVoid ->
            fail "cannot read a `void` field"
        | TRecord _ ->
            fail "record-valued fields are unsupported in this proof-of-concept"
        | TPointer _ ->
            fail "pointer-valued fields are unsupported in this proof-of-concept"
        | TArray _ ->
            fail "array-valued fields are unsupported in this proof-of-concept"
        | TReference _ | TConstReference _ ->
            fail "reference-valued fields are unsupported in this proof-of-concept"
      in
      (match scalar_shadow_location env block offset field_type with
      | Some location ->
          (match lookup_shadow_scalar state location field_type with
          | Some value ->
              Ok (prefix, value, state)
          | None ->
              Ok
                ( prefix
                  @ [ heap_guard_stmt
                        (valid_access_formula env block offset (scalar_byte_size_expr field_type))
                        [] ]
                , FuncCall (load_helper_name field_type, [ block; offset ])
                , state ))
      | None ->
          Ok
            ( prefix
              @ [ heap_guard_stmt
                    (valid_access_formula env block offset (scalar_byte_size_expr field_type))
                    [] ]
            , FuncCall (load_helper_name field_type, [ block; offset ])
            , state ))
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Scalar_kind, Scalar_kind ->
          let* left_prefix, left, state = lower_scalar_expr env state left in
          let* right_prefix, right, state = lower_scalar_expr env state right in
          Ok (left_prefix @ right_prefix, Add (left, right), state)
      | _ ->
          fail "pointer arithmetic result used where a scalar was expected")
  | Sub (left, right) ->
      let* left_prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (left_prefix @ right_prefix, Sub (left, right), state)
  | Mul (left, right) ->
      let* left_prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (left_prefix @ right_prefix, Mul (left, right), state)
  | Div (left, right) ->
      let* left_prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (left_prefix @ right_prefix, Div (left, right), state)
  | Mod (left, right) ->
      let* left_prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (left_prefix @ right_prefix, Mod (left, right), state)
  | FuncCall (name, args) when String.equal name "malloc" ->
      fail "`malloc` used where a scalar was expected"
  | FuncCall (name, args) ->
      let* prefix, args, state = lower_call_args env state name args in
      Ok (prefix, FuncCall (name, args), state)

and lower_field_address env state base field =
  let* prefix, block, offset, base_type, state =
    lower_addressable_expr env state base
  in
  let* record_name =
    match base_type with
    | TRecord record_name -> Ok record_name
    | _ ->
        fail "expected a record receiver in `%s`" (expr_to_c (Field (base, field)))
  in
  let* field_type =
    match lookup_field_type env record_name field with
    | Some field_type -> Ok field_type
    | None ->
        fail "unknown field `%s` on `struct %s`" field record_name
  in
  let* field_offset =
    match lookup_field_offset env record_name field with
    | Some offset -> Ok offset
    | None ->
        fail "unknown field `%s` on `struct %s`" field record_name
  in
  Ok (prefix, block, add_expr offset (Int field_offset), field_type, state)

and lower_pointer_value_from_addressable env state expr =
  let* prefix, block, offset, value_type, state =
    lower_addressable_expr env state expr
  in
  match value_type with
  | TPointer pointee ->
      (match pointer_shadow_location env block offset with
      | Some location ->
          (match lookup_shadow_pointer state location pointee with
          | Some pointer ->
              let block, offset = concrete_pointer_expr pointer in
              Ok (prefix, block, offset, Some pointee, state)
          | None ->
              let load_prefix, loaded_block, loaded_offset, pointee_opt =
                pointer_load_from_address env block offset pointee
              in
              Ok (prefix @ load_prefix, loaded_block, loaded_offset, pointee_opt, state))
      | None ->
          let load_prefix, loaded_block, loaded_offset, pointee_opt =
            pointer_load_from_address env block offset pointee
          in
          Ok (prefix @ load_prefix, loaded_block, loaded_offset, pointee_opt, state))
  | TArray (element_type, _) ->
      Ok (prefix, block, offset, Some element_type, state)
  | _ ->
      fail "expression `%s` does not evaluate to a pointer" (expr_to_c expr)

and lower_call_args env state name args =
  match lookup_function_sig env name with
  | None ->
      lower_scalar_expr_list env state args
  | Some (param_types, _return_type) ->
      let rec loop state param_types args =
        match param_types, args with
        | [], [] ->
            Ok ([], [], state)
        | TPointer pointee :: rest_params, arg :: rest_args ->
            let* prefix, block, offset, _pointee, state =
              lower_ptr_expr ~expected:pointee env state arg
            in
            let* rest_prefix, rest_args, state = loop state rest_params rest_args in
            Ok (prefix @ rest_prefix, block :: offset :: rest_args, state)
        | (TInt | TFloat | TDouble | TChar | TBool) :: rest_params, arg :: rest_args ->
            let* prefix, lowered_arg, state = lower_scalar_expr env state arg in
            let* rest_prefix, rest_args, state = loop state rest_params rest_args in
            Ok (prefix @ rest_prefix, lowered_arg :: rest_args, state)
        | TVoid :: _, _ ->
            fail "void parameters are unsupported in lowered calls to `%s`" name
        | TRecord _ :: _, _ ->
            fail "record parameters are unsupported in lowered calls to `%s`" name
        | TArray _ :: _, _ ->
            fail "array parameters are unsupported in lowered calls to `%s`" name
        | TReference _ :: _, _
        | TConstReference _ :: _, _ ->
            fail "reference parameters should be lowered before lowered calls to `%s`" name
        | _, _ ->
            fail "arity mismatch while lowering call to `%s`" name
      in
      loop state param_types args

and lower_scalar_expr_list env state exprs =
  match exprs with
  | [] -> Ok ([], [], state)
  | expr :: rest ->
      let* prefix, expr, state = lower_scalar_expr env state expr in
      let* rest_prefix, rest, state = lower_scalar_expr_list env state rest in
      Ok (prefix @ rest_prefix, expr :: rest, state)

and lower_ptr_expr ?expected env state expr =
  match expr with
  | Var name when is_pointer_name env name ->
      (match lookup_known_pointer state name with
      | Some pointer ->
          let block, offset = concrete_pointer_expr pointer in
          Ok ([], block, offset, pointer.pointee, state)
      | None ->
          Ok
            ( []
            , Var (ptr_block_name name)
            , Var (ptr_offset_name name)
            , pointer_pointee_type env name
            , state ))
  | Var name ->
      (match global_scalar_type env name with
      | Some (TArray (element_type, _)) ->
          (match global_block_id env name with
          | Some block_id -> Ok ([], Int block_id, Int 0, Some element_type, state)
          | None -> fail "missing array global `%s` in memory environment" name)
      | Some (TRecord _) ->
          fail "record `%s` used where a pointer was expected" name
      | Some _ | None ->
          Ok ([], Var name, Int 0, None, state))
  | Int n ->
      Ok ([], Int n, Int 0, expected, state)
  | CharLit value ->
      Ok ([], int_expr_of_char value, Int 0, expected, state)
  | BoolLit value ->
      Ok ([], int_expr_of_bool value, Int 0, expected, state)
  | FloatLit _ | DoubleLit _ ->
      fail "floating-point values cannot be used as pointer expressions"
  | AddrOf (Var name) ->
      (match global_block_id env name, global_decay_pointee_type env name with
      | Some block_id, Some global_type ->
          Ok ([], Int block_id, Int 0, Some global_type, state)
      | None, _ ->
          fail "only address-of for modeled objects is supported, got `&%s`" name
      | _, None ->
          fail "only address-of for modeled objects is supported, got `&%s`" name)
  | AddrOf inner ->
      let* prefix, block, offset, pointee, state =
        lower_addressable_expr env state inner
      in
      Ok (prefix, block, offset, Some pointee, state)
  | Index _ ->
      lower_pointer_value_from_addressable env state expr
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind pointee, Scalar_kind ->
          let* prefix, block, offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state left
          in
          let* delta_prefix, delta, state = lower_scalar_expr env state right in
          Ok
            ( prefix @ delta_prefix
            , block
            , add_expr offset (scale_pointer_delta env.records pointee delta)
            , Some pointee
            , state )
      | Scalar_kind, Pointer_kind pointee ->
          let* delta_prefix, delta, state = lower_scalar_expr env state left in
          let* prefix, block, offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state right
          in
          Ok
            ( delta_prefix @ prefix
            , block
            , add_expr offset (scale_pointer_delta env.records pointee delta)
            , Some pointee
            , state )
      | _ ->
          fail "unsupported pointer arithmetic expression")
  | FuncCall (name, args) when String.equal name "malloc" ->
      (match args with
      | [size_expr] ->
          let site = state.next_malloc_site in
          let state = { state with next_malloc_site = site + 1 } in
          let* prefix, size_expr, state = lower_scalar_expr env state size_expr in
          Ok
            ( prefix
              @ [ Assign (alloc_live_name site, Int 1)
                ; Assign (alloc_size_name site, size_expr)
                ]
            , Int (alloc_block_id env site)
            , Int 0
            , expected
            , state )
      | _ -> fail "`malloc` expects exactly one argument")
  | FuncCall _ ->
      fail "pointer-returning function calls are unsupported in this proof-of-concept"
  | Field _ | Deref _ ->
      lower_pointer_value_from_addressable env state expr
  | Sub _ | Mul _ | Div _ | Mod _ ->
      fail "unsupported pointer expression"

and lower_bexpr env state bexpr =
  match bexpr with
  | True -> Ok ([], True, state)
  | False -> Ok ([], False, state)
  | Eq (left, right) ->
      lower_equality_like env state ~negated:false left right
  | Neq (left, right) ->
      lower_equality_like env state ~negated:true left right
  | Lt (left, right) ->
      let* prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (prefix @ right_prefix, Lt (left, right), state)
  | Le (left, right) ->
      let* prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (prefix @ right_prefix, Le (left, right), state)
  | Gt (left, right) ->
      let* prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (prefix @ right_prefix, Gt (left, right), state)
  | Ge (left, right) ->
      let* prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      Ok (prefix @ right_prefix, Ge (left, right), state)
  | Not inner ->
      let* prefix, inner, state = lower_bexpr env state inner in
      Ok (prefix, Not inner, state)
  | And (left, right) ->
      let* left_prefix, left, state = lower_bexpr env state left in
      let* right_prefix, right, state = lower_bexpr env state right in
      if left_prefix <> [] || right_prefix <> [] then
        fail "memory operations inside `&&` conditions are unsupported"
      else
        Ok ([], And (left, right), state)
  | Or (left, right) ->
      let* left_prefix, left, state = lower_bexpr env state left in
      let* right_prefix, right, state = lower_bexpr env state right in
      if left_prefix <> [] || right_prefix <> [] then
        fail "memory operations inside `||` conditions are unsupported"
      else
        Ok ([], Or (left, right), state)

and lower_equality_like env state ~negated left right =
  match expr_kind env left, expr_kind env right with
  | Pointer_kind pointee, _ ->
      let* prefix, left_block, left_offset, _left_pointee, state =
        lower_ptr_expr ~expected:pointee env state left
      in
      let* right_prefix, right_block, right_offset, _right_pointee, state =
        lower_ptr_expr ~expected:pointee env state right
      in
      let eq_formula =
        mk_and
          [ int_eq left_block right_block
          ; int_eq left_offset right_offset
          ]
      in
      let formula =
        if negated then Not eq_formula else eq_formula
      in
      Ok (prefix @ right_prefix, formula, state)
  | _, Pointer_kind pointee ->
      let* prefix, left_block, left_offset, _left_pointee, state =
        lower_ptr_expr ~expected:pointee env state left
      in
      let* right_prefix, right_block, right_offset, _right_pointee, state =
        lower_ptr_expr ~expected:pointee env state right
      in
      let eq_formula =
        mk_and
          [ int_eq left_block right_block
          ; int_eq left_offset right_offset
          ]
      in
      let formula =
        if negated then Not eq_formula else eq_formula
      in
      Ok (prefix @ right_prefix, formula, state)
  | Scalar_kind, Scalar_kind ->
      let* prefix, left, state = lower_scalar_expr env state left in
      let* right_prefix, right, state = lower_scalar_expr env state right in
      let formula =
        if negated then Neq (left, right) else Eq (left, right)
      in
      Ok (prefix @ right_prefix, formula, state)

and lower_stmt env state stmt =
  match stmt with
  | Skip -> Ok (Skip, state)
  | Block _ | LocalDecl _ ->
      fail "unresolved local syntax reached memory lowering"
  | Assign (name, rhs) ->
      (match pointer_pointee_type env name with
      | Some pointee ->
          let* prefix, block, offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state rhs
          in
          let state =
            match concrete_pointer_of_exprs ~pointee block offset with
            | Some pointer -> remember_known_pointer state name pointer
            | None -> forget_known_pointer state name
          in
          Ok
            ( seq_of_list
                (prefix
                @ [ Assign (ptr_block_name name, block)
                  ; Assign (ptr_offset_name name, offset)
                  ])
            , state )
      | None ->
          (match global_scalar_type env name with
          | Some (TRecord _) ->
              fail "record assignment to `%s` is unsupported in this proof-of-concept" name
          | Some _ | None ->
              let* prefix, rhs, state = lower_scalar_expr env state rhs in
              Ok (seq_of_list (prefix @ [ Assign (name, rhs) ]), state)))
  | Store (ptr, value) ->
      let* ptr_prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state ptr
      in
      (match pointee_opt with
      | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
          let* value_prefix, lowered_value, state = lower_scalar_expr env state value in
          let shadow_prefix, shadow_value, state =
            match scalar_shadow_location env block offset pointee with
            | Some _ ->
                freeze_scalar_value state pointee lowered_value
            | None ->
                [], lowered_value, clear_shadow_cells state
          in
          let state =
            match scalar_shadow_location env block offset pointee with
            | Some location ->
                update_shadow_scalar state location pointee shadow_value
            | None ->
                state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ shadow_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                      []
                  ])
            , state )
      | Some TVoid ->
          fail "cannot write through `void*` in this proof-of-concept"
      | Some (TRecord _) ->
          fail "record stores are unsupported in this proof-of-concept"
      | Some (TPointer pointee) ->
          let* value_prefix, value_block, value_offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state value
          in
          let state =
            match pointer_shadow_location env block offset with
            | Some location ->
                (match concrete_pointer_of_exprs ~pointee value_block value_offset with
                | Some pointer ->
                    update_shadow_pointer state location pointee pointer
                | None ->
                    forget_shadow_location state location)
            | None ->
                clear_shadow_cells state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset pointer_object_byte_size_expr)
                      []
                  ])
            , state )
      | Some (TArray _) ->
          fail "nested array stores are unsupported in this proof-of-concept"
      | Some (TReference _) | Some (TConstReference _) ->
          fail "reference stores are unsupported in this proof-of-concept"
      | None ->
          fail "could not infer the pointee type for store")
  | ArrayAssign (base, index, value) ->
      let* ptr_prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state (Add (base, index))
      in
      (match pointee_opt with
      | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
          let* value_prefix, lowered_value, state = lower_scalar_expr env state value in
          let shadow_prefix, shadow_value, state =
            match scalar_shadow_location env block offset pointee with
            | Some _ ->
                freeze_scalar_value state pointee lowered_value
            | None ->
                [], lowered_value, clear_shadow_cells state
          in
          let state =
            match scalar_shadow_location env block offset pointee with
            | Some location ->
                update_shadow_scalar state location pointee shadow_value
            | None ->
                state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ shadow_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                      []
                  ])
            , state )
      | Some TVoid ->
          fail "cannot write through `void*` in this proof-of-concept"
      | Some (TRecord _) ->
          fail "record stores are unsupported in this proof-of-concept"
      | Some (TPointer pointee) ->
          let* value_prefix, value_block, value_offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state value
          in
          let state =
            match pointer_shadow_location env block offset with
            | Some location ->
                (match concrete_pointer_of_exprs ~pointee value_block value_offset with
                | Some pointer ->
                    update_shadow_pointer state location pointee pointer
                | None ->
                    forget_shadow_location state location)
            | None ->
                clear_shadow_cells state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset pointer_object_byte_size_expr)
                      []
                  ])
            , state )
      | Some (TArray _) ->
          fail "nested array stores are unsupported in this proof-of-concept"
      | Some (TReference _) | Some (TConstReference _) ->
          fail "reference stores are unsupported in this proof-of-concept"
      | None ->
          fail "could not infer the element type for indexed store")
  | FieldAssign (base, field, value) ->
      let* ptr_prefix, block, offset, field_type, state =
        lower_field_address env state base field
      in
      (match field_type with
      | TInt | TFloat | TDouble | TChar | TBool as field_type ->
          let* value_prefix, lowered_value, state = lower_scalar_expr env state value in
          let shadow_prefix, shadow_value, state =
            match scalar_shadow_location env block offset field_type with
            | Some _ ->
                freeze_scalar_value state field_type lowered_value
            | None ->
                [], lowered_value, clear_shadow_cells state
          in
          let state =
            match scalar_shadow_location env block offset field_type with
            | Some location ->
                update_shadow_scalar state location field_type shadow_value
            | None ->
                state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ shadow_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset (scalar_byte_size_expr field_type))
                      []
                  ])
            , state )
      | TVoid ->
          fail "cannot assign to a `void` field"
      | TRecord _ ->
          fail "record-valued fields are unsupported in this proof-of-concept"
      | TPointer pointee ->
          let* value_prefix, value_block, value_offset, _pointee, state =
            lower_ptr_expr ~expected:pointee env state value
          in
          let state =
            match pointer_shadow_location env block offset with
            | Some location ->
                (match concrete_pointer_of_exprs ~pointee value_block value_offset with
                | Some pointer ->
                    update_shadow_pointer state location pointee pointer
                | None ->
                    forget_shadow_location state location)
            | None ->
                clear_shadow_cells state
          in
          Ok
            ( seq_of_list
                (ptr_prefix
                @ value_prefix
                @ [ heap_guard_stmt
                      (valid_access_formula env block offset pointer_object_byte_size_expr)
                      []
                  ])
            , state )
      | TArray _ ->
          fail "array-valued fields are unsupported in this proof-of-concept"
      | TReference _ | TConstReference _ ->
          fail "reference-valued fields are unsupported in this proof-of-concept")
  | Seq stmts ->
      let* stmts, state = lower_stmt_list env state stmts in
      Ok (seq_of_list stmts, state)
  | If (cond, then_branch, else_branch) ->
      let* prefix, cond, state = lower_bexpr env state cond in
      let branch_seed = state in
      let* then_branch, then_state = lower_stmt env branch_seed then_branch in
      let else_seed =
        {
          then_state with
          shadow_cells = branch_seed.shadow_cells;
          known_pointers = branch_seed.known_pointers;
        }
      in
      let* else_branch, else_state = lower_stmt env else_seed else_branch in
      let state = merge_semantic_state else_state then_state else_state in
      Ok (seq_of_list (prefix @ [ If (cond, then_branch, else_branch) ]), state)
  | While (invariant, cond, body) ->
      let* invariant =
        match invariant with
        | None -> Ok None
        | Some invariant ->
            let* prefix, invariant, state = lower_bexpr env state invariant in
            if prefix <> [] then
              fail "memory operations inside loop invariants are unsupported"
            else
              Ok (Some invariant)
      in
      let* prefix, cond, state = lower_bexpr env state cond in
      if prefix <> [] then
        fail "memory operations inside `while` conditions are unsupported"
      else
        let* body, body_state = lower_stmt env state body in
        Ok (While (invariant, cond, body), clear_semantic_state body_state)
  | Assume cond ->
      let* prefix, cond, state = lower_bexpr env state cond in
      Ok (seq_of_list (prefix @ [ Assume cond ]), state)
  | Assert (origin, cond) ->
      let* prefix, cond, state = lower_bexpr env state cond in
      Ok (seq_of_list (prefix @ [ Assert (origin, cond) ]), state)
  | Free ptr ->
      let* prefix, block, offset, _pointee, state = lower_ptr_expr env state ptr in
      let live_updates =
        List.init env.malloc_sites (fun index -> index + 1)
        |> List.map (fun site ->
               If
                 ( Neq (block, Int (alloc_block_id env site))
                 , Skip
                 , Assign (alloc_live_name site, Int 0) ))
      in
      Ok
        ( seq_of_list
            (prefix
            @ [ heap_guard_stmt (can_free_formula env block offset) live_updates ])
        , state )
  | Return None -> Ok (Return None, state)
  | Return (Some value) ->
      let* prefix, value, state = lower_scalar_expr env state value in
      Ok (seq_of_list (prefix @ [ Return (Some value) ]), state)

and lower_stmt_list env state stmts =
  match stmts with
  | [] -> Ok ([], state)
  | stmt :: rest ->
      let* stmt, state = lower_stmt env state stmt in
      let* rest, state = lower_stmt_list env state rest in
      Ok (stmt :: rest, state)

let lower_function env state fn =
  let has_array_param =
    List.exists
      (fun param ->
        match param.param_type with
        | TArray _ -> true
        | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _
        | TReference _ | TConstReference _ ->
            false)
      fn.params
  in
  let has_record_param =
    List.exists
      (fun param ->
        match param.param_type with
        | TRecord _ -> true
        | TInt | TFloat | TDouble | TChar | TBool | TVoid | TPointer _ | TArray _
        | TReference _ | TConstReference _ ->
            false)
      fn.params
  in
  if has_array_param then
    fail
      "array parameters in function `%s` are unsupported in this proof-of-concept"
      fn.name
  else if has_record_param then
    fail
      "record parameters in function `%s` are unsupported in this proof-of-concept"
      fn.name
  else
    match fn.return_type with
    | TPointer _ ->
        fail
          "pointer return type in function `%s` is unsupported in this proof-of-concept"
          fn.name
    | TArray _ ->
        fail
          "array return type in function `%s` is unsupported in this proof-of-concept"
          fn.name
    | TRecord _ ->
        fail
          "record return type in function `%s` is unsupported in this proof-of-concept"
          fn.name
    | TInt | TFloat | TDouble | TChar | TBool | TVoid ->
        let params = lower_function_params fn.params in
        let state = clear_semantic_state state in
        let init = alloc_init_stmts env.malloc_sites in
        let* body, state = lower_stmt env state fn.body in
        let body = seq_of_list (Assign (heap_ok_name, Int 1) :: init @ [ body ]) in
        Ok ({ fn with params; body }, clear_semantic_state state)
    | TReference _
    | TConstReference _ ->
        fail
          "reference return type in function `%s` is unsupported in this proof-of-concept"
          fn.name

let lower_functions (program : program) state malloc_sites functions =
  let rec loop acc state = function
    | [] -> Ok (List.rev acc, state)
    | fn :: rest ->
        let env = function_env_of_program program fn malloc_sites in
        let* fn, state = lower_function env state fn in
        loop (fn :: acc) state rest
  in
  loop [] state functions

let lower_program (program : program) =
  let* program = lower_references_program program in
  if not (uses_memory_program program) then
    Ok program
  else
  let malloc_sites = count_malloc_program program in
  let state =
    {
      next_malloc_site = 1;
      next_shadow_temp = 1;
      temp_globals_rev = [];
      shadow_cells = [];
      known_pointers = [];
    }
  in
  let* functions = lower_functions program state malloc_sites program.functions in
  let functions, state = functions in
  let main_env = function_env_of_program program program.main malloc_sites in
  let* main, state = lower_function main_env state program.main in
  let pointer_names =
    List.concat_map
      (fun fn ->
        pointer_bindings_of_defs fn.locals
        |> List.map fst)
      (program.main :: program.functions)
  in
  let extra_globals =
    pointer_shadow_globals (List.sort_uniq String.compare (List.map fst (pointer_globals_of_program program) @ pointer_names))
    @ alloc_globals malloc_sites
    @ [ heap_ok_name ]
  in
  Ok
    {
      program with
      globals =
        program.globals
        @ List.rev state.temp_globals_rev
        @ List.map (fun name -> { global_type = TInt; global_name = name }) extra_globals;
      functions;
      main;
    }

let contract_env_of_program (program : program) =
  {
    records = program.records;
    scalar_globals = scalar_globals program.globals;
    pointer_globals = pointer_globals_of_program program;
    function_sigs = build_function_sigs program;
    malloc_sites = count_malloc_program program;
  }

let rec lower_contract_scalar_expr env expr =
  match expr with
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ as expr -> Ok expr
  | Var name ->
      if is_pointer_name env name then
        fail "pointer variable `%s` used where a scalar contract expression was expected" name
      else
        (match global_scalar_type env name with
        | Some (TArray _) ->
            fail "array `%s` used where a scalar contract expression was expected" name
        | Some (TRecord _) ->
            fail "record `%s` used where a scalar contract expression was expected" name
        | Some _ | None ->
            Ok (Var name))
  | AddrOf _ ->
      fail "address-of expression used where a scalar contract expression was expected"
  | Index _ ->
      fail "indexed reads are unsupported inside contract expressions"
  | Deref ptr ->
      let* block, offset, pointee_opt = lower_contract_ptr_expr env ptr in
      (match pointee_opt with
      | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
          Ok (FuncCall (load_helper_name pointee, [ block; offset ]))
      | Some TVoid ->
          fail "cannot dereference `void*` inside contract expressions"
      | Some (TRecord _) ->
          fail "record dereference is unsupported inside contract expressions"
      | Some (TPointer _) ->
          fail "pointer-to-pointer dereference is unsupported inside contract expressions"
      | Some (TArray _) ->
          fail "nested array dereference is unsupported inside contract expressions"
      | Some (TReference _) | Some (TConstReference _) ->
          fail "reference dereference is unsupported inside contract expressions"
      | None ->
          fail "could not infer the pointee type for contract dereference")
  | Field _ ->
      fail "field reads are unsupported inside contract expressions"
  | Add (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Add (left, right))
  | Sub (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Sub (left, right))
  | Mul (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Mul (left, right))
  | Div (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Div (left, right))
  | Mod (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Mod (left, right))
  | FuncCall (name, args) ->
      let* args =
        match lower_contract_scalar_expr_list env args with
        | Ok args -> Ok args
        | Error _ as error -> error
      in
      Ok (FuncCall (name, args))

and lower_contract_scalar_expr_list env exprs =
  match exprs with
  | [] -> Ok []
  | expr :: rest ->
      let* expr = lower_contract_scalar_expr env expr in
      let* rest = lower_contract_scalar_expr_list env rest in
      Ok (expr :: rest)

and lower_contract_ptr_expr ?expected env expr =
  match expr with
  | Var name when is_pointer_name env name ->
      Ok (Var (ptr_block_name name), Var (ptr_offset_name name), pointer_pointee_type env name)
  | Var name ->
      (match global_scalar_type env name with
      | Some (TArray (element_type, _)) ->
          (match global_block_id env name with
          | Some block_id -> Ok (Int block_id, Int 0, Some element_type)
          | None -> fail "missing array global `%s` in contract environment" name)
      | Some (TRecord _) ->
          fail "record `%s` used where a pointer contract expression was expected" name
      | Some _ | None ->
          fail "scalar variable `%s` used where a pointer contract expression was expected" name)
  | Int n -> Ok (Int n, Int 0, None)
  | CharLit value -> Ok (int_expr_of_char value, Int 0, None)
  | BoolLit value -> Ok (int_expr_of_bool value, Int 0, None)
  | FloatLit _ | DoubleLit _ ->
      fail "floating-point values cannot be used as pointer contract expressions"
  | AddrOf (Var name) ->
      (match global_block_id env name, global_decay_pointee_type env name with
      | Some block_id, Some global_type -> Ok (Int block_id, Int 0, Some global_type)
      | None, _ ->
          fail "only address-of for globals is supported in contracts, got `&%s`" name
      | _, None ->
          fail "only address-of for globals is supported in contracts, got `&%s`" name)
  | AddrOf (Index (base, index)) ->
      lower_contract_ptr_expr env (Add (base, index))
  | AddrOf (Deref ptr) ->
      lower_contract_ptr_expr env ptr
  | AddrOf (Field _) ->
      fail "field addresses are unsupported inside contract expressions"
  | AddrOf _ ->
      fail "only address-of for globals and indexed locations is supported in contracts"
  | Index _ ->
      fail "indexed value used where a pointer contract expression was expected"
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind pointee, Scalar_kind ->
          let* block, offset, _ = lower_contract_ptr_expr ~expected:pointee env left in
          let* delta = lower_contract_scalar_expr env right in
          Ok (block, Add (offset, scale_pointer_delta env.records pointee delta), Some pointee)
      | Scalar_kind, Pointer_kind pointee ->
          let* delta = lower_contract_scalar_expr env left in
          let* block, offset, _ = lower_contract_ptr_expr ~expected:pointee env right in
          Ok (block, Add (offset, scale_pointer_delta env.records pointee delta), Some pointee)
      | _ ->
          fail "unsupported pointer arithmetic expression in contract")
  | Field _ ->
      fail "field values are unsupported inside contract pointer expressions"
  | Deref _ ->
      fail "dereference is unsupported inside contract pointer expressions"
  | FuncCall _ ->
      fail "function calls are unsupported inside contract pointer expressions"
  | Sub _ | Mul _ | Div _ | Mod _ ->
      fail "unsupported pointer contract expression"

let pointer_eq_formula left_block left_offset right_block right_offset =
  mk_and
    [ int_eq left_block right_block
    ; int_eq left_offset right_offset
    ]

let allocated_formula env block offset pointee_opt =
  let width =
    match pointee_opt with
    | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
        scalar_byte_size_expr pointee
    | Some (TRecord name) ->
        object_byte_size_expr env.records (TRecord name)
    | Some TVoid | Some (TPointer _) | Some (TArray _) | Some (TReference _)
    | Some (TConstReference _) | None ->
        Int 1
  in
  valid_access_formula env block offset width

let is_live_formula env block =
  let global_cases =
    List.filter_map
      (fun global ->
        Option.map
          (fun block_id -> int_eq block (Int block_id))
          (global_block_id env global.global_name))
      env.scalar_globals
  in
  let alloc_cases =
    List.init env.malloc_sites (fun index -> index + 1)
    |> List.map (fun site ->
           mk_and
             [ int_eq block (Int (alloc_block_id env site))
             ; int_eq (Var (alloc_live_name site)) (Int 1)
             ])
  in
  mk_or (global_cases @ alloc_cases)

let lower_predicate env name args =
  match name, args with
  | "heap_ok", [] ->
      Ok (Eq (Var heap_ok_name, Int 1))
  | "valid_read", [ptr; width]
  | "valid_write", [ptr; width] ->
      let* block, offset, _ = lower_contract_ptr_expr env ptr in
      let* width = lower_contract_scalar_expr env width in
      Ok (valid_access_formula env block offset width)
  | "allocated", [ptr] ->
      let* block, offset, pointee_opt = lower_contract_ptr_expr env ptr in
      Ok (allocated_formula env block offset pointee_opt)
  | "live", [ptr] ->
      let* block, _offset, _ = lower_contract_ptr_expr env ptr in
      Ok (is_live_formula env block)
  | "can_free", [ptr] ->
      let* block, offset, _ = lower_contract_ptr_expr env ptr in
      Ok (can_free_formula env block offset)
  | "same_block", [left; right] ->
      let* left_block, _, _ = lower_contract_ptr_expr env left in
      let* right_block, _, _ = lower_contract_ptr_expr env right in
      Ok (Eq (left_block, right_block))
  | "is_null", [ptr] ->
      let* block, offset, _ = lower_contract_ptr_expr env ptr in
      Ok (mk_and [ Eq (block, Int 0); Eq (offset, Int 0) ])
  | _ ->
      fail "unknown ghost-heap predicate `%s`" name

let rec lower_contract_bexpr env bexpr =
  match bexpr with
  | True -> Ok True
  | False -> Ok False
  | Not inner ->
      let* inner = lower_contract_bexpr env inner in
      Ok (Not inner)
  | And (left, right) ->
      let* left = lower_contract_bexpr env left in
      let* right = lower_contract_bexpr env right in
      Ok (And (left, right))
  | Or (left, right) ->
      let* left = lower_contract_bexpr env left in
      let* right = lower_contract_bexpr env right in
      Ok (Or (left, right))
  | Neq (FuncCall (name, args), Int 0)
  | Eq (FuncCall (name, args), Int 1) ->
      lower_predicate env name args
  | Eq (FuncCall (name, args), Int 0)
  | Neq (FuncCall (name, args), Int 1) ->
      let* formula = lower_predicate env name args in
      Ok (Not formula)
  | Eq (left, right) ->
      lower_contract_equality_like env false left right
  | Neq (left, right) ->
      lower_contract_equality_like env true left right
  | Lt (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Lt (left, right))
  | Le (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Le (left, right))
  | Gt (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Gt (left, right))
  | Ge (left, right) ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (Ge (left, right))

and lower_contract_equality_like env negated left right =
  match expr_kind env left, expr_kind env right with
  | Pointer_kind pointee, _ ->
      let* left_block, left_offset, _ = lower_contract_ptr_expr ~expected:pointee env left in
      let* right_block, right_offset, _ = lower_contract_ptr_expr ~expected:pointee env right in
      let formula = pointer_eq_formula left_block left_offset right_block right_offset in
      Ok (if negated then Not formula else formula)
  | _, Pointer_kind pointee ->
      let* left_block, left_offset, _ = lower_contract_ptr_expr ~expected:pointee env left in
      let* right_block, right_offset, _ = lower_contract_ptr_expr ~expected:pointee env right in
      let formula = pointer_eq_formula left_block left_offset right_block right_offset in
      Ok (if negated then Not formula else formula)
  | Scalar_kind, Scalar_kind ->
      let* left = lower_contract_scalar_expr env left in
      let* right = lower_contract_scalar_expr env right in
      Ok (if negated then Neq (left, right) else Eq (left, right))
