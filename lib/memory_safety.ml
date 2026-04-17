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
  | TPointer _ -> failwith "pointer byte size is not modeled directly"
  | TArray _ -> failwith "array is not a scalar byte-sized type"

let scalar_byte_size_expr c_type =
  Int (scalar_byte_size c_type)

let rec object_byte_size = function
  | TInt | TFloat | TDouble | TChar | TBool as c_type ->
      scalar_byte_size c_type
  | TArray (element_type, length) ->
      length * scalar_byte_size element_type
  | TVoid -> failwith "void has no object byte size"
  | TPointer _ -> failwith "pointer object byte size is not modeled directly"

let object_byte_size_expr c_type =
  Int (object_byte_size c_type)

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
  | AddrOf _ | Index _ | Deref _ -> true
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
  | Store _ | ArrayAssign _ | Free _ -> true
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
  scalar_globals : global_def list;
  pointer_globals : (var * c_type) list;
  malloc_sites : int;
}

type contract_env = env

type lower_state = {
  next_malloc_site : int;
}

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

let pointer_bindings_of_defs defs =
  List.filter_map
    (fun def ->
      match def.global_type with
      | TPointer inner -> Some (def.global_name, inner)
      | TInt | TFloat | TDouble | TChar | TBool | TVoid | TArray _ -> None)
    defs

let pointer_globals_of_program program =
  pointer_bindings_of_defs (pointer_globals program.globals)

let function_env_of_program program fn malloc_sites =
  {
    scalar_globals =
      scalar_globals program.globals
      @ List.filter (fun local -> not (is_pointer_type local.global_type)) fn.locals;
    pointer_globals =
      pointer_globals_of_program program
      @ pointer_bindings_of_defs (pointer_globals fn.locals);
    malloc_sites;
  }

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
      | _ -> Scalar_kind)
  | Index _ ->
      Scalar_kind
  | Deref _ -> Scalar_kind
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
                  (object_byte_size_expr global.global_type)
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

let scale_pointer_delta pointee delta =
  Mul (delta, scalar_byte_size_expr pointee)

let int_expr_of_char value =
  Int value

let int_expr_of_bool = function
  | true -> Int 1
  | false -> Int 0

let rec lower_scalar_expr env state expr =
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
        | Some (TPointer _) ->
            fail "pointer-to-pointer indexing is unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array indexing is unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the element type for indexed access"
      in
      Ok
        ( prefix
          @ [ heap_guard_stmt
                (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                [] ]
        , FuncCall (load_helper_name pointee, [ block; offset ])
        , state )
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
        | Some (TPointer _) ->
            fail "pointer-to-pointer operations are unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array operations are unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the pointee type for dereference"
      in
      Ok
        ( prefix
          @ [ heap_guard_stmt
                (valid_access_formula env block offset (scalar_byte_size_expr pointee))
                [] ]
        , FuncCall (load_helper_name pointee, [ block; offset ])
        , state )
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
      let* prefix, args, state = lower_scalar_expr_list env state args in
      Ok (prefix, FuncCall (name, args), state)

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
      Ok
        ( []
        , Var (ptr_block_name name)
        , Var (ptr_offset_name name)
        , pointer_pointee_type env name
        , state )
  | Var name ->
      (match global_scalar_type env name with
      | Some (TArray (element_type, _)) ->
          (match global_block_id env name with
          | Some block_id -> Ok ([], Int block_id, Int 0, Some element_type, state)
          | None -> fail "missing array global `%s` in memory environment" name)
      | Some _ | None ->
          Ok ([], Var name, Int 0, None, state))
  | Int n ->
      Ok ([], Int n, Int 0, None, state)
  | CharLit value ->
      Ok ([], int_expr_of_char value, Int 0, None, state)
  | BoolLit value ->
      Ok ([], int_expr_of_bool value, Int 0, None, state)
  | FloatLit _ | DoubleLit _ ->
      fail "floating-point values cannot be used as pointer expressions"
  | AddrOf (Var name) ->
      (match global_block_id env name, global_decay_pointee_type env name with
      | Some block_id, Some global_type ->
          Ok ([], Int block_id, Int 0, Some global_type, state)
      | None, _ ->
          fail "only address-of for globals is supported, got `&%s`" name
      | _, None ->
          fail "only address-of for globals is supported, got `&%s`" name)
  | AddrOf (Index (base, index)) ->
      lower_ptr_expr env state (Add (base, index))
  | AddrOf _ ->
      fail "only address-of for globals and indexed locations is supported"
  | Index _ ->
      fail "indexed value used where a pointer was expected"
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
            , Add (offset, scale_pointer_delta pointee delta)
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
            , Add (offset, scale_pointer_delta pointee delta)
            , Some pointee
            , state )
      | _ ->
          fail "unsupported pointer arithmetic expression")
  | FuncCall (name, args) when String.equal name "malloc" ->
      (match args with
      | [size_expr] ->
          let site = state.next_malloc_site in
          let state = { next_malloc_site = site + 1 } in
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
  | Deref _ ->
      fail "pointer-to-pointer operations are unsupported in this proof-of-concept"
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
        Ok
          ( seq_of_list
              (prefix
              @ [ Assign (ptr_block_name name, block)
                ; Assign (ptr_offset_name name, offset)
                ])
          , state )
      | None ->
        let* prefix, rhs, state = lower_scalar_expr env state rhs in
        Ok (seq_of_list (prefix @ [ Assign (name, rhs) ]), state)
      )
  | Store (ptr, value) ->
      let* ptr_prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state ptr
      in
      let* value_prefix, _value, state = lower_scalar_expr env state value in
      let* width =
        match pointee_opt with
        | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
            Ok (scalar_byte_size_expr pointee)
        | Some TVoid ->
            fail "cannot write through `void*` in this proof-of-concept"
        | Some (TPointer _) ->
            fail "pointer-to-pointer stores are unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array stores are unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the pointee type for store"
      in
      Ok
        ( seq_of_list
            (ptr_prefix
            @ value_prefix
            @ [ heap_guard_stmt (valid_access_formula env block offset width) [] ])
        , state )
  | ArrayAssign (base, index, value) ->
      let* ptr_prefix, block, offset, pointee_opt, state =
        lower_ptr_expr env state (Add (base, index))
      in
      let* value_prefix, _value, state = lower_scalar_expr env state value in
      let* width =
        match pointee_opt with
        | Some (TInt | TFloat | TDouble | TChar | TBool as pointee) ->
            Ok (scalar_byte_size_expr pointee)
        | Some TVoid ->
            fail "cannot write through `void*` in this proof-of-concept"
        | Some (TPointer _) ->
            fail "pointer-to-pointer indexed stores are unsupported in this proof-of-concept"
        | Some (TArray _) ->
            fail "nested array stores are unsupported in this proof-of-concept"
        | None ->
            fail "could not infer the element type for indexed store"
      in
      Ok
        ( seq_of_list
            (ptr_prefix
            @ value_prefix
            @ [ heap_guard_stmt (valid_access_formula env block offset width) [] ])
        , state )
  | Seq stmts ->
      let* stmts, state = lower_stmt_list env state stmts in
      Ok (seq_of_list stmts, state)
  | If (cond, then_branch, else_branch) ->
      let* prefix, cond, state = lower_bexpr env state cond in
      let* then_branch, state = lower_stmt env state then_branch in
      let* else_branch, state = lower_stmt env state else_branch in
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
        let* body, state = lower_stmt env state body in
        Ok (While (invariant, cond, body), state)
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
  let has_pointer_param =
    List.exists
      (fun param ->
        match param.param_type with
        | TPointer _ -> true
        | TInt | TFloat | TDouble | TChar | TBool | TVoid | TArray _ -> false)
      fn.params
  in
  let has_array_param =
    List.exists
      (fun param ->
        match param.param_type with
        | TArray _ -> true
        | TInt | TFloat | TDouble | TChar | TBool | TVoid | TPointer _ -> false)
      fn.params
  in
  if has_pointer_param then
    fail
      "pointer parameters in function `%s` are unsupported in this proof-of-concept"
      fn.name
  else if has_array_param then
    fail
      "array parameters in function `%s` are unsupported in this proof-of-concept"
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
    | TInt | TFloat | TDouble | TChar | TBool | TVoid ->
        let init = alloc_init_stmts env.malloc_sites in
        let* body, state = lower_stmt env state fn.body in
        let body = seq_of_list (Assign (heap_ok_name, Int 1) :: init @ [ body ]) in
        Ok ({ fn with body }, state)

let lower_functions program state malloc_sites functions =
  let rec loop acc state = function
    | [] -> Ok (List.rev acc, state)
    | fn :: rest ->
        let env = function_env_of_program program fn malloc_sites in
        let* fn, state = lower_function env state fn in
        loop (fn :: acc) state rest
  in
  loop [] state functions

let lower_program program =
  if not (uses_memory_program program) then
    Ok program
  else
  let malloc_sites = count_malloc_program program in
  let state = { next_malloc_site = 1 } in
  let* functions = lower_functions program state malloc_sites program.functions in
  let functions, state = functions in
  let main_env = function_env_of_program program program.main malloc_sites in
  let* main, _ = lower_function main_env state program.main in
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
        @ List.map (fun name -> { global_type = TInt; global_name = name }) extra_globals;
      functions;
      main;
    }

let contract_env_of_program program =
  {
    scalar_globals = scalar_globals program.globals;
    pointer_globals = pointer_globals_of_program program;
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
        | Some _ | None ->
            Ok (Var name))
  | AddrOf _ ->
      fail "address-of expression used where a scalar contract expression was expected"
  | Index _ ->
      fail "indexed reads are unsupported inside contract expressions"
  | Deref _ ->
      fail "dereference is unsupported inside contract expressions"
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
  | AddrOf _ ->
      fail "only address-of for globals and indexed locations is supported in contracts"
  | Index _ ->
      fail "indexed value used where a pointer contract expression was expected"
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind pointee, Scalar_kind ->
          let* block, offset, _ = lower_contract_ptr_expr ~expected:pointee env left in
          let* delta = lower_contract_scalar_expr env right in
          Ok (block, Add (offset, scale_pointer_delta pointee delta), Some pointee)
      | Scalar_kind, Pointer_kind pointee ->
          let* delta = lower_contract_scalar_expr env left in
          let* block, offset, _ = lower_contract_ptr_expr ~expected:pointee env right in
          Ok (block, Add (offset, scale_pointer_delta pointee delta), Some pointee)
      | _ ->
          fail "unsupported pointer arithmetic expression in contract")
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
    | Some TVoid | Some (TPointer _) | Some (TArray _) | None ->
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
