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
  | Int _ | Var _ | AddrOf _ -> 0
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
  | Int _ | Var _ -> false
  | AddrOf _ | Deref _ -> true
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
  | Assign (_, expr) -> count_malloc_expr expr
  | Store (ptr, value) -> count_malloc_expr ptr + count_malloc_expr value
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
  | Assert cond ->
      count_malloc_bexpr cond
  | Free ptr -> count_malloc_expr ptr
  | Return None -> 0
  | Return (Some value) -> count_malloc_expr value

let rec uses_memory_stmt = function
  | Skip -> false
  | Assign (_, expr) -> uses_memory_expr expr
  | Store _ | Free _ -> true
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
  | Assume cond | Assert cond -> uses_memory_bexpr cond
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

let uses_memory_program program =
  program.pointer_globals <> []
  || List.exists uses_memory_stmt (program.main.body :: List.map (fun fn -> fn.body) program.functions)
  || List.exists function_mentions_memory_contract (program.main :: program.functions)
  || List.exists
       (fun (imported_header : header_import) ->
         List.exists imported_function_mentions_memory_contract imported_header.functions)
       program.imports

type expr_kind =
  | Int_kind
  | Pointer_kind

type env = {
  int_globals : var list;
  pointer_globals : var list;
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
        if String.equal current name then Some index
        else loop (index + 1) rest
  in
  loop 1 env.int_globals

let alloc_block_id env site =
  List.length env.int_globals + site

let is_pointer_name env name =
  List.exists (String.equal name) env.pointer_globals

let rec expr_kind env = function
  | Int _ -> Int_kind
  | Var name ->
      if is_pointer_name env name then Pointer_kind else Int_kind
  | AddrOf _ -> Pointer_kind
  | Deref _ -> Int_kind
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind, Int_kind
      | Int_kind, Pointer_kind ->
          Pointer_kind
      | Int_kind, Int_kind -> Int_kind
      | Pointer_kind, Pointer_kind -> Int_kind)
  | Sub _ | Mul _ | Div _ | Mod _ -> Int_kind
  | FuncCall (name, args) ->
      if String.equal name "malloc" && List.length args = 1 then Pointer_kind
      else Int_kind

let valid_access_formula env block offset width =
  let global_cases =
    List.filter_map
      (fun name ->
        Option.map
          (fun block_id ->
            mk_and
              [ int_eq block (Int block_id)
              ; int_ge offset (Int 0)
              ; int_le (Add (offset, width)) (Int 1)
              ])
          (global_block_id env name))
      env.int_globals
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

let rec lower_int_expr env state expr =
  match expr with
  | Int _ as expr -> Ok ([], expr, state)
  | Var name when not (is_pointer_name env name) ->
      Ok ([], Var name, state)
  | Var name ->
      fail "pointer variable `%s` used where an integer was expected" name
  | AddrOf _ ->
      fail "address-of expression used where an integer was expected"
  | Deref ptr ->
      let* prefix, block, offset, state = lower_ptr_expr env state ptr in
      Ok
        ( prefix
          @ [ heap_guard_stmt
                (valid_access_formula env block offset (Int 1))
                [] ]
        , FuncCall ("__anvil_load", [ block; offset ])
        , state )
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Int_kind, Int_kind ->
          let* left_prefix, left, state = lower_int_expr env state left in
          let* right_prefix, right, state = lower_int_expr env state right in
          Ok (left_prefix @ right_prefix, Add (left, right), state)
      | _ ->
          fail "pointer arithmetic result used where an integer was expected")
  | Sub (left, right) ->
      let* left_prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (left_prefix @ right_prefix, Sub (left, right), state)
  | Mul (left, right) ->
      let* left_prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (left_prefix @ right_prefix, Mul (left, right), state)
  | Div (left, right) ->
      let* left_prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (left_prefix @ right_prefix, Div (left, right), state)
  | Mod (left, right) ->
      let* left_prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (left_prefix @ right_prefix, Mod (left, right), state)
  | FuncCall (name, args) when String.equal name "malloc" ->
      fail "`malloc` used where an integer was expected"
  | FuncCall (name, args) ->
      let* prefix, args, state = lower_int_expr_list env state args in
      Ok (prefix, FuncCall (name, args), state)

and lower_int_expr_list env state exprs =
  match exprs with
  | [] -> Ok ([], [], state)
  | expr :: rest ->
      let* prefix, expr, state = lower_int_expr env state expr in
      let* rest_prefix, rest, state = lower_int_expr_list env state rest in
      Ok (prefix @ rest_prefix, expr :: rest, state)

and lower_ptr_expr env state expr =
  match expr with
  | Var name when is_pointer_name env name ->
      Ok ([], Var (ptr_block_name name), Var (ptr_offset_name name), state)
  | Var name ->
      Ok ([], Var name, Int 0, state)
  | Int n ->
      Ok ([], Int n, Int 0, state)
  | AddrOf name ->
      (match global_block_id env name with
      | Some block_id ->
          Ok ([], Int block_id, Int 0, state)
      | None ->
          fail "only address-of for integer globals is supported, got `&%s`" name)
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind, Int_kind ->
          let* prefix, block, offset, state = lower_ptr_expr env state left in
          let* delta_prefix, delta, state = lower_int_expr env state right in
          Ok (prefix @ delta_prefix, block, Add (offset, delta), state)
      | Int_kind, Pointer_kind ->
          let* delta_prefix, delta, state = lower_int_expr env state left in
          let* prefix, block, offset, state = lower_ptr_expr env state right in
          Ok (delta_prefix @ prefix, block, Add (offset, delta), state)
      | _ ->
          fail "unsupported pointer arithmetic expression")
  | FuncCall (name, args) when String.equal name "malloc" ->
      (match args with
      | [size_expr] ->
          let site = state.next_malloc_site in
          let state = { next_malloc_site = site + 1 } in
          let* prefix, size_expr, state = lower_int_expr env state size_expr in
          Ok
            ( prefix
              @ [ Assign (alloc_live_name site, Int 1)
                ; Assign (alloc_size_name site, size_expr)
                ]
            , Int (alloc_block_id env site)
            , Int 0
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
      let* prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (prefix @ right_prefix, Lt (left, right), state)
  | Le (left, right) ->
      let* prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (prefix @ right_prefix, Le (left, right), state)
  | Gt (left, right) ->
      let* prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      Ok (prefix @ right_prefix, Gt (left, right), state)
  | Ge (left, right) ->
      let* prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
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
  | Pointer_kind, _
  | _, Pointer_kind ->
      let* prefix, left_block, left_offset, state = lower_ptr_expr env state left in
      let* right_prefix, right_block, right_offset, state =
        lower_ptr_expr env state right
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
  | Int_kind, Int_kind ->
      let* prefix, left, state = lower_int_expr env state left in
      let* right_prefix, right, state = lower_int_expr env state right in
      let formula =
        if negated then Neq (left, right) else Eq (left, right)
      in
      Ok (prefix @ right_prefix, formula, state)

and lower_stmt env state stmt =
  match stmt with
  | Skip -> Ok (Skip, state)
  | Assign (name, rhs) ->
      if is_pointer_name env name then
        let* prefix, block, offset, state = lower_ptr_expr env state rhs in
        Ok
          ( seq_of_list
              (prefix
              @ [ Assign (ptr_block_name name, block)
                ; Assign (ptr_offset_name name, offset)
                ])
          , state )
      else
        let* prefix, rhs, state = lower_int_expr env state rhs in
        Ok (seq_of_list (prefix @ [ Assign (name, rhs) ]), state)
  | Store (ptr, value) ->
      let* ptr_prefix, block, offset, state = lower_ptr_expr env state ptr in
      let* value_prefix, value, state = lower_int_expr env state value in
      Ok
        ( seq_of_list
            (ptr_prefix
            @ value_prefix
            @ [ heap_guard_stmt
                  (valid_access_formula env block offset (Int 1))
                  [ Assign (memory_sink_name, value) ]
              ])
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
  | Assert cond ->
      let* prefix, cond, state = lower_bexpr env state cond in
      Ok (seq_of_list (prefix @ [ Assert cond ]), state)
  | Free ptr ->
      let* prefix, block, offset, state = lower_ptr_expr env state ptr in
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
      let* prefix, value, state = lower_int_expr env state value in
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
        | TInt | TVoid -> false)
      fn.params
  in
  if has_pointer_param then
    fail
      "pointer parameters in function `%s` are unsupported in this proof-of-concept"
      fn.name
  else
    match fn.return_type with
    | TPointer _ ->
        fail
          "pointer return type in function `%s` is unsupported in this proof-of-concept"
          fn.name
    | TInt | TVoid ->
        let init = alloc_init_stmts env.malloc_sites in
        let* body, state = lower_stmt env state fn.body in
        let body = seq_of_list (Assign (heap_ok_name, Int 1) :: init @ [ body ]) in
        Ok ({ fn with body }, state)

let lower_functions env state functions =
  let rec loop acc state = function
    | [] -> Ok (List.rev acc, state)
    | fn :: rest ->
        let* fn, state = lower_function env state fn in
        loop (fn :: acc) state rest
  in
  loop [] state functions

let lower_program program =
  if not (uses_memory_program program) then
    Ok program
  else
  let malloc_sites = count_malloc_program program in
  let env =
    {
      int_globals = program.globals;
      pointer_globals = program.pointer_globals;
      malloc_sites;
    }
  in
  let state = { next_malloc_site = 1 } in
  let* functions, state = lower_functions env state program.functions in
  let* main, _ = lower_function env state program.main in
  let extra_globals =
    pointer_shadow_globals program.pointer_globals
    @ alloc_globals malloc_sites
    @ [ memory_sink_name; heap_ok_name ]
  in
  Ok
    {
      program with
      globals = program.globals @ extra_globals;
      functions;
      main;
    }

let contract_env_of_program program =
  {
    int_globals = program.globals;
    pointer_globals = program.pointer_globals;
    malloc_sites = count_malloc_program program;
  }

let rec lower_contract_int_expr env expr =
  match expr with
  | Int _ as expr -> Ok expr
  | Var name when not (is_pointer_name env name) -> Ok (Var name)
  | Var name ->
      fail "pointer variable `%s` used where an integer contract expression was expected" name
  | AddrOf _ ->
      fail "address-of expression used where an integer contract expression was expected"
  | Deref _ ->
      fail "dereference is unsupported inside contract expressions"
  | Add (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Add (left, right))
  | Sub (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Sub (left, right))
  | Mul (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Mul (left, right))
  | Div (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Div (left, right))
  | Mod (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Mod (left, right))
  | FuncCall (name, args) ->
      let* args =
        match lower_contract_int_expr_list env args with
        | Ok args -> Ok args
        | Error _ as error -> error
      in
      Ok (FuncCall (name, args))

and lower_contract_int_expr_list env exprs =
  match exprs with
  | [] -> Ok []
  | expr :: rest ->
      let* expr = lower_contract_int_expr env expr in
      let* rest = lower_contract_int_expr_list env rest in
      Ok (expr :: rest)

and lower_contract_ptr_expr env expr =
  match expr with
  | Var name when is_pointer_name env name ->
      Ok (Var (ptr_block_name name), Var (ptr_offset_name name))
  | Int n -> Ok (Int n, Int 0)
  | AddrOf name ->
      (match global_block_id env name with
      | Some block_id -> Ok (Int block_id, Int 0)
      | None ->
          fail "only address-of for integer globals is supported in contracts, got `&%s`" name)
  | Add (left, right) ->
      (match expr_kind env left, expr_kind env right with
      | Pointer_kind, Int_kind ->
          let* block, offset = lower_contract_ptr_expr env left in
          let* delta = lower_contract_int_expr env right in
          Ok (block, Add (offset, delta))
      | Int_kind, Pointer_kind ->
          let* delta = lower_contract_int_expr env left in
          let* block, offset = lower_contract_ptr_expr env right in
          Ok (block, Add (offset, delta))
      | _ ->
          fail "unsupported pointer arithmetic expression in contract")
  | Var name ->
      fail "integer variable `%s` used where a pointer contract expression was expected" name
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

let allocated_formula env block offset =
  valid_access_formula env block offset (Int 1)

let is_live_formula env block =
  let global_cases =
    List.filter_map
      (fun name ->
        Option.map (fun block_id -> int_eq block (Int block_id)) (global_block_id env name))
      env.int_globals
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
      let* block, offset = lower_contract_ptr_expr env ptr in
      let* width = lower_contract_int_expr env width in
      Ok (valid_access_formula env block offset width)
  | "allocated", [ptr] ->
      let* block, offset = lower_contract_ptr_expr env ptr in
      Ok (allocated_formula env block offset)
  | "live", [ptr] ->
      let* block, _offset = lower_contract_ptr_expr env ptr in
      Ok (is_live_formula env block)
  | "can_free", [ptr] ->
      let* block, offset = lower_contract_ptr_expr env ptr in
      Ok (can_free_formula env block offset)
  | "same_block", [left; right] ->
      let* left_block, _ = lower_contract_ptr_expr env left in
      let* right_block, _ = lower_contract_ptr_expr env right in
      Ok (Eq (left_block, right_block))
  | "is_null", [ptr] ->
      let* block, offset = lower_contract_ptr_expr env ptr in
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
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Lt (left, right))
  | Le (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Le (left, right))
  | Gt (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Gt (left, right))
  | Ge (left, right) ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (Ge (left, right))

and lower_contract_equality_like env negated left right =
  match expr_kind env left, expr_kind env right with
  | Pointer_kind, _
  | _, Pointer_kind ->
      let* left_block, left_offset = lower_contract_ptr_expr env left in
      let* right_block, right_offset = lower_contract_ptr_expr env right in
      let formula = pointer_eq_formula left_block left_offset right_block right_offset in
      Ok (if negated then Not formula else formula)
  | Int_kind, Int_kind ->
      let* left = lower_contract_int_expr env left in
      let* right = lower_contract_int_expr env right in
      Ok (if negated then Neq (left, right) else Eq (left, right))
