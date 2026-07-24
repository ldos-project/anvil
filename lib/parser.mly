%{
open Ast

let fail fmt = Printf.ksprintf failwith fmt

let seq_of_list stmts =
  let stmts =
    List.concat_map
      (function
        | Seq inner -> inner
        | stmt -> [stmt])
      stmts
  in
  match stmts with
  | [] -> Skip
  | [stmt] -> stmt
  | _ -> Seq stmts

let bool_of_int = function
  | 0 -> False
  | _ -> True

let is_zero_float text =
  let stripped =
    if String.length text > 0
       && (text.[String.length text - 1] = 'f' || text.[String.length text - 1] = 'F')
    then
      String.sub text 0 (String.length text - 1)
    else
      text
  in
  try float_of_string stripped = 0.0 with
  | Failure _ -> false

let expect_zero_literal = function
  | Int 0
  | CharLit 0
  | BoolLit false ->
      ()
  | FloatLit text
  | DoubleLit text when is_zero_float text ->
      ()
  | expr ->
      fail "expected a zero literal in assumption form, got `%s`" (expr_to_c expr)

let expect_abort name =
  if String.equal name "abort" then ()
  else fail "expected `abort()`, got `%s()`" name

let bexpr_of_expr = function
  | Int n -> bool_of_int n
  | CharLit n -> bool_of_int n
  | BoolLit true -> True
  | BoolLit false -> False
  | FloatLit text
  | DoubleLit text when is_zero_float text ->
      False
  | FloatLit _
  | DoubleLit _ ->
      True
  | expr ->
      Neq (expr, Int 0)

let negate_expr = function
  | Int n -> Int (-n)
  | FloatLit value -> FloatLit ("-" ^ value)
  | DoubleLit value -> DoubleLit ("-" ^ value)
  | value -> Sub (Int 0, value)

let rec pointer_type base = function
  | 0 -> base
  | depth -> TPointer (pointer_type base (depth - 1))

let array_type element_type size =
  if size <= 0 then
    fail "array size must be positive, got %d" size;
  match element_type with
  | TInt | TFloat | TDouble | TChar | TBool | TRecord _ | TPointer _ ->
      TArray (element_type, size)
  | TVoid ->
      fail "arrays of `void` are unsupported"
  | TArray _ ->
      fail "nested arrays are unsupported in this proof-of-concept"
  | TReference _ | TConstReference _ ->
      fail "arrays of references are unsupported"

let ensure_quantified_type_supported c_type =
  match c_type with
  | TInt | TFloat | TDouble | TChar | TBool | TPointer _ ->
      c_type
  | TVoid | TRecord _ | TArray _ | TReference _ | TConstReference _ ->
      fail
        "quantified variables must have a scalar or pointer type, got `%s`"
        (c_type_to_c c_type)

let make_function ?contract ~name ~return_type ~params body =
  { name; return_type; params; locals = []; contract; body }

let make_global global_type global_name =
  { global_type; global_name }

let make_local_decl local_type local_name init =
  LocalDecl (make_global local_type local_name, init)

let record_field field_type field_name =
  { field_type; field_name }

let record_field_tail base stars field_name = function
  | `Scalar ->
      record_field (pointer_type base stars) field_name
  | `Array size ->
      record_field (array_type (pointer_type base stars) size) field_name

let assignment_stmt lhs rhs =
  match lhs with
  | Var name -> Assign (name, rhs)
  | Index (base, index) -> ArrayAssign (base, index, rhs)
  | Field (base, field) -> FieldAssign (base, field, rhs)
  | _ ->
      fail "unsupported assignment target `%s`" (expr_to_c lhs)

let compound_assignment_stmt combine lhs rhs =
  assignment_stmt lhs (combine lhs rhs)

let compound_store_stmt combine ptr rhs =
  Store (ptr, combine (Deref ptr) rhs)

let call_stmt name args =
  expect_abort name;
  if args <> [] then
    fail "expected `abort()` without arguments";
  Assert (Source_assert, False)

let stmt_of_if_without_else cond then_branch =
  match cond, then_branch with
  | Not premise, Block [ Return None ] ->
      Assume premise
  | Not premise, Block [ Return (Some value) ] ->
      expect_zero_literal value;
      Assume premise
  | Not premise, Block [ Assert (Source_assert, False) ] ->
      Assert (Source_assert, premise)
  | _ ->
      If (cond, then_branch, Skip)

let raw_qualified_name parts =
  String.concat raw_namespace_separator parts

let qualify_decl_name namespace name =
  namespace_qualify namespace name

let make_method_function ~class_name ~name ~return_type ~params body =
  make_function
    ~name:(class_method_name class_name name)
    ~return_type
    ~params:
      ({ param_type = TPointer (TRecord class_name); param_name = Some method_this_name }
       :: params)
    body

type class_member =
  | Class_field of field_def
  | Class_method of function_def

type top_item =
  | Top_record of record_def
  | Top_global of global_def
  | Top_function of function_def
  | Top_main of function_def

type top_group_builder = string list -> top_item list

let build_class class_name members =
  let fields_rev, methods_rev =
    List.fold_left
      (fun (fields_rev, methods_rev) -> function
        | Class_field field ->
            field :: fields_rev, methods_rev
        | Class_method method_fn ->
            fields_rev, Top_function method_fn :: methods_rev)
      ([], [])
      members
  in
  Top_record { record_name = class_name; fields = List.rev fields_rev }
  :: List.rev methods_rev

(* ----------------------------------------------------------------------- *)
(* Evolve-block desugaring.                                                  *)
(*                                                                           *)
(* The evolve block the LLM writes (listener attachments + a `score_fn`      *)
(* lambda) uses value-level constructs the core language lacks: comparisons  *)
(* and `&&`/`||`/`!` used as values, the ternary `?:`, `static_cast`,        *)
(* bounded `for`, and `{a, b}` initializer lists as call arguments.          *)
(*                                                                           *)
(* Rather than grow the core AST (and every pass that matches on it), the    *)
(* evolve grammar desugars all of these into the EXISTING `expr`/`stmt`      *)
(* nodes. Boolean/comparison/ternary results become opaque intrinsic         *)
(* `FuncCall`s, so `strict_syntax` still recurses into every operand and the *)
(* memory-safety gate sees the whole program. Unsafe constructs (`*`, `&`,   *)
(* `[]`, `->`) are kept as their real AST nodes (`Deref`/`AddrOf`/`Index`/   *)
(* `Field (Deref _, _)`) precisely so strict mode rejects them with a clear  *)
(* message instead of a generic parse error.                                 *)
(* ----------------------------------------------------------------------- *)

let anvil_intrinsic name args = FuncCall (name, args)

let val_cmp op left right =
  let name =
    match op with
    | `Eq -> "__anvil_eq"
    | `Neq -> "__anvil_neq"
    | `Lt -> "__anvil_lt"
    | `Le -> "__anvil_le"
    | `Gt -> "__anvil_gt"
    | `Ge -> "__anvil_ge"
  in
  anvil_intrinsic name [left; right]

let val_and left right = anvil_intrinsic "__anvil_and" [left; right]
let val_or left right = anvil_intrinsic "__anvil_or" [left; right]
let val_not inner = anvil_intrinsic "__anvil_not" [inner]
let val_ite cond then_value else_value =
  anvil_intrinsic "__anvil_ite" [cond; then_value; else_value]
let val_list items = anvil_intrinsic "__anvil_list" items

(* A value used where the core language wants a `bexpr` (if/while/for
   conditions). Desugaring conditions to `Neq (e, 0)` keeps the entire
   condition expression visible to the strict scan. *)
let value_as_cond expr = Neq (expr, Int 0)

let zero_of_type = function
  | TDouble -> DoubleLit "0.0"
  | TFloat -> FloatLit "0.0f"
  | TChar -> CharLit 0
  | TBool -> BoolLit false
  | _ -> Int 0

(* Locals are restricted to the three scalar types the DSL documents. Anvil has
   no `int64_t` keyword, so an unknown type name arrives here as `TRecord` --
   `int64_t`, `uint32_t`, or a typo alike -- and must be rejected at the gate
   rather than in the C++ build. Parameters are parsed by `evolve_param_list`
   and are unaffected, so `int64_t obj_id` still works. *)
let evolve_local_type local_type name =
  match local_type with
  | TInt | TDouble | TBool -> local_type
  | TRecord type_name ->
      fail
        "local `%s` has type `%s`, which is not a scalar type; evolve-block \
         locals must be `int`, `double` or `bool` (`int64_t` is only for the \
         score function's object-id parameter)"
        name type_name
  | other ->
      fail
        "local `%s` has type `%s`; evolve-block locals must be `int`, `double` \
         or `bool`"
        name (c_type_to_c other)

(* An uninitialized scalar local is memory-safe (no pointer/heap involved),
   so the gate admits it by supplying a synthetic zero initializer. This is
   only used for the safety gate, which does not reason about reads of
   uninitialized values. *)
let evolve_local_decl local_type name init =
  let local_type = evolve_local_type local_type name in
  let init =
    match init with
    | Some _ -> init
    | None -> Some (zero_of_type local_type)
  in
  make_local_decl local_type name init

(* An expression evaluated for effect (e.g. a listener attachment
   `store_cfg.add_listeners(...)`). The core language has no expression
   statement, so bind it to a discard name; strict still scans the
   expression. *)
let evolve_effect_stmt expr = Assign ("__anvil_discard", expr)

let evolve_compound combine lhs rhs = assignment_stmt lhs (combine lhs rhs)

(* Evolve-block loops must be canonical counted loops, checked here because
   `evolve_for` desugars to `While` and the shape is unrecoverable afterwards:

     for (int i = <literal>; i <  <literal>; i++)   (also <=, counting up)
     for (int i = <literal>; i >  <literal>; i--)   (also >=, counting down)

   with the body forbidden from assigning to `i`. The induction variable then
   moves one step toward a fixed bound every iteration and nothing else can
   move it, so the loop terminates by construction. *)

(* Endpoint magnitude keeps the counter clear of the integer limits, where the
   final `i++` wraps and makes the condition true again, and keeps both values
   exactly representable in a `double` counter. The trip cap is a per-loop cost
   bound: scoring runs on every eviction, and real heuristics iterate over a
   listener window of 8-18. It does not bound a loop nest -- nested counted
   loops multiply, and each is still individually terminating, which is what
   the gate promises. *)
let loop_literal_limit = 1 lsl 30
let loop_max_trip = 4096

let for_induction_var = function
  | LocalDecl ({ global_name; _ }, Some (Int value)) -> Some (global_name, value)
  | Assign (name, Int value) -> Some (name, value)
  | _ -> None

(* Exact iteration count for a `+/-1` counted loop with literal endpoints. *)
let for_trip_count op ~init ~bound =
  match op with
  | `Lt -> if init >= bound then 0 else bound - init
  | `Le -> if init > bound then 0 else bound - init + 1
  | `Gt -> if init <= bound then 0 else init - bound
  | `Ge -> if init < bound then 0 else init - bound + 1
  (* `evolve_for` rejects equality conditions before reaching this point. *)
  | `Eq | `Neq -> assert false

let rec stmt_assigns_var name stmt =
  match stmt with
  | Assign (target, _) -> String.equal target name
  | LocalDecl ({ global_name; _ }, _) -> String.equal global_name name
  | Block stmts | Seq stmts -> List.exists (stmt_assigns_var name) stmts
  | If (_, then_branch, else_branch) ->
      stmt_assigns_var name then_branch || stmt_assigns_var name else_branch
  | While (_, _, body) -> stmt_assigns_var name body
  | Skip | Break | Continue | Store _ | ArrayAssign _ | FieldAssign _
  | Assume _ | Assert _ | Free _ | Return _ ->
      false

let evolve_for ~init ~cond ~step body =
  let op, cond_left, cond_right = cond in
  let name, init_value =
    match for_induction_var init with
    | Some pair -> pair
    | None ->
        fail
          "strict for-loops require an induction variable initialised to an \
           integer literal, e.g. `for (int i = 0; i < 8; i++)`"
  in
  let bound_value =
    match cond_left, cond_right with
    | Var v, Int bound when String.equal v name -> bound
    | _ ->
        fail
          "strict for-loops require the condition to compare `%s` against an \
           integer literal, e.g. `%s < 8`, got `%s ? %s`"
          name name (expr_to_c cond_left) (expr_to_c cond_right)
  in
  List.iter
    (fun (what, value) ->
      if abs value > loop_literal_limit then
        fail
          "strict for-loop %s %d is too large: both endpoints must satisfy \
           |value| <= %d so the counter cannot overflow or lose precision"
          what value loop_literal_limit)
    [ ("initialiser", init_value); ("bound", bound_value) ];
  let expected_step, shown_step =
    match op with
    | `Lt | `Le -> Add (Var name, Int 1), name ^ "++"
    | `Gt | `Ge -> Sub (Var name, Int 1), name ^ "--"
    | `Eq | `Neq ->
        fail
          "strict for-loops require a `<`, `<=`, `>` or `>=` condition on `%s`; \
           an equality test gives no termination argument"
          name
  in
  (match step, expected_step with
  | Assign (target, Add (Var v, Int 1)), Add (Var _, Int 1)
    when String.equal target name && String.equal v name ->
      ()
  | Assign (target, Sub (Var v, Int 1)), Sub (Var _, Int 1)
    when String.equal target name && String.equal v name ->
      ()
  | _ ->
      fail
        "strict for-loops require the step `%s` so it matches the condition \
         direction and provably approaches the bound"
        shown_step);
  if stmt_assigns_var name body then
    fail
      "strict for-loops forbid assigning to the induction variable `%s` inside \
       the loop body; that breaks the termination argument"
      name;
  let trips = for_trip_count op ~init:init_value ~bound:bound_value in
  if trips > loop_max_trip then
    fail
      "strict for-loop runs %d iterations, over the limit of %d; the scoring \
       function is called on every eviction, so keep loops short"
      trips loop_max_trip;
  let cond = val_cmp op cond_left cond_right in
  seq_of_list [ init; While (None, value_as_cond cond, seq_of_list [ body; step ]) ]

type evolve_item =
  | Evolve_effect of stmt
  | Evolve_score of function_def

(* Assemble the parsed evolve block into a whole program: the `score_fn`
   becomes a top-level function and the loose listener statements become the
   body of a synthesized `main`. A trivial `score_fn` is synthesized if the
   block declares none, so listener-only fragments are still well-formed and
   gated. *)
let build_evolve_program items =
  let effects_rev, score_fns_rev =
    List.fold_left
      (fun (effects_rev, score_fns_rev) -> function
        | None -> effects_rev, score_fns_rev
        | Some (Evolve_effect stmt) -> stmt :: effects_rev, score_fns_rev
        | Some (Evolve_score fn) -> effects_rev, fn :: score_fns_rev)
      ([], [])
      items
  in
  let effects = List.rev effects_rev in
  let score_fns = List.rev score_fns_rev in
  let main =
    make_function ~name:"main" ~return_type:TInt ~params:[]
      (Block (effects @ [ Return (Some (Int 0)) ]))
  in
  let functions =
    match score_fns with
    | [] ->
        [ make_function ~name:"score_fn" ~return_type:TDouble ~params:[]
            (Block [ Return (Some (DoubleLit "0.0")) ]) ]
    | _ -> score_fns
  in
  { imports = []; records = []; globals = []; functions; main }

let build_program items =
  let rec loop records_rev globals_rev functions_rev main = function
    | [] ->
        let main =
          match main with
          | Some main -> main
          | None -> fail "missing `main` definition"
        in
        {
          imports = [];
          records = List.rev records_rev;
          globals = List.rev globals_rev;
          functions = List.rev functions_rev;
          main;
        }
    | Top_record record :: rest ->
        loop (record :: records_rev) globals_rev functions_rev main rest
    | Top_global global :: rest ->
        loop records_rev (global :: globals_rev) functions_rev main rest
    | Top_function fn :: rest ->
        loop records_rev globals_rev (fn :: functions_rev) main rest
    | Top_main fn :: rest ->
        (match main with
        | Some _ -> fail "multiple `main` definitions"
        | None ->
            loop records_rev globals_rev functions_rev (Some fn) rest)
  in
  loop [] [] [] None items
%}

%token <int> INT_LIT
%token <string> FLOAT_LIT
%token <string> DOUBLE_LIT
%token <int> CHAR_LIT
%token <string> IDENT
%token INT_KW FLOAT_KW DOUBLE_KW CHAR_KW BOOL_KW CONST_KW MAIN_KW VOID_KW STRUCT_KW CLASS_KW NAMESPACE_KW IF_KW ELSE_KW WHILE_KW RETURN_KW FREE_KW TRUE_KW FALSE_KW FORALL_KW
%token AUTO_KW STATIC_CAST_KW FOR_KW BREAK_KW CONTINUE_KW
%token <string> STDFUNCTION_TYPE
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET SEMI COMMA AMP DOT ARROW SCOPE
%token QUESTION COLON INCR DECR STAREQ SLASHEQ
%token PLUS MINUS STAR SLASH PERCENT
%token ASSIGN PLUSEQ MINUSEQ EQEQ NEQ LT LE GT GE NOT AND OR IMPLIES
%token EOF

%right IMPLIES
%left OR
%left AND

%start <Ast.program> program
%start <Ast.program> evolve_program
%start <Ast.expr> contract_expr_eof
%start <Ast.bexpr> contract_bexpr_eof
%start <Ast.bexpr> bexpr_eof

%%

contract_expr_eof:
  | value = contract_expr EOF
      { value }

contract_bexpr_eof:
  | value = contract_bexpr EOF
      { value }

bexpr_eof:
  | value = bexpr EOF
      { value }

scalar_type:
  | INT_KW
      { TInt }
  | FLOAT_KW
      { TFloat }
  | DOUBLE_KW
      { TDouble }
  | CHAR_KW
      { TChar }
  | BOOL_KW
      { TBool }

struct_type:
  | STRUCT_KW name = qualified_ident
      { TRecord name }

nonvoid_type:
  | base = scalar_type
      { base }
  | base = struct_type
      { base }
  | name = qualified_ident
      { TRecord name }

qualified_ident:
  | first = IDENT rest = qualified_ident_tail
      { raw_qualified_name (first :: rest) }

qualified_ident_tail:
  | { [] }
  | SCOPE next = IDENT rest = qualified_ident_tail
      { next :: rest }

contract_expr:
  | value = contract_add_expr
      { value }

contract_add_expr:
  | value = contract_mul_expr
      { value }
  | left = contract_add_expr PLUS right = contract_mul_expr
      { Add (left, right) }
  | left = contract_add_expr MINUS right = contract_mul_expr
      { Sub (left, right) }

contract_mul_expr:
  | value = contract_unary_expr
      { value }
  | left = contract_mul_expr STAR right = contract_unary_expr
      { Mul (left, right) }
  | left = contract_mul_expr SLASH right = contract_unary_expr
      { Div (left, right) }
  | left = contract_mul_expr PERCENT right = contract_unary_expr
      { Mod (left, right) }

contract_unary_expr:
  | value = contract_postfix_expr
      { value }
  | AMP value = contract_postfix_expr
      { AddrOf value }
  | STAR value = contract_unary_expr
      { Deref value }
  | MINUS value = contract_unary_expr
      { negate_expr value }

contract_postfix_expr:
  | value = contract_primary_expr
      { value }
  | base = contract_postfix_expr LBRACKET index = contract_expr RBRACKET
      { Index (base, index) }

contract_nonparen_expr:
  | value = contract_nonparen_add_expr
      { value }

contract_nonparen_add_expr:
  | value = contract_nonparen_mul_expr
      { value }
  | left = contract_nonparen_add_expr PLUS right = contract_mul_expr
      { Add (left, right) }
  | left = contract_nonparen_add_expr MINUS right = contract_mul_expr
      { Sub (left, right) }

contract_nonparen_mul_expr:
  | value = contract_nonparen_unary_expr
      { value }
  | left = contract_nonparen_mul_expr STAR right = contract_unary_expr
      { Mul (left, right) }
  | left = contract_nonparen_mul_expr SLASH right = contract_unary_expr
      { Div (left, right) }
  | left = contract_nonparen_mul_expr PERCENT right = contract_unary_expr
      { Mod (left, right) }

contract_nonparen_unary_expr:
  | value = contract_nonparen_postfix_expr
      { value }
  | AMP value = contract_postfix_expr
      { AddrOf value }
  | STAR value = contract_unary_expr
      { Deref value }
  | MINUS value = contract_unary_expr
      { negate_expr value }

contract_primary_expr:
  | n = INT_LIT
      { Int n }
  | value = FLOAT_LIT
      { FloatLit value }
  | value = DOUBLE_LIT
      { DoubleLit value }
  | value = CHAR_LIT
      { CharLit value }
  | TRUE_KW
      { BoolLit true }
  | FALSE_KW
      { BoolLit false }
  | name = qualified_ident LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { FuncCall (name, args) }
  | name = qualified_ident
      { Var name }
  | LPAREN value = contract_expr RPAREN
      { value }

contract_nonparen_postfix_expr:
  | value = contract_nonparen_primary_expr
      { value }
  | base = contract_nonparen_postfix_expr LBRACKET index = contract_expr RBRACKET
      { Index (base, index) }

contract_nonparen_primary_expr:
  | n = INT_LIT
      { Int n }
  | value = FLOAT_LIT
      { FloatLit value }
  | value = DOUBLE_LIT
      { DoubleLit value }
  | value = CHAR_LIT
      { CharLit value }
  | TRUE_KW
      { BoolLit true }
  | FALSE_KW
      { BoolLit false }
  | name = qualified_ident LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { FuncCall (name, args) }
  | name = qualified_ident
      { Var name }

contract_quantified_type:
  | base = nonvoid_type stars = pointer_stars
      { ensure_quantified_type_supported (pointer_type base stars) }
  | VOID_KW STAR stars = pointer_stars
      { ensure_quantified_type_supported (pointer_type TVoid (stars + 1)) }

contract_quantified_binding:
  | quant_type = contract_quantified_type name = IDENT
      { { quant_type; quant_name = name } }

contract_bexpr:
  | value = contract_implies_bexpr
      { value }

contract_implies_bexpr:
  | value = contract_or_bexpr
      %prec IMPLIES
      { value }
  | left = contract_or_bexpr IMPLIES right = contract_implies_bexpr
      { Or (Not left, right) }

contract_or_bexpr:
  | value = contract_and_bexpr
      %prec OR
      { value }
  | left = contract_or_bexpr OR right = contract_and_bexpr
      { Or (left, right) }

contract_and_bexpr:
  | value = contract_not_bexpr
      { value }
  | left = contract_and_bexpr AND right = contract_not_bexpr
      { And (left, right) }

contract_not_bexpr:
  | value = contract_atom_bexpr
      { value }
  | FORALL_KW LPAREN bindings = separated_nonempty_list(COMMA, contract_quantified_binding) RPAREN DOT value = contract_bexpr
      { Forall (bindings, value) }
  | NOT value = contract_not_bexpr
      { Not value }

contract_cmp_tail:
  | ASSIGN right = contract_expr
      { fun left -> Eq (left, right) }
  | EQEQ right = contract_expr
      { fun left -> Eq (left, right) }
  | NEQ right = contract_expr
      { fun left -> Neq (left, right) }
  | LT right = contract_expr
      { fun left -> Lt (left, right) }
  | LE right = contract_expr
      { fun left -> Le (left, right) }
  | GT right = contract_expr
      { fun left -> Gt (left, right) }
  | GE right = contract_expr
      { fun left -> Ge (left, right) }
  |
      { fun left -> bexpr_of_expr left }

contract_atom_bexpr:
  | LPAREN value = contract_bexpr RPAREN
      { value }
  | left = contract_nonparen_expr tail = contract_cmp_tail
      { tail left }

program:
  | items = list(top_group) EOF
      { build_program (List.concat_map (fun build -> build []) items) }

top_group:
  | NAMESPACE_KW name = qualified_ident LBRACE items = list(top_group) RBRACE
      {
        fun namespace ->
          let nested_namespace =
            namespace @ split_on_substring ~sep:raw_namespace_separator name
          in
          List.concat_map (fun build -> build nested_namespace) items
      }
  | STRUCT_KW name = IDENT LBRACE fields = record_field_list RBRACE SEMI
      {
        fun namespace ->
          [ Top_record
              {
                record_name = qualify_decl_name namespace name;
                fields;
              }
          ]
      }
  | CLASS_KW name = IDENT LBRACE members = class_member_list RBRACE SEMI
      {
        fun namespace ->
          let class_name = qualify_decl_name namespace name in
          build_class class_name (List.map (fun build -> build class_name) members)
      }
  | INT_KW MAIN_KW LPAREN VOID_KW RPAREN body = block
      {
        fun namespace ->
          if namespace <> [] then
            fail "`main` must be declared at global scope";
          [ Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) ]
      }
  | INT_KW MAIN_KW LPAREN RPAREN body = block
      {
        fun namespace ->
          if namespace <> [] then
            fail "`main` must be declared at global scope";
          [ Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) ]
      }
  | base = nonvoid_type stars = pointer_stars name = IDENT LPAREN params = param_list RPAREN SEMI
      {
        ignore base;
        ignore stars;
        ignore name;
        ignore params;
        fun _namespace -> []
      }
  | base = nonvoid_type stars = pointer_stars name = IDENT tail = top_tail
      {
        fun namespace ->
          [ tail base stars (qualify_decl_name namespace name) ]
      }
  | VOID_KW stars = pointer_stars name = IDENT LPAREN params = param_list RPAREN SEMI
      {
        ignore stars;
        ignore name;
        ignore params;
        fun _namespace -> []
      }
  | VOID_KW stars = pointer_stars name = IDENT LPAREN params = param_list RPAREN body = block
      {
        fun namespace ->
          [ Top_function
              (make_function
                 ~name:(qualify_decl_name namespace name)
                 ~return_type:(pointer_type TVoid stars)
                 ~params
                 body)
          ]
      }

class_member_list:
  | { [] }
  | member = class_member_decl rest = class_member_list
      { member :: rest }

class_member_decl:
  | base = nonvoid_type stars = pointer_stars member_name = IDENT tail = class_member_nonvoid_tail
      { fun class_name -> tail class_name base stars member_name }
  | VOID_KW stars = pointer_stars member_name = IDENT tail = class_member_void_tail
      { fun class_name -> tail class_name stars member_name }

class_member_nonvoid_tail:
  | SEMI
      {
        fun _class_name base stars member_name ->
          Class_field (record_field_tail base stars member_name `Scalar)
      }
  | LBRACKET size = INT_LIT RBRACKET SEMI
      {
        fun _class_name base stars member_name ->
          Class_field (record_field_tail base stars member_name (`Array size))
      }
  | LPAREN params = param_list RPAREN body = block
      {
        fun class_name base stars member_name ->
          Class_method
            (make_method_function
               ~class_name
               ~name:member_name
               ~return_type:(pointer_type base stars)
               ~params
               body)
      }

class_member_void_tail:
  | SEMI
      {
        fun _class_name stars member_name ->
          if stars = 0 then
            fail "fields of type `void` are unsupported";
          Class_field (record_field (pointer_type TVoid stars) member_name)
      }
  | LPAREN params = param_list RPAREN body = block
      {
        fun class_name stars member_name ->
          Class_method
            (make_method_function
               ~class_name
               ~name:member_name
               ~return_type:(pointer_type TVoid stars)
               ~params
               body)
      }

record_field_list:
  | { [] }
  | field = record_field_decl rest = record_field_list
      { field :: rest }

record_field_decl:
  | base = nonvoid_type stars = pointer_stars field_name = IDENT tail = record_field_nonvoid_tail
      { tail base stars field_name }
  | VOID_KW STAR stars = pointer_stars field_name = IDENT SEMI
      { record_field (pointer_type TVoid (stars + 1)) field_name }

record_field_nonvoid_tail:
  | SEMI
      {
        fun base stars field_name ->
          record_field_tail base stars field_name `Scalar
      }
  | LBRACKET size = INT_LIT RBRACKET SEMI
      {
        fun base stars field_name ->
          record_field_tail base stars field_name (`Array size)
      }

top_tail:
  | SEMI
      {
        fun base stars name ->
          Top_global (make_global (pointer_type base stars) name)
      }
  | LBRACKET size = INT_LIT RBRACKET SEMI
      {
        fun base stars name ->
          if stars <> 0 then
            fail "array globals with pointer element types are unsupported";
          Top_global (make_global (array_type base size) name)
      }
  | LPAREN params = param_list RPAREN body = block
      {
        fun base stars name ->
          Top_function
            (make_function ~name ~return_type:(pointer_type base stars) ~params body)
      }

pointer_stars:
  | { 0 }
  | STAR rest = pointer_stars
      { 1 + rest }

param_list:
  | { [] }
  | VOID_KW
      { [] }
  | first = named_param rest = param_tail
      { first :: rest }

param_tail:
  | { [] }
  | COMMA next = named_param rest = param_tail
      { next :: rest }

named_param:
  | base = nonvoid_type stars = pointer_stars name = IDENT
      { { param_type = pointer_type base stars; param_name = Some name } }
  | base = nonvoid_type stars = pointer_stars AMP name = IDENT
      { { param_type = TReference (pointer_type base stars); param_name = Some name } }
  | CONST_KW base = nonvoid_type stars = pointer_stars AMP name = IDENT
      { { param_type = TConstReference (pointer_type base stars); param_name = Some name } }
  | VOID_KW STAR stars = pointer_stars name = IDENT
      { { param_type = pointer_type TVoid (stars + 1); param_name = Some name } }

stmt_list:
  | { [] }
  | stmt = stmt rest = stmt_list
      { stmt :: rest }

block:
  | LBRACE stmts = stmt_list RBRACE
      { Block stmts }

local_decl_tail:
  | SEMI
      {
        fun base stars name ->
          make_local_decl (pointer_type base stars) name None
      }
  | ASSIGN init = expr SEMI
      {
        fun base stars name ->
          make_local_decl (pointer_type base stars) name (Some init)
      }
  | LBRACKET size = INT_LIT RBRACKET SEMI
      {
        fun base stars name ->
          if stars <> 0 then
            fail "array locals with pointer element types are unsupported";
          make_local_decl (array_type base size) name None
      }

local_void_decl_tail:
  | SEMI
      {
        fun stars name ->
          make_local_decl (pointer_type TVoid (stars + 1)) name None
      }
  | ASSIGN init = expr SEMI
      {
        fun stars name ->
          make_local_decl (pointer_type TVoid (stars + 1)) name (Some init)
      }

stmt:
  | SEMI
      { Skip }
  | body = block
      { body }
  | base = nonvoid_type stars = pointer_stars name = IDENT tail = local_decl_tail
      { tail base stars name }
  | VOID_KW STAR stars = pointer_stars name = IDENT tail = local_void_decl_tail
      { tail stars name }
  | lhs = postfix_expr ASSIGN rhs = expr SEMI
      { assignment_stmt lhs rhs }
  | lhs = postfix_expr PLUSEQ rhs = expr SEMI
      { compound_assignment_stmt (fun left right -> Add (left, right)) lhs rhs }
  | lhs = postfix_expr MINUSEQ rhs = expr SEMI
      { compound_assignment_stmt (fun left right -> Sub (left, right)) lhs rhs }
  | STAR lhs = expr ASSIGN rhs = expr SEMI
      { Store (lhs, rhs) }
  | STAR lhs = expr PLUSEQ rhs = expr SEMI
      { compound_store_stmt (fun left right -> Add (left, right)) lhs rhs }
  | STAR lhs = expr MINUSEQ rhs = expr SEMI
      { compound_store_stmt (fun left right -> Sub (left, right)) lhs rhs }
  | name = qualified_ident LPAREN args = separated_list(COMMA, expr) RPAREN SEMI
      { call_stmt name args }
  | RETURN_KW value = option(expr) SEMI
      { Return value }
  | FREE_KW LPAREN ptr = expr RPAREN SEMI
      { Free ptr }
  | IF_KW LPAREN cond = bexpr RPAREN then_branch = block ELSE_KW else_branch = block
      { If (cond, then_branch, else_branch) }
  | IF_KW LPAREN cond = bexpr RPAREN then_branch = block
      { stmt_of_if_without_else cond then_branch }
  | WHILE_KW LPAREN cond = bexpr RPAREN body = block
      { While (None, cond, body) }

bexpr:
  | value = or_bexpr
      { value }

or_bexpr:
  | value = and_bexpr
      { value }
  | left = or_bexpr OR right = and_bexpr
      { Or (left, right) }

and_bexpr:
  | value = not_bexpr
      { value }
  | left = and_bexpr AND right = not_bexpr
      { And (left, right) }

not_bexpr:
  | value = atom_bexpr
      { value }
  | NOT inner = not_bexpr
      { Not inner }

bexpr_tail:
  | EQEQ right = expr
      { fun left -> Eq (left, right) }
  | NEQ right = expr
      { fun left -> Neq (left, right) }
  | LT right = expr
      { fun left -> Lt (left, right) }
  | LE right = expr
      { fun left -> Le (left, right) }
  | GT right = expr
      { fun left -> Gt (left, right) }
  | GE right = expr
      { fun left -> Ge (left, right) }
  |
      { fun left -> bexpr_of_expr left }

atom_bexpr:
  | LPAREN value = bexpr RPAREN
      { value }
  | left = nonparen_expr tail = bexpr_tail
      { tail left }

expr:
  | value = add_expr
      { value }

add_expr:
  | value = mul_expr
      { value }
  | left = add_expr PLUS right = mul_expr
      { Add (left, right) }
  | left = add_expr MINUS right = mul_expr
      { Sub (left, right) }

mul_expr:
  | value = unary_expr
      { value }
  | left = mul_expr STAR right = unary_expr
      { Mul (left, right) }
  | left = mul_expr SLASH right = unary_expr
      { Div (left, right) }
  | left = mul_expr PERCENT right = unary_expr
      { Mod (left, right) }

unary_expr:
  | value = postfix_expr
      { value }
  | MINUS value = unary_expr
      { negate_expr value }
  | AMP value = postfix_expr
      { AddrOf value }
  | STAR value = unary_expr
      { Deref value }

nonparen_expr:
  | value = nonparen_add_expr
      { value }

nonparen_add_expr:
  | value = nonparen_mul_expr
      { value }
  | left = nonparen_add_expr PLUS right = mul_expr
      { Add (left, right) }
  | left = nonparen_add_expr MINUS right = mul_expr
      { Sub (left, right) }

nonparen_mul_expr:
  | value = nonparen_unary_expr
      { value }
  | left = nonparen_mul_expr STAR right = unary_expr
      { Mul (left, right) }
  | left = nonparen_mul_expr SLASH right = unary_expr
      { Div (left, right) }
  | left = nonparen_mul_expr PERCENT right = unary_expr
      { Mod (left, right) }

nonparen_unary_expr:
  | value = nonparen_postfix_expr
      { value }
  | MINUS value = unary_expr
      { negate_expr value }
  | AMP value = postfix_expr
      { AddrOf value }
  | STAR value = unary_expr
      { Deref value }

nonparen_postfix_expr:
  | value = nonparen_primary_expr
      { value }
  | base = nonparen_postfix_expr LBRACKET index = expr RBRACKET
      { Index (base, index) }
  | base = nonparen_postfix_expr DOT method_name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (method_dot_call_name method_name, base :: args) }
  | base = nonparen_postfix_expr ARROW method_name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (method_arrow_call_name method_name, base :: args) }
  | base = nonparen_postfix_expr DOT field = IDENT
      { Field (base, field) }
  | base = nonparen_postfix_expr ARROW field = IDENT
      { Field (Deref base, field) }

postfix_expr:
  | value = primary_expr
      { value }
  | base = postfix_expr LBRACKET index = expr RBRACKET
      { Index (base, index) }
  | base = postfix_expr DOT method_name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (method_dot_call_name method_name, base :: args) }
  | base = postfix_expr ARROW method_name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (method_arrow_call_name method_name, base :: args) }
  | base = postfix_expr DOT field = IDENT
      { Field (base, field) }
  | base = postfix_expr ARROW field = IDENT
      { Field (Deref base, field) }

primary_expr:
  | n = INT_LIT
      { Int n }
  | value = FLOAT_LIT
      { FloatLit value }
  | value = DOUBLE_LIT
      { DoubleLit value }
  | value = CHAR_LIT
      { CharLit value }
  | TRUE_KW
      { BoolLit true }
  | FALSE_KW
      { BoolLit false }
  | name = qualified_ident LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (name, args) }
  | name = qualified_ident
      { Var name }
  | LPAREN value = expr RPAREN
      { value }

nonparen_primary_expr:
  | n = INT_LIT
      { Int n }
  | value = FLOAT_LIT
      { FloatLit value }
  | value = DOUBLE_LIT
      { DoubleLit value }
  | value = CHAR_LIT
      { CharLit value }
  | TRUE_KW
      { BoolLit true }
  | FALSE_KW
      { BoolLit false }
  | name = qualified_ident LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (name, args) }
  | name = qualified_ident
      { Var name }

(* ======================================================================= *)
(* Evolve-block grammar.                                                     *)
(*                                                                           *)
(* A separate start symbol with its own value-expression and statement       *)
(* nonterminals (all prefixed `val_`/`evolve_`). It is reachable only from   *)
(* `evolve_program`, so it cannot perturb the core `program` grammar. Every  *)
(* production desugars into the existing AST (see the header helpers), so no *)
(* downstream pass changes. The grammar is intentionally permissive about    *)
(* SAFE constructs and preserves UNSAFE ones (`*`,`&`,`[]`,`->`,arrays) as   *)
(* their real AST nodes so `--strict` rejects them precisely.                *)
(* ======================================================================= *)

evolve_program:
  | items = list(evolve_item) EOF
      { build_evolve_program items }

(* Each top-level item is either the score-function definition or a statement
   evaluated for effect (a listener attachment). `None` is an empty `;`. *)
evolve_item:
  | score = evolve_score_fn
      { Some (Evolve_score score) }
  | stmt = evolve_toplevel_stmt
      { Some (Evolve_effect stmt) }

(* The score function in any of the shapes the demo emits:
     auto score_fn = [&](params) -> double { body };
     std::function<...> score_fn = [&](params) -> double { body };
   The `double score_fn(params) { body }` plain-function form is handled by
   evolve_toplevel_stmt's leading-type case is NOT — it is parsed here so the
   block is treated as a function body. *)
evolve_score_fn:
  | AUTO_KW name = IDENT ASSIGN body = evolve_lambda SEMI
      { let (return_type, params, block) = body in
        make_function ~name ~return_type ~params block }
  | STDFUNCTION_TYPE name = IDENT ASSIGN body = evolve_lambda SEMI
      { let (return_type, params, block) = body in
        make_function ~name ~return_type ~params block }
  | return_type = scalar_type name = IDENT LPAREN params = evolve_param_list RPAREN block = evolve_block
      { make_function ~name ~return_type ~params block }

evolve_lambda:
  | LBRACKET AMP RBRACKET LPAREN params = evolve_param_list RPAREN ARROW return_type = evolve_ret_type block = evolve_block
      { (return_type, params, block) }
  | LBRACKET RBRACKET LPAREN params = evolve_param_list RPAREN ARROW return_type = evolve_ret_type block = evolve_block
      { (return_type, params, block) }

(* Top-level statements in the evolve block are listener attachments (method
   calls evaluated for effect) and empty `;`. Anything richer belongs inside
   the score function. *)
evolve_toplevel_stmt:
  | SEMI
      { Skip }
  | expr = val_expr SEMI
      { evolve_effect_stmt expr }

(* The feature_store parameter is passed by value here; the C++ build restores
   the reference via a `#define`. Anvil accepts a leading `const` on the
   by-value record param and treats it as a plain record. *)
evolve_param_list:
  | { [] }
  | VOID_KW
      { [] }
  | first = evolve_param rest = evolve_param_tail
      { first :: rest }

evolve_param_tail:
  | { [] }
  | COMMA next = evolve_param rest = evolve_param_tail
      { next :: rest }

evolve_param:
  | base = evolve_value_type name = IDENT
      { { param_type = base; param_name = Some name } }
  | CONST_KW base = evolve_value_type name = IDENT
      { { param_type = base; param_name = Some name } }

evolve_ret_type:
  | base = evolve_value_type
      { base }

evolve_value_type:
  | base = scalar_type
      { base }
  | name = qualified_ident
      { TRecord name }
  | STRUCT_KW name = qualified_ident
      { TRecord name }

evolve_block:
  | LBRACE stmts = list(evolve_stmt) RBRACE
      { seq_of_list stmts }

evolve_stmt:
  | SEMI
      { Skip }
  | block = evolve_block
      { block }
  | base = evolve_value_type name = IDENT ASSIGN init = val_expr SEMI
      { evolve_local_decl base name (Some init) }
  | base = evolve_value_type name = IDENT SEMI
      { evolve_local_decl base name None }
  | AUTO_KW name = IDENT ASSIGN init = val_expr SEMI
      { (* `auto x = <numeric>` — model as a double scalar local. *)
        evolve_local_decl TDouble name (Some init) }
  | lhs = val_postfix_expr ASSIGN rhs = val_expr SEMI
      { assignment_stmt lhs rhs }
  | lhs = val_postfix_expr PLUSEQ rhs = val_expr SEMI
      { evolve_compound (fun l r -> Add (l, r)) lhs rhs }
  | lhs = val_postfix_expr MINUSEQ rhs = val_expr SEMI
      { evolve_compound (fun l r -> Sub (l, r)) lhs rhs }
  | lhs = val_postfix_expr STAREQ rhs = val_expr SEMI
      { evolve_compound (fun l r -> Mul (l, r)) lhs rhs }
  | lhs = val_postfix_expr SLASHEQ rhs = val_expr SEMI
      { evolve_compound (fun l r -> Div (l, r)) lhs rhs }
  | lhs = val_postfix_expr INCR SEMI
      { evolve_compound (fun l _ -> Add (l, Int 1)) lhs (Int 1) }
  | lhs = val_postfix_expr DECR SEMI
      { evolve_compound (fun l _ -> Sub (l, Int 1)) lhs (Int 1) }
  | RETURN_KW value = val_expr SEMI
      { Return (Some value) }
  | RETURN_KW SEMI
      { Return None }
  | BREAK_KW SEMI
      { Break }
  | CONTINUE_KW SEMI
      { Continue }
  | IF_KW LPAREN cond = val_expr RPAREN then_branch = evolve_stmt ELSE_KW else_branch = evolve_stmt
      { If (value_as_cond cond, then_branch, else_branch) }
  | IF_KW LPAREN cond = val_expr RPAREN then_branch = evolve_stmt
      { If (value_as_cond cond, then_branch, Skip) }
  (* No `while` production here on purpose: an evolve-block loop must carry a
     syntactic termination argument, and only the counted `for` below does.
     The core language keeps its own `while` (see `stmt`). *)
  | FOR_KW LPAREN init = evolve_for_init SEMI cond = val_for_cond SEMI step = evolve_for_step RPAREN body = evolve_stmt
      { evolve_for ~init ~cond ~step body }
  | expr = val_expr SEMI
      { evolve_effect_stmt expr }

(* Yields the operator tag alongside its operands; `evolve_for` checks that the
   condition compares the induction variable against a literal and that the
   step moves it toward that bound. *)
val_for_cond:
  | left = val_add_expr op = val_cmp_op right = val_add_expr
      { (op, left, right) }

%inline val_cmp_op:
  | EQEQ { `Eq }
  | NEQ  { `Neq }
  | LT   { `Lt }
  | LE   { `Le }
  | GT   { `Gt }
  | GE   { `Ge }

evolve_for_init:
  | base = evolve_value_type name = IDENT ASSIGN init = val_expr
      { evolve_local_decl base name (Some init) }
  | lhs = val_postfix_expr ASSIGN rhs = val_expr
      { assignment_stmt lhs rhs }
  |
      { Skip }

evolve_for_step:
  | lhs = val_postfix_expr INCR
      { evolve_compound (fun l _ -> Add (l, Int 1)) lhs (Int 1) }
  | lhs = val_postfix_expr DECR
      { evolve_compound (fun l _ -> Sub (l, Int 1)) lhs (Int 1) }
  | lhs = val_postfix_expr PLUSEQ rhs = val_expr
      { evolve_compound (fun l r -> Add (l, r)) lhs rhs }
  | lhs = val_postfix_expr MINUSEQ rhs = val_expr
      { evolve_compound (fun l r -> Sub (l, r)) lhs rhs }
  | lhs = val_postfix_expr ASSIGN rhs = val_expr
      { assignment_stmt lhs rhs }
  |
      { Skip }

(* Value expressions: a full C-style precedence ladder that folds comparisons
   and boolean connectives into intrinsic calls so they live in `expr`. *)
val_expr:
  | value = val_ternary_expr
      { value }

val_ternary_expr:
  | cond = val_or_expr QUESTION t = val_expr COLON e = val_ternary_expr
      { val_ite cond t e }
  | value = val_or_expr
      { value }

val_or_expr:
  | left = val_or_expr OR right = val_and_expr
      { val_or left right }
  | value = val_and_expr
      { value }

val_and_expr:
  | left = val_and_expr AND right = val_cmp_expr
      { val_and left right }
  | value = val_cmp_expr
      { value }

val_cmp_expr:
  | left = val_add_expr EQEQ right = val_add_expr
      { val_cmp `Eq left right }
  | left = val_add_expr NEQ right = val_add_expr
      { val_cmp `Neq left right }
  | left = val_add_expr LT right = val_add_expr
      { val_cmp `Lt left right }
  | left = val_add_expr LE right = val_add_expr
      { val_cmp `Le left right }
  | left = val_add_expr GT right = val_add_expr
      { val_cmp `Gt left right }
  | left = val_add_expr GE right = val_add_expr
      { val_cmp `Ge left right }
  | value = val_add_expr
      { value }

val_add_expr:
  | left = val_add_expr PLUS right = val_mul_expr
      { Add (left, right) }
  | left = val_add_expr MINUS right = val_mul_expr
      { Sub (left, right) }
  | value = val_mul_expr
      { value }

val_mul_expr:
  | left = val_mul_expr STAR right = val_unary_expr
      { Mul (left, right) }
  | left = val_mul_expr SLASH right = val_unary_expr
      { Div (left, right) }
  | left = val_mul_expr PERCENT right = val_unary_expr
      { Mod (left, right) }
  | value = val_unary_expr
      { value }

val_unary_expr:
  | MINUS value = val_unary_expr
      { negate_expr value }
  | NOT value = val_unary_expr
      { val_not value }
  | STAR value = val_unary_expr
      { Deref value }
  | AMP value = val_unary_expr
      { AddrOf value }
  | LPAREN base = scalar_type RPAREN value = val_unary_expr
      { (* C-style cast to a scalar type, e.g. `(double)x`. Transparent for
           safety purposes; the operand is still scanned. Restricted to scalar
           type keywords so it cannot be confused with a parenthesized
           expression. *)
        ignore base; value }
  | value = val_postfix_expr
      { value }

val_postfix_expr:
  | base = val_postfix_expr DOT method_name = IDENT LPAREN args = separated_list(COMMA, val_arg) RPAREN
      { FuncCall (method_dot_call_name method_name, base :: List.concat args) }
  | base = val_postfix_expr ARROW method_name = IDENT LPAREN args = separated_list(COMMA, val_arg) RPAREN
      { FuncCall (method_arrow_call_name method_name, base :: List.concat args) }
  | base = val_postfix_expr DOT field = IDENT
      { Field (base, field) }
  | base = val_postfix_expr ARROW field = IDENT
      { Field (Deref base, field) }
  | base = val_postfix_expr LBRACKET index = val_expr RBRACKET
      { Index (base, index) }
  | value = val_primary_expr
      { value }

val_primary_expr:
  | n = INT_LIT
      { Int n }
  | value = FLOAT_LIT
      { FloatLit value }
  | value = DOUBLE_LIT
      { DoubleLit value }
  | value = CHAR_LIT
      { CharLit value }
  | TRUE_KW
      { BoolLit true }
  | FALSE_KW
      { BoolLit false }
  | STATIC_CAST_KW LT base = evolve_value_type GT LPAREN value = val_expr RPAREN
      { ignore base; value }
  | name = qualified_ident LPAREN args = separated_list(COMMA, val_arg) RPAREN
      { FuncCall (name, List.concat args) }
  | name = qualified_ident
      { Var name }
  | LPAREN value = val_expr RPAREN
      { value }

(* A call argument is either an ordinary value or a `{a, b, ...}` initializer
   list (used for listener attachment). The list is folded into an intrinsic
   so its elements are still scanned by strict mode. Each argument yields a
   list of exprs (always a singleton) so the call rule can `List.concat`. *)
val_arg:
  | value = val_expr
      { [value] }
  | LBRACE items = separated_list(COMMA, val_expr) RBRACE
      { [val_list items] }
