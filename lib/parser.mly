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

let negate_expr = function
  | Int n -> Int (-n)
  | FloatLit value -> FloatLit ("-" ^ value)
  | DoubleLit value -> DoubleLit ("-" ^ value)
  | value -> Sub (Int 0, value)

let predicate_bexpr name args =
  Neq (FuncCall (name, args), Int 0)

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

type top_item =
  | Top_record of record_def
  | Top_global of global_def
  | Top_function of function_def
  | Top_main of function_def

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
%token INT_KW FLOAT_KW DOUBLE_KW CHAR_KW BOOL_KW MAIN_KW VOID_KW STRUCT_KW IF_KW ELSE_KW WHILE_KW RETURN_KW FREE_KW TRUE_KW FALSE_KW
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET SEMI COMMA AMP DOT ARROW
%token PLUS MINUS STAR SLASH PERCENT
%token ASSIGN EQEQ NEQ LT LE GT GE NOT AND OR
%token EOF

%start <Ast.program> program
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
  | STRUCT_KW name = IDENT
      { TRecord name }

nonvoid_type:
  | base = scalar_type
      { base }
  | base = struct_type
      { base }

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
  | name = IDENT LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { FuncCall (name, args) }
  | name = IDENT
      { Var name }
  | LPAREN value = contract_expr RPAREN
      { value }

contract_bexpr:
  | value = contract_or_bexpr
      { value }

contract_or_bexpr:
  | value = contract_and_bexpr
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
  | NOT value = contract_not_bexpr
      { Not value }

contract_atom_bexpr:
  | n = INT_LIT
      { bool_of_int n }
  | TRUE_KW
      { True }
  | FALSE_KW
      { False }
  | name = IDENT LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { predicate_bexpr name args }
  | LPAREN value = contract_bexpr RPAREN
      { value }
  | left = contract_expr EQEQ right = contract_expr
      { Eq (left, right) }
  | left = contract_expr NEQ right = contract_expr
      { Neq (left, right) }
  | left = contract_expr LT right = contract_expr
      { Lt (left, right) }
  | left = contract_expr LE right = contract_expr
      { Le (left, right) }
  | left = contract_expr GT right = contract_expr
      { Gt (left, right) }
  | left = contract_expr GE right = contract_expr
      { Ge (left, right) }

program:
  | items = list(top_item) EOF
      { build_program items }

top_item:
  | STRUCT_KW name = IDENT LBRACE fields = record_field_list RBRACE SEMI
      { Top_record { record_name = name; fields } }
  | INT_KW MAIN_KW LPAREN VOID_KW RPAREN body = block
      { Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) }
  | INT_KW MAIN_KW LPAREN RPAREN body = block
      { Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) }
  | base = nonvoid_type stars = pointer_stars name = IDENT tail = top_tail
      { tail base stars name }
  | VOID_KW stars = pointer_stars name = IDENT LPAREN params = param_list RPAREN body = block
      {
        Top_function
          (make_function ~name ~return_type:(pointer_type TVoid stars) ~params body)
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
  | STAR lhs = expr ASSIGN rhs = expr SEMI
      { Store (lhs, rhs) }
  | RETURN_KW value = option(expr) SEMI
      { Return value }
  | FREE_KW LPAREN ptr = expr RPAREN SEMI
      { Free ptr }
  | IF_KW LPAREN cond = bexpr RPAREN then_branch = block ELSE_KW else_branch = block
      { If (cond, then_branch, else_branch) }
  | IF_KW LPAREN NOT cond = bexpr RPAREN LBRACE RETURN_KW SEMI RBRACE
      { Assume cond }
  | IF_KW LPAREN NOT cond = bexpr RPAREN LBRACE RETURN_KW value = expr SEMI RBRACE
      { expect_zero_literal value; Assume cond }
  | IF_KW LPAREN NOT cond = bexpr RPAREN LBRACE name = IDENT LPAREN RPAREN SEMI RBRACE
      { expect_abort name; Assert (Source_assert, cond) }
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

atom_bexpr:
  | LPAREN value = bexpr RPAREN
      { value }
  | n = INT_LIT
      { bool_of_int n }
  | TRUE_KW
      { True }
  | FALSE_KW
      { False }
  | left = expr EQEQ right = expr
      { Eq (left, right) }
  | left = expr NEQ right = expr
      { Neq (left, right) }
  | left = expr LT right = expr
      { Lt (left, right) }
  | left = expr LE right = expr
      { Le (left, right) }
  | left = expr GT right = expr
      { Gt (left, right) }
  | left = expr GE right = expr
      { Ge (left, right) }

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

postfix_expr:
  | value = primary_expr
      { value }
  | base = postfix_expr LBRACKET index = expr RBRACKET
      { Index (base, index) }
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
  | name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (name, args) }
  | name = IDENT
      { Var name }
  | LPAREN value = expr RPAREN
      { value }
