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

let expect_zero n =
  if n <> 0 then fail "expected `return 0;`, got `return %d;`" n

let expect_abort name =
  if String.equal name "abort" then ()
  else fail "expected `abort()`, got `%s()`" name

let predicate_bexpr name args =
  Neq (FuncCall (name, args), Int 0)

let rec pointer_type base = function
  | 0 -> base
  | depth -> TPointer (pointer_type base (depth - 1))

let make_function ?contract ~name ~return_type ~params body =
  { name; return_type; params; contract; body }

type top_item =
  | Top_global of var
  | Top_pointer_global of var
  | Top_function of function_def
  | Top_main of function_def

let build_program items =
  let rec loop globals_rev pointer_globals_rev functions_rev main = function
    | [] ->
        let main =
          match main with
          | Some main -> main
          | None -> fail "missing `main` definition"
        in
        {
          imports = [];
          globals = List.rev globals_rev;
          pointer_globals = List.rev pointer_globals_rev;
          functions = List.rev functions_rev;
          main;
        }
    | Top_global name :: rest ->
        loop (name :: globals_rev) pointer_globals_rev functions_rev main rest
    | Top_pointer_global name :: rest ->
        loop globals_rev (name :: pointer_globals_rev) functions_rev main rest
    | Top_function fn :: rest ->
        loop globals_rev pointer_globals_rev (fn :: functions_rev) main rest
    | Top_main fn :: rest ->
        (match main with
        | Some _ -> fail "multiple `main` definitions"
        | None ->
            loop globals_rev pointer_globals_rev functions_rev (Some fn) rest)
  in
  loop [] [] [] None items
%}

%token <int> INT_LIT
%token <string> IDENT
%token INT_KW MAIN_KW VOID_KW IF_KW ELSE_KW WHILE_KW RETURN_KW FREE_KW
%token LPAREN RPAREN LBRACE RBRACE SEMI COMMA AMP
%token PLUS MINUS STAR SLASH PERCENT
%token ASSIGN EQEQ NEQ LT LE GT GE NOT AND OR
%token EOF

%start <Ast.program> program
%start <Ast.expr> contract_expr_eof
%start <Ast.bexpr> contract_bexpr_eof
%start <Ast.bexpr> bexpr_eof

%left OR
%left AND
%nonassoc EQEQ NEQ LT LE GT GE
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UMINUS
%right NOT

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

contract_expr:
  | n = INT_LIT
      { Int n }
  | MINUS value = contract_expr %prec UMINUS
      { match value with Int n -> Int (-n) | _ -> Sub (Int 0, value) }
  | AMP name = IDENT
      { AddrOf name }
  | STAR value = contract_expr %prec UMINUS
      { Deref value }
  | name = IDENT LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { FuncCall (name, args) }
  | name = IDENT
      { Var name }
  | LPAREN value = contract_expr RPAREN
      { value }
  | left = contract_expr PLUS right = contract_expr
      { Add (left, right) }
  | left = contract_expr MINUS right = contract_expr
      { Sub (left, right) }
  | left = contract_expr STAR right = contract_expr
      { Mul (left, right) }
  | left = contract_expr SLASH right = contract_expr
      { Div (left, right) }
  | left = contract_expr PERCENT right = contract_expr
      { Mod (left, right) }

contract_bexpr:
  | n = INT_LIT
      { bool_of_int n }
  | name = IDENT LPAREN args = separated_list(COMMA, contract_expr) RPAREN
      { predicate_bexpr name args }
  | LPAREN value = contract_bexpr RPAREN
      { value }
  | NOT value = contract_bexpr %prec NOT
      { Not value }
  | left = contract_bexpr AND right = contract_bexpr
      { And (left, right) }
  | left = contract_bexpr OR right = contract_bexpr
      { Or (left, right) }
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
  | INT_KW MAIN_KW LPAREN VOID_KW RPAREN body = block
      { Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) }
  | INT_KW MAIN_KW LPAREN RPAREN body = block
      { Top_main (make_function ~name:"main" ~return_type:TInt ~params:[] body) }
  | INT_KW stars = pointer_stars name = IDENT tail = int_top_tail
      { tail stars name }
  | VOID_KW stars = pointer_stars name = IDENT LPAREN params = param_list RPAREN body = block
      {
        Top_function
          (make_function ~name ~return_type:(pointer_type TVoid stars) ~params body)
      }

int_top_tail:
  | SEMI
      {
        fun stars name ->
          if stars = 0 then Top_global name
          else if stars = 1 then Top_pointer_global name
          else fail "only `int*` globals are supported"
      }
  | LPAREN params = param_list RPAREN body = block
      {
        fun stars name ->
          Top_function
            (make_function ~name ~return_type:(pointer_type TInt stars) ~params body)
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
  | INT_KW stars = pointer_stars name = IDENT
      { { param_type = pointer_type TInt stars; param_name = Some name } }
  | VOID_KW STAR stars = pointer_stars name = IDENT
      { { param_type = pointer_type TVoid (stars + 1); param_name = Some name } }

stmt_list:
  | { [] }
  | stmt = stmt rest = stmt_list
      { stmt :: rest }

block:
  | LBRACE stmts = stmt_list RBRACE
      { seq_of_list stmts }

stmt:
  | SEMI
      { Skip }
  | name = IDENT ASSIGN rhs = expr SEMI
      { Assign (name, rhs) }
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
  | IF_KW LPAREN NOT cond = bexpr RPAREN LBRACE RETURN_KW n = INT_LIT SEMI RBRACE
      { expect_zero n; Assume cond }
  | IF_KW LPAREN NOT cond = bexpr RPAREN LBRACE name = IDENT LPAREN RPAREN SEMI RBRACE
      { expect_abort name; Assert cond }
  | WHILE_KW LPAREN cond = bexpr RPAREN body = block
      { While (None, cond, body) }

bexpr:
  | n = INT_LIT
      { bool_of_int n }
  | LPAREN NOT inner = bexpr RPAREN
      { Not inner }
  | LPAREN left = bexpr AND right = bexpr RPAREN
      { And (left, right) }
  | LPAREN left = bexpr OR right = bexpr RPAREN
      { Or (left, right) }
  | LPAREN left = expr EQEQ right = expr RPAREN
      { Eq (left, right) }
  | LPAREN left = expr NEQ right = expr RPAREN
      { Neq (left, right) }
  | LPAREN left = expr LT right = expr RPAREN
      { Lt (left, right) }
  | LPAREN left = expr LE right = expr RPAREN
      { Le (left, right) }
  | LPAREN left = expr GT right = expr RPAREN
      { Gt (left, right) }
  | LPAREN left = expr GE right = expr RPAREN
      { Ge (left, right) }

expr:
  | n = INT_LIT
      { Int n }
  | MINUS n = INT_LIT
      { Int (-n) }
  | AMP name = IDENT
      { AddrOf name }
  | STAR value = expr %prec UMINUS
      { Deref value }
  | name = IDENT LPAREN args = separated_list(COMMA, expr) RPAREN
      { FuncCall (name, args) }
  | name = IDENT
      { Var name }
  | LPAREN left = expr PLUS right = expr RPAREN
      { Add (left, right) }
  | LPAREN left = expr MINUS right = expr RPAREN
      { Sub (left, right) }
  | LPAREN left = expr STAR right = expr RPAREN
      { Mul (left, right) }
  | LPAREN left = expr SLASH right = expr RPAREN
      { Div (left, right) }
  | LPAREN left = expr PERCENT right = expr RPAREN
      { Mod (left, right) }
