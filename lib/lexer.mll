{
open Parser

exception Syntax_error of string

let raise_syntax msg = raise (Syntax_error msg)

let char_of_escape = function
  | '0' -> 0
  | 'a' -> 7
  | 'b' -> 8
  | 't' -> 9
  | 'n' -> 10
  | 'v' -> 11
  | 'f' -> 12
  | 'r' -> 13
  | '"' -> 34
  | '\'' -> 39
  | '\\' -> 92
  | c -> Char.code c

let parse_char_lit lit =
  if String.length lit = 3 then
    Char.code lit.[1]
  else if String.length lit = 4 && lit.[1] = '\\' then
    char_of_escape lit.[2]
  else
    raise_syntax ("unsupported character literal `" ^ lit ^ "`")
}

rule read = parse
  | [' ' '\t' '\r']     { read lexbuf }
  | '\n'                { Lexing.new_line lexbuf; read lexbuf }
  | '#'                 { skip_line lexbuf; read lexbuf }
  | "/*"                { block_comment lexbuf; read lexbuf }
  | "//"                { skip_line lexbuf; read lexbuf }
  | "int"               { INT_KW }
  | "float"             { FLOAT_KW }
  | "double"            { DOUBLE_KW }
  | "char"              { CHAR_KW }
  | "bool"              { BOOL_KW }
  | "struct"            { STRUCT_KW }
  | "class"             { CLASS_KW }
  | "namespace"         { NAMESPACE_KW }
  | "true"              { TRUE_KW }
  | "false"             { FALSE_KW }
  | "main"              { MAIN_KW }
  | "void"              { VOID_KW }
  | "if"                { IF_KW }
  | "else"              { ELSE_KW }
  | "while"             { WHILE_KW }
  | "return"            { RETURN_KW }
  | "free"              { FREE_KW }
  | "&&"                { AND }
  | "||"                { OR }
  | "::"                { SCOPE }
  | "->"                { ARROW }
  | "=="                { EQEQ }
  | "!="                { NEQ }
  | "<="                { LE }
  | ">="                { GE }
  | ['0'-'9']+ '.' ['0'-'9']* (['e' 'E'] ['+' '-']? ['0'-'9']+)? ['f' 'F'] as lit
                        { FLOAT_LIT lit }
  | ['0'-'9']+ ['e' 'E'] ['+' '-']? ['0'-'9']+ ['f' 'F'] as lit
                        { FLOAT_LIT lit }
  | ['0'-'9']+ '.' ['0'-'9']* (['e' 'E'] ['+' '-']? ['0'-'9']+)? as lit
                        { DOUBLE_LIT lit }
  | ['0'-'9']+ ['e' 'E'] ['+' '-']? ['0'-'9']+ as lit
                        { DOUBLE_LIT lit }
  | '\'' '\\' ['0' 'a' 'b' 't' 'n' 'v' 'f' 'r' '"' '\'' '\\'] '\'' as lit
                        { CHAR_LIT (parse_char_lit lit) }
  | '\'' [^ '\\' '\''] '\'' as lit
                        { CHAR_LIT (parse_char_lit lit) }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '{'                 { LBRACE }
  | '}'                 { RBRACE }
  | '['                 { LBRACKET }
  | ']'                 { RBRACKET }
  | ';'                 { SEMI }
  | ','                 { COMMA }
  | '&'                 { AMP }
  | '.'                 { DOT }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { STAR }
  | '/'                 { SLASH }
  | '%'                 { PERCENT }
  | '='                 { ASSIGN }
  | '!'                 { NOT }
  | '<'                 { LT }
  | '>'                 { GT }
  | ['0'-'9']+ as lit   { INT_LIT (int_of_string lit) }
  | ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']* as id
                        { IDENT id }
  | eof                 { EOF }
  | _ as c              { raise_syntax (Printf.sprintf "unexpected character `%c`" c) }

and skip_line = parse
  | '\n'                { Lexing.new_line lexbuf }
  | eof                 { () }
  | _                   { skip_line lexbuf }

and block_comment = parse
  | "*/"                { () }
  | '\n'                { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof                 { raise_syntax "unterminated comment" }
  | _                   { block_comment lexbuf }
