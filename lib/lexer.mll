{
open Parser

exception Syntax_error of string

let raise_syntax msg = raise (Syntax_error msg)
}

rule read = parse
  | [' ' '\t' '\r']     { read lexbuf }
  | '\n'                { Lexing.new_line lexbuf; read lexbuf }
  | '#'                 { skip_line lexbuf; read lexbuf }
  | "/*"                { block_comment lexbuf; read lexbuf }
  | "//"                { skip_line lexbuf; read lexbuf }
  | "int"               { INT_KW }
  | "main"              { MAIN_KW }
  | "void"              { VOID_KW }
  | "if"                { IF_KW }
  | "else"              { ELSE_KW }
  | "while"             { WHILE_KW }
  | "return"            { RETURN_KW }
  | "free"              { FREE_KW }
  | "&&"                { AND }
  | "||"                { OR }
  | "=="                { EQEQ }
  | "!="                { NEQ }
  | "<="                { LE }
  | ">="                { GE }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '{'                 { LBRACE }
  | '}'                 { RBRACE }
  | ';'                 { SEMI }
  | ','                 { COMMA }
  | '&'                 { AMP }
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
