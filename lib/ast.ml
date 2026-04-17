type var = string

type func_name = string

type c_type =
  | TInt
  | TFloat
  | TDouble
  | TChar
  | TBool
  | TVoid
  | TPointer of c_type

type global_def = {
  global_type : c_type;
  global_name : var;
}

type param = {
  param_type : c_type;
  param_name : string option;
}

type contract = {
  require : string;
  guarantee : string;
  safety : string;
}

type contracted_function = {
  name : func_name;
  return_type : c_type;
  params : param list;
  contract : contract;
}

type imported_function = contracted_function

type header_import = {
  include_path : string;
  functions : imported_function list;
}

type expr =
  | Int of int
  | FloatLit of string
  | DoubleLit of string
  | CharLit of int
  | BoolLit of bool
  | Var of var
  | AddrOf of var
  | Deref of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Mod of expr * expr
  | FuncCall of func_name * expr list

type bexpr =
  | True
  | False
  | Eq of expr * expr
  | Neq of expr * expr
  | Lt of expr * expr
  | Le of expr * expr
  | Gt of expr * expr
  | Ge of expr * expr
  | Not of bexpr
  | And of bexpr * bexpr
  | Or of bexpr * bexpr

type stmt =
  | Skip
  | Assign of var * expr
  | Store of expr * expr
  | Seq of stmt list
  | If of bexpr * stmt * stmt
  | While of bexpr option * bexpr * stmt
  | Assume of bexpr
  | Assert of assert_origin * bexpr
  | Free of expr
  | Return of expr option

and assert_origin =
  | Source_assert
  | Call_require of func_name
  | Function_guarantee of func_name
  | Function_safety of func_name

type function_def = {
  name : func_name;
  return_type : c_type;
  params : param list;
  contract : contract option;
  body : stmt;
}

type program = {
  imports : header_import list;
  globals : global_def list;
  functions : function_def list;
  main : function_def;
}

let rec c_type_to_c = function
  | TInt -> "int"
  | TFloat -> "float"
  | TDouble -> "double"
  | TChar -> "char"
  | TBool -> "bool"
  | TVoid -> "void"
  | TPointer inner -> c_type_to_c inner ^ "*"

let type_with_name_to_c c_type name =
  c_type_to_c c_type ^ " " ^ name

let global_names globals =
  List.map (fun global -> global.global_name) globals

let is_pointer_type = function
  | TPointer _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid -> false

let pointer_base_type = function
  | TPointer inner -> Some inner
  | TInt | TFloat | TDouble | TChar | TBool | TVoid -> None

let is_real_type = function
  | TFloat | TDouble -> true
  | TInt | TChar | TBool | TVoid | TPointer _ -> false

let is_integer_like_type = function
  | TInt | TChar | TBool -> true
  | TFloat | TDouble | TVoid | TPointer _ -> false

let is_scalar_type = function
  | TInt | TFloat | TDouble | TChar | TBool -> true
  | TVoid | TPointer _ -> false

let lookup_global globals name =
  List.find_opt (fun global -> String.equal global.global_name name) globals

let lookup_global_type globals name =
  Option.map (fun global -> global.global_type) (lookup_global globals name)

let pointer_globals globals =
  List.filter (fun global -> is_pointer_type global.global_type) globals

let scalar_globals globals =
  List.filter (fun global -> not (is_pointer_type global.global_type)) globals

let load_helper_name = function
  | TInt -> "__anvil_load_int"
  | TFloat -> "__anvil_load_float"
  | TDouble -> "__anvil_load_double"
  | TChar -> "__anvil_load_char"
  | TBool -> "__anvil_load_bool"
  | TVoid | TPointer _ -> failwith "unsupported helper load type"

let escape_char_code = function
  | 0 -> "'\\0'"
  | 7 -> "'\\a'"
  | 8 -> "'\\b'"
  | 9 -> "'\\t'"
  | 10 -> "'\\n'"
  | 11 -> "'\\v'"
  | 12 -> "'\\f'"
  | 13 -> "'\\r'"
  | 34 -> "'\\\"'"
  | 39 -> "'\\''"
  | 92 -> "'\\\\'"
  | n when n >= 32 && n <= 126 ->
      Printf.sprintf "'%c'" (Char.chr n)
  | n ->
      Printf.sprintf "'\\x%02x'" n

let rec expr_to_c = function
  | Int i -> string_of_int i
  | FloatLit text
  | DoubleLit text ->
      text
  | CharLit value -> escape_char_code value
  | BoolLit true -> "true"
  | BoolLit false -> "false"
  | Var x -> x
  | AddrOf x -> "&" ^ x
  | Deref e -> "*" ^ expr_to_c e
  | Add (a, b) -> "(" ^ expr_to_c a ^ " + " ^ expr_to_c b ^ ")"
  | Sub (a, b) -> "(" ^ expr_to_c a ^ " - " ^ expr_to_c b ^ ")"
  | Mul (a, b) -> "(" ^ expr_to_c a ^ " * " ^ expr_to_c b ^ ")"
  | Div (a, b) -> "(" ^ expr_to_c a ^ " / " ^ expr_to_c b ^ ")"
  | Mod (a, b) -> "(" ^ expr_to_c a ^ " % " ^ expr_to_c b ^ ")"
  | FuncCall (f, args) ->
      f ^ "(" ^ String.concat ", " (List.map expr_to_c args) ^ ")"

let rec bexpr_to_c = function
  | True -> "1"
  | False -> "0"
  | Eq (a, b) -> "(" ^ expr_to_c a ^ " == " ^ expr_to_c b ^ ")"
  | Neq (a, b) -> "(" ^ expr_to_c a ^ " != " ^ expr_to_c b ^ ")"
  | Lt (a, b) -> "(" ^ expr_to_c a ^ " < " ^ expr_to_c b ^ ")"
  | Le (a, b) -> "(" ^ expr_to_c a ^ " <= " ^ expr_to_c b ^ ")"
  | Gt (a, b) -> "(" ^ expr_to_c a ^ " > " ^ expr_to_c b ^ ")"
  | Ge (a, b) -> "(" ^ expr_to_c a ^ " >= " ^ expr_to_c b ^ ")"
  | Not p -> "(!" ^ bexpr_to_c p ^ ")"
  | And (p, q) -> "(" ^ bexpr_to_c p ^ " && " ^ bexpr_to_c q ^ ")"
  | Or (p, q) -> "(" ^ bexpr_to_c p ^ " || " ^ bexpr_to_c q ^ ")"

let bexpr_to_annotation = function
  | bexpr -> bexpr_to_c bexpr

let indent n = String.make (n * 2) ' '

let param_to_c param =
  match param.param_name with
  | None -> c_type_to_c param.param_type
  | Some name -> type_with_name_to_c param.param_type name

let params_to_c params =
  match params with
  | [] -> "void"
  | params -> String.concat ", " (List.map param_to_c params)

let contract_to_c = function
  | None -> ""
  | Some contract ->
      "/* @Require " ^ contract.require ^ "\n"
      ^ " * @Guarantee " ^ contract.guarantee ^ "\n"
      ^ " * @Safety " ^ contract.safety ^ "\n"
      ^ " */\n"

let zero_literal_for_type = function
  | TInt -> "0"
  | TFloat -> "0.0f"
  | TDouble -> "0.0"
  | TChar -> "'\\0'"
  | TBool -> "false"
  | TVoid -> failwith "void does not have a zero literal"
  | TPointer _ -> "0"

let assume_fallback_to_c = function
  | TVoid -> "return;"
  | return_type -> "return " ^ zero_literal_for_type return_type ^ ";"

let loop_invariant_to_c ~indent_level = function
  | None -> ""
  | Some invariant ->
      indent indent_level ^ "/* @Invariant " ^ bexpr_to_annotation invariant
      ^ " */\n"

let negate_bexpr bexpr =
  match bexpr with
  | Not inner -> inner
  | other -> Not other

let rec stmt_to_c ~indent_level ~return_type = function
  | Skip -> indent indent_level ^ ";\n"
  | Assign (x, e) -> indent indent_level ^ x ^ " = " ^ expr_to_c e ^ ";\n"
  | Store (ptr, value) ->
      indent indent_level ^ "*" ^ expr_to_c ptr ^ " = " ^ expr_to_c value ^ ";\n"
  | Seq ss ->
      String.concat ""
        (List.map (stmt_to_c ~indent_level ~return_type) ss)
  | If (c, t, e) ->
      let cond = bexpr_to_c c in
      let then_branch =
        stmt_to_c ~indent_level:(indent_level + 1) ~return_type t
      in
      let else_branch =
        stmt_to_c ~indent_level:(indent_level + 1) ~return_type e
      in
      indent indent_level ^ "if (" ^ cond ^ ") {\n"
      ^ then_branch
      ^ indent indent_level ^ "} else {\n"
      ^ else_branch
      ^ indent indent_level ^ "}\n"
  | While (invariant, c, b) ->
      let cond = bexpr_to_c c in
      let body = stmt_to_c ~indent_level:(indent_level + 1) ~return_type b in
      loop_invariant_to_c ~indent_level invariant
      ^ indent indent_level ^ "while (" ^ cond ^ ") {\n"
      ^ body
      ^ indent indent_level ^ "}\n"
  | Assume c ->
      let wait_cond = negate_bexpr c in
      let body = stmt_to_c ~indent_level:(indent_level + 1) ~return_type Skip in
      loop_invariant_to_c ~indent_level (Some wait_cond)
      ^ indent indent_level ^ "while (" ^ bexpr_to_c wait_cond ^ ") {\n"
      ^ body
      ^ indent indent_level ^ "} /* assume */\n"
  | Assert (_, c) ->
      indent indent_level ^ "if (!" ^ bexpr_to_c c
      ^ ") { abort(); } /* assert */\n"
  | Free ptr ->
      indent indent_level ^ "free(" ^ expr_to_c ptr ^ ");\n"
  | Return None -> indent indent_level ^ "return;\n"
  | Return (Some value) ->
      indent indent_level ^ "return " ^ expr_to_c value ^ ";\n"

let function_def_to_c fn =
  let signature =
    type_with_name_to_c fn.return_type fn.name
    ^ "(" ^ params_to_c fn.params ^ ")"
  in
  let body = stmt_to_c ~indent_level:1 ~return_type:fn.return_type fn.body in
  contract_to_c fn.contract
  ^ signature ^ " {\n"
  ^ body
  ^ "}\n"

let helper_prototype name =
  match name with
  | "__anvil_load_int" -> "int __anvil_load_int(int block, int offset);\n"
  | "__anvil_load_float" -> "float __anvil_load_float(int block, int offset);\n"
  | "__anvil_load_double" -> "double __anvil_load_double(int block, int offset);\n"
  | "__anvil_load_char" -> "char __anvil_load_char(int block, int offset);\n"
  | "__anvil_load_bool" -> "bool __anvil_load_bool(int block, int offset);\n"
  | _ -> failwith ("unknown helper function " ^ name)

let helper_prototypes p =
  let rec helpers_in_expr acc = function
    | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ | AddrOf _ ->
        acc
    | Deref inner -> helpers_in_expr acc inner
    | Add (left, right)
    | Sub (left, right)
    | Mul (left, right)
    | Div (left, right)
    | Mod (left, right) ->
        helpers_in_expr (helpers_in_expr acc left) right
    | FuncCall (name, args) ->
        let acc =
          if String.length name >= 13
             && String.sub name 0 13 = "__anvil_load_"
          then
            name :: acc
          else
            acc
        in
        List.fold_left helpers_in_expr acc args
  in
  let rec helpers_in_bexpr acc = function
    | True | False -> acc
    | Eq (left, right)
    | Neq (left, right)
    | Lt (left, right)
    | Le (left, right)
    | Gt (left, right)
    | Ge (left, right) ->
        helpers_in_expr (helpers_in_expr acc left) right
    | Not inner -> helpers_in_bexpr acc inner
    | And (left, right)
    | Or (left, right) ->
        helpers_in_bexpr (helpers_in_bexpr acc left) right
  in
  let rec helpers_in_stmt acc = function
    | Skip -> acc
    | Assign (_, expr) -> helpers_in_expr acc expr
    | Store (ptr, value) -> helpers_in_expr (helpers_in_expr acc ptr) value
    | Seq stmts ->
        List.fold_left helpers_in_stmt acc stmts
    | If (cond, then_branch, else_branch) ->
        helpers_in_stmt
          (helpers_in_stmt (helpers_in_bexpr acc cond) then_branch)
          else_branch
    | While (invariant, cond, body) ->
        let acc =
          match invariant with
          | None -> acc
          | Some invariant -> helpers_in_bexpr acc invariant
        in
        helpers_in_stmt (helpers_in_bexpr acc cond) body
    | Assume cond | Assert (_, cond) -> helpers_in_bexpr acc cond
    | Free ptr -> helpers_in_expr acc ptr
    | Return None -> acc
    | Return (Some value) -> helpers_in_expr acc value
  in
  let helper_names =
    List.fold_left
      (fun acc fn -> helpers_in_stmt acc fn.body)
      (helpers_in_stmt [] p.main.body)
      p.functions
  in
  let helper_names =
    List.sort_uniq String.compare helper_names
  in
  String.concat "" (List.map helper_prototype helper_names)

let program_to_c p =
  let header =
    "#include <stdlib.h>\n#include <stdio.h>\n#include <stdbool.h>\n"
  in
  let helpers =
    match helper_prototypes p with
    | "" -> ""
    | prototypes -> prototypes ^ "\n"
  in
  let imports =
    match p.imports with
    | [] -> "\n"
    | imports ->
        String.concat ""
          (List.map
             (fun imported_header ->
               "#include \"" ^ imported_header.include_path ^ "\"\n")
             imports)
        ^ "\n"
  in
  let globals =
    match p.globals with
    | [] -> ""
    | decls ->
        String.concat "\n"
          (List.map
             (fun global ->
               type_with_name_to_c global.global_type global.global_name ^ ";")
             decls)
        ^ "\n\n"
  in
  let functions =
    match p.functions with
    | [] -> ""
    | functions ->
        String.concat "\n" (List.map function_def_to_c functions) ^ "\n"
  in
  let main = function_def_to_c p.main in
  header ^ helpers ^ imports ^ globals ^ functions ^ main
