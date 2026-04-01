type var = string

type func_name = string

type c_type =
  | TInt
  | TVoid
  | TPointer of c_type

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
  | Var of var
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
  | Seq of stmt list
  | If of bexpr * stmt * stmt
  | While of bexpr option * bexpr * stmt
  | Assume of bexpr
  | Assert of bexpr
  | Return of expr option

type function_def = {
  name : func_name;
  return_type : c_type;
  params : param list;
  contract : contract option;
  body : stmt;
}

type program = {
  imports : header_import list;
  globals : var list;
  functions : function_def list;
  main : function_def;
}

let rec expr_to_c = function
  | Int i -> string_of_int i
  | Var x -> x
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

let rec c_type_to_c = function
  | TInt -> "int"
  | TVoid -> "void"
  | TPointer inner -> c_type_to_c inner ^ "*"

let type_with_name_to_c c_type name =
  c_type_to_c c_type ^ " " ^ name

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

let assume_fallback_to_c = function
  | TVoid -> "return;"
  | TInt | TPointer _ -> "return 0;"

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
  | Assert c ->
      indent indent_level ^ "if (!" ^ bexpr_to_c c
      ^ ") { abort(); } /* assert */\n"
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

let program_to_c p =
  let header = "#include <stdlib.h>\n#include <stdio.h>\n" in
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
    | vars ->
        String.concat "\n" (List.map (fun v -> "int " ^ v ^ ";") vars) ^ "\n\n"
  in
  let functions =
    match p.functions with
    | [] -> ""
    | functions ->
        String.concat "\n" (List.map function_def_to_c functions) ^ "\n"
  in
  let main = function_def_to_c p.main in
  header ^ imports ^ globals ^ functions ^ main
