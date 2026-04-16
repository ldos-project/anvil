type sort =
  | Int
  | Bool

type int_expr =
  | Int_lit of int
  | Var of string
  | Add of int_expr list
  | Sub of int_expr * int_expr
  | Mul of int_expr list
  | Div of int_expr * int_expr
  | Mod of int_expr * int_expr
  | App of string * int_expr list

type formula =
  | True
  | False
  | Not of formula
  | And of formula list
  | Or of formula list
  | Implies of formula * formula
  | Eq of int_expr * int_expr
  | Neq of int_expr * int_expr
  | Lt of int_expr * int_expr
  | Le of int_expr * int_expr
  | Gt of int_expr * int_expr
  | Ge of int_expr * int_expr

type command =
  | Set_option of string * string
  | Declare_const of string * sort
  | Declare_fun of string * sort list * sort
  | Assert of formula
  | Check_sat
  | Get_value of int_expr

module String_set = Set.Make (String)
module String_map = Map.Make (String)

let sort_to_smt = function
  | Int -> "Int"
  | Bool -> "Bool"

let parens head args =
  "(" ^ String.concat " " (head :: args) ^ ")"

let rec int_expr_to_smt = function
  | Int_lit n when n < 0 -> parens "-" [string_of_int (-n)]
  | Int_lit n -> string_of_int n
  | Var name -> name
  | Add [] -> "0"
  | Add [expr] -> int_expr_to_smt expr
  | Add exprs -> parens "+" (List.map int_expr_to_smt exprs)
  | Sub (left, right) ->
      parens "-" [int_expr_to_smt left; int_expr_to_smt right]
  | Mul [] -> "1"
  | Mul [expr] -> int_expr_to_smt expr
  | Mul exprs -> parens "*" (List.map int_expr_to_smt exprs)
  | Div (left, right) ->
      parens "div" [int_expr_to_smt left; int_expr_to_smt right]
  | Mod (left, right) ->
      parens "mod" [int_expr_to_smt left; int_expr_to_smt right]
  | App (name, []) -> name
  | App (name, args) ->
      parens name (List.map int_expr_to_smt args)

let rec formula_to_smt = function
  | True -> "true"
  | False -> "false"
  | Not inner -> parens "not" [formula_to_smt inner]
  | And [] -> "true"
  | And [inner] -> formula_to_smt inner
  | And parts -> parens "and" (List.map formula_to_smt parts)
  | Or [] -> "false"
  | Or [inner] -> formula_to_smt inner
  | Or parts -> parens "or" (List.map formula_to_smt parts)
  | Implies (left, right) ->
      parens "=>" [formula_to_smt left; formula_to_smt right]
  | Eq (left, right) ->
      parens "=" [int_expr_to_smt left; int_expr_to_smt right]
  | Neq (left, right) ->
      parens "not" [parens "=" [int_expr_to_smt left; int_expr_to_smt right]]
  | Lt (left, right) ->
      parens "<" [int_expr_to_smt left; int_expr_to_smt right]
  | Le (left, right) ->
      parens "<=" [int_expr_to_smt left; int_expr_to_smt right]
  | Gt (left, right) ->
      parens ">" [int_expr_to_smt left; int_expr_to_smt right]
  | Ge (left, right) ->
      parens ">=" [int_expr_to_smt left; int_expr_to_smt right]

let command_to_smt = function
  | Set_option (name, value) ->
      parens "set-option" [name; value]
  | Declare_const (name, sort) ->
      parens "declare-const" [name; sort_to_smt sort]
  | Declare_fun (name, arg_sorts, ret_sort) ->
      parens "declare-fun"
        [ name
        ; "(" ^ String.concat " " (List.map sort_to_smt arg_sorts) ^ ")"
        ; sort_to_smt ret_sort
        ]
  | Assert formula ->
      parens "assert" [formula_to_smt formula]
  | Check_sat -> parens "check-sat" []
  | Get_value expr ->
      parens "get-value" ["(" ^ int_expr_to_smt expr ^ ")"]

let script_to_smt commands =
  String.concat "\n" (List.map command_to_smt commands) ^ "\n"

let mk_not = function
  | True -> False
  | False -> True
  | Not inner -> inner
  | formula -> Not formula

let mk_and formulas =
  let formulas =
    List.concat_map
      (function
        | True -> []
        | And inner -> inner
        | formula -> [formula])
      formulas
  in
  if List.exists (( = ) False) formulas then False
  else
    match formulas with
    | [] -> True
    | [formula] -> formula
    | formulas -> And formulas

let mk_or formulas =
  let formulas =
    List.concat_map
      (function
        | False -> []
        | Or inner -> inner
        | formula -> [formula])
      formulas
  in
  if List.exists (( = ) True) formulas then True
  else
    match formulas with
    | [] -> False
    | [formula] -> formula
    | formulas -> Or formulas

let mk_implies left right =
  match left, right with
  | False, _ -> True
  | _, True -> True
  | True, formula -> formula
  | formula, False -> mk_not formula
  | _ -> Implies (left, right)

let rec subst_int_expr var replacement = function
  | Int_lit _ as expr -> expr
  | Var name ->
      if String.equal name var then replacement else Var name
  | Add exprs -> Add (List.map (subst_int_expr var replacement) exprs)
  | Sub (left, right) ->
      Sub
        (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Mul exprs -> Mul (List.map (subst_int_expr var replacement) exprs)
  | Div (left, right) ->
      Div
        (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Mod (left, right) ->
      Mod
        (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | App (name, args) ->
      App (name, List.map (subst_int_expr var replacement) args)

let rec subst_formula var replacement = function
  | True -> True
  | False -> False
  | Not inner -> mk_not (subst_formula var replacement inner)
  | And formulas -> mk_and (List.map (subst_formula var replacement) formulas)
  | Or formulas -> mk_or (List.map (subst_formula var replacement) formulas)
  | Implies (left, right) ->
      mk_implies
        (subst_formula var replacement left)
        (subst_formula var replacement right)
  | Eq (left, right) ->
      Eq (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Neq (left, right) ->
      Neq (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Lt (left, right) ->
      Lt (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Le (left, right) ->
      Le (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Gt (left, right) ->
      Gt (subst_int_expr var replacement left, subst_int_expr var replacement right)
  | Ge (left, right) ->
      Ge (subst_int_expr var replacement left, subst_int_expr var replacement right)

let rec vars_in_int_expr acc = function
  | Int_lit _ -> acc
  | Var name -> String_set.add name acc
  | Add exprs | Mul exprs ->
      List.fold_left vars_in_int_expr acc exprs
  | Sub (left, right) | Div (left, right) | Mod (left, right) ->
      vars_in_int_expr (vars_in_int_expr acc left) right
  | App (_, args) ->
      List.fold_left vars_in_int_expr acc args

let rec vars_in_formula acc = function
  | True | False -> acc
  | Not inner -> vars_in_formula acc inner
  | And formulas | Or formulas ->
      List.fold_left vars_in_formula acc formulas
  | Implies (left, right) ->
      vars_in_formula (vars_in_formula acc left) right
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      vars_in_int_expr (vars_in_int_expr acc left) right

let collect_vars formula =
  vars_in_formula String_set.empty formula |> String_set.elements

let rec apps_in_int_expr acc = function
  | Int_lit _ | Var _ -> acc
  | Add exprs | Mul exprs ->
      List.fold_left apps_in_int_expr acc exprs
  | Sub (left, right) | Div (left, right) | Mod (left, right) ->
      apps_in_int_expr (apps_in_int_expr acc left) right
  | App (name, args) as expr ->
      let acc =
        List.fold_left apps_in_int_expr acc args
      in
      String_map.add (int_expr_to_smt expr) (name, expr) acc

let rec apps_in_formula acc = function
  | True | False -> acc
  | Not inner -> apps_in_formula acc inner
  | And formulas | Or formulas ->
      List.fold_left apps_in_formula acc formulas
  | Implies (left, right) ->
      apps_in_formula (apps_in_formula acc left) right
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      apps_in_int_expr (apps_in_int_expr acc left) right

let collect_apps formula =
  apps_in_formula String_map.empty formula
  |> String_map.bindings
  |> List.map (fun (_, value) -> value)

let collect_function_decls apps =
  let rec loop decls = function
    | [] -> Ok (String_map.bindings decls)
    | (name, App (_, args)) :: rest ->
        let arity = List.length args in
        (match String_map.find_opt name decls with
        | None ->
            loop (String_map.add name arity decls) rest
        | Some existing when existing = arity ->
            loop decls rest
        | Some existing ->
            Error
              (Printf.sprintf
                 "function `%s` used with arities %d and %d in Z3 translation"
                 name
                 existing
                 arity))
    | _ :: rest -> loop decls rest
  in
  loop String_map.empty apps

let declare_consts vars =
  List.map (fun name -> Declare_const (name, Int)) vars

let declare_funs decls =
  List.map
    (fun (name, arity) ->
      Declare_fun (name, List.init arity (fun _ -> Int), Int))
    decls

let rec int_expr_to_pretty = function
  | Int_lit n -> string_of_int n
  | Var name -> name
  | Add [left; right] ->
      "(" ^ int_expr_to_pretty left ^ " + " ^ int_expr_to_pretty right ^ ")"
  | Add exprs ->
      "(" ^ String.concat " + " (List.map int_expr_to_pretty exprs) ^ ")"
  | Sub (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " - " ^ int_expr_to_pretty right ^ ")"
  | Mul [left; right] ->
      "(" ^ int_expr_to_pretty left ^ " * " ^ int_expr_to_pretty right ^ ")"
  | Mul exprs ->
      "(" ^ String.concat " * " (List.map int_expr_to_pretty exprs) ^ ")"
  | Div (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " / " ^ int_expr_to_pretty right ^ ")"
  | Mod (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " % " ^ int_expr_to_pretty right ^ ")"
  | App (name, args) ->
      name ^ "(" ^ String.concat ", " (List.map int_expr_to_pretty args) ^ ")"

let rec formula_to_pretty = function
  | True -> "true"
  | False -> "false"
  | Not inner -> "!(" ^ formula_to_pretty inner ^ ")"
  | And formulas ->
      "(" ^ String.concat " && " (List.map formula_to_pretty formulas) ^ ")"
  | Or formulas ->
      "(" ^ String.concat " || " (List.map formula_to_pretty formulas) ^ ")"
  | Implies (left, right) ->
      "(" ^ formula_to_pretty left ^ " => " ^ formula_to_pretty right ^ ")"
  | Eq (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " == " ^ int_expr_to_pretty right ^ ")"
  | Neq (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " != " ^ int_expr_to_pretty right ^ ")"
  | Lt (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " < " ^ int_expr_to_pretty right ^ ")"
  | Le (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " <= " ^ int_expr_to_pretty right ^ ")"
  | Gt (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " > " ^ int_expr_to_pretty right ^ ")"
  | Ge (left, right) ->
      "(" ^ int_expr_to_pretty left ^ " >= " ^ int_expr_to_pretty right ^ ")"
