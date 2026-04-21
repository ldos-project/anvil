type sort =
  | Int
  | Real
  | Bool

type int_expr =
  | Int_lit of int
  | Real_lit of string
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
  | Forall of (string * sort) list * formula
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
  | Real -> "Real"
  | Bool -> "Bool"

let parens head args =
  "(" ^ String.concat " " (head :: args) ^ ")"

let quantified_binding_to_smt (name, sort) =
  "(" ^ name ^ " " ^ sort_to_smt sort ^ ")"

let quantified_binding_to_pretty (name, sort) =
  name ^ ":" ^ sort_to_smt sort

let rec int_expr_to_smt = function
  | Int_lit n when n < 0 -> parens "-" [string_of_int (-n)]
  | Int_lit n -> string_of_int n
  | Real_lit text -> text
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
  | Forall ([], body) ->
      formula_to_smt body
  | Forall (bindings, body) ->
      parens "forall"
        [ "(" ^ String.concat " " (List.map quantified_binding_to_smt bindings) ^ ")"
        ; formula_to_smt body
        ]
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

let mk_forall bindings body =
  match bindings with
  | [] -> body
  | _ -> Forall (bindings, body)

let rec subst_int_expr var replacement = function
  | Int_lit _ as expr -> expr
  | Real_lit _ as expr -> expr
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

let add_bound_names set bindings =
  List.fold_left
    (fun acc (name, _sort) -> String_set.add name acc)
    set
    bindings

let rec all_var_names_in_int_expr acc = function
  | Int_lit _ | Real_lit _ -> acc
  | Var name -> String_set.add name acc
  | Add exprs | Mul exprs ->
      List.fold_left all_var_names_in_int_expr acc exprs
  | Sub (left, right) | Div (left, right) | Mod (left, right) ->
      all_var_names_in_int_expr (all_var_names_in_int_expr acc left) right
  | App (_, args) ->
      List.fold_left all_var_names_in_int_expr acc args

and all_var_names_in_formula acc = function
  | True | False -> acc
  | Not inner -> all_var_names_in_formula acc inner
  | And formulas | Or formulas ->
      List.fold_left all_var_names_in_formula acc formulas
  | Implies (left, right) ->
      all_var_names_in_formula (all_var_names_in_formula acc left) right
  | Forall (bindings, body) ->
      all_var_names_in_formula (add_bound_names acc bindings) body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      all_var_names_in_int_expr (all_var_names_in_int_expr acc left) right

and fresh_quantified_name used_names base =
  let rec loop index =
    let candidate = Printf.sprintf "%s__q%d" base index in
    if String_set.mem candidate used_names then loop (index + 1) else candidate
  in
  loop 1

and alpha_rename_quantified_bindings replacement_vars bindings body =
  let used_names =
    add_bound_names
      (all_var_names_in_formula replacement_vars body)
      bindings
  in
  let rec loop acc current_body used_names = function
    | [] -> List.rev acc, current_body
    | ((name, sort) as binding) :: rest ->
        if String_set.mem name replacement_vars then
          let fresh = fresh_quantified_name used_names name in
          let renamed_body = subst_formula name (Var fresh) current_body in
          loop
            ((fresh, sort) :: acc)
            renamed_body
            (String_set.add fresh used_names)
            rest
        else
          loop (binding :: acc) current_body (String_set.add name used_names) rest
  in
  loop [] body used_names bindings

and subst_formula var replacement = function
  | True -> True
  | False -> False
  | Not inner -> mk_not (subst_formula var replacement inner)
  | And formulas -> mk_and (List.map (subst_formula var replacement) formulas)
  | Or formulas -> mk_or (List.map (subst_formula var replacement) formulas)
  | Implies (left, right) ->
      mk_implies
        (subst_formula var replacement left)
        (subst_formula var replacement right)
  | Forall (bindings, body) ->
      if List.exists (fun (name, _sort) -> String.equal name var) bindings then
        Forall (bindings, body)
      else
        let replacement_vars = all_var_names_in_int_expr String_set.empty replacement in
        let bindings, body =
          alpha_rename_quantified_bindings replacement_vars bindings body
        in
        mk_forall bindings (subst_formula var replacement body)
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
  | Int_lit _ | Real_lit _ -> acc
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
  | Forall (bindings, body) ->
      let body_vars = vars_in_formula String_set.empty body in
      let body_vars =
        List.fold_left
          (fun acc (name, _sort) -> String_set.remove name acc)
          body_vars
          bindings
      in
      String_set.union acc body_vars
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
  | Int_lit _ | Real_lit _ | Var _ -> acc
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
  | Forall (_, body) ->
      apps_in_formula acc body
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

let rec int_expr_mentions_bound_var bound = function
  | Int_lit _ | Real_lit _ -> false
  | Var name -> String_set.mem name bound
  | Add exprs | Mul exprs ->
      List.exists (int_expr_mentions_bound_var bound) exprs
  | Sub (left, right) | Div (left, right) | Mod (left, right) ->
      int_expr_mentions_bound_var bound left || int_expr_mentions_bound_var bound right
  | App (_, args) ->
      List.exists (int_expr_mentions_bound_var bound) args

let rec queryable_apps_in_int_expr bound acc = function
  | Int_lit _ | Real_lit _ | Var _ -> acc
  | Add exprs | Mul exprs ->
      List.fold_left (queryable_apps_in_int_expr bound) acc exprs
  | Sub (left, right) | Div (left, right) | Mod (left, right) ->
      queryable_apps_in_int_expr bound
        (queryable_apps_in_int_expr bound acc left)
        right
  | App (name, args) as expr ->
      let acc =
        List.fold_left (queryable_apps_in_int_expr bound) acc args
      in
      if int_expr_mentions_bound_var bound expr then acc
      else String_map.add (int_expr_to_smt expr) (name, expr) acc

let rec queryable_apps_in_formula bound acc = function
  | True | False -> acc
  | Not inner -> queryable_apps_in_formula bound acc inner
  | And formulas | Or formulas ->
      List.fold_left (queryable_apps_in_formula bound) acc formulas
  | Implies (left, right) ->
      queryable_apps_in_formula bound
        (queryable_apps_in_formula bound acc left)
        right
  | Forall (bindings, body) ->
      queryable_apps_in_formula (add_bound_names bound bindings) acc body
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      queryable_apps_in_int_expr bound
        (queryable_apps_in_int_expr bound acc left)
        right

let collect_queryable_apps formula =
  queryable_apps_in_formula String_set.empty String_map.empty formula
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
  | Real_lit text -> text
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
  | Forall ([], body) ->
      formula_to_pretty body
  | Forall (bindings, body) ->
      "forall "
      ^ String.concat ", " (List.map quantified_binding_to_pretty bindings)
      ^ ". "
      ^ formula_to_pretty body
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
