open Ast

(* Verification models a call as a pure function of its arguments: nothing a
   callee writes is reflected in the caller's state. A call statement such as
   `set_g();` is only ever made for such writes, so if the callee is defined
   here and can make one, treating the statement as a no-op would let false
   claims about that state verify. Such statements are rejected instead.

   Callees without a body in the program (header or external functions) are
   trusted to be effect-free, as they already are in `x = f(...)`. *)

let ( let* ) result f =
  match result with
  | Ok value -> f value
  | Error _ as error -> error

let param_type (fn : function_def) name =
  List.find_map
    (fun (param : param) ->
      match param.param_name with
      | Some param_name when String.equal param_name name -> Some param.param_type
      | Some _ | None -> None)
    fn.params

let declared_local (fn : function_def) name =
  List.find_map
    (fun (local : global_def) ->
      if String.equal local.global_name name then Some local.global_type else None)
    fn.locals

let local_type (fn : function_def) name =
  match declared_local fn name with
  | Some _ as local_type -> local_type
  | None -> param_type fn name

(* An lvalue rooted in storage [fn] owns: a local array or record, or a record
   parameter (passed by copy). Array parameters decay to pointers, and
   pointers and references alias storage the caller can see. *)
let rec owned_lvalue fn = function
  | Var name ->
      (match declared_local fn name, param_type fn name with
      | Some (TArray _ | TRecord _), _ | None, Some (TRecord _) -> true
      | _ -> false)
  | Index (base, _) | Field (base, _) -> owned_lvalue fn base
  | _ -> false

(* The first write in [fn]'s own body that a caller could observe. *)
let rec direct_write fn stmt =
  match stmt with
  | Assign (name, _) ->
      (match local_type fn name with
      | Some (TReference _ | TConstReference _) ->
          Some (Printf.sprintf "assigns through reference `%s`" name)
      | Some _ -> None
      | None -> Some (Printf.sprintf "assigns global `%s`" name))
  | Store _ -> Some "writes through a pointer"
  | ArrayAssign (base, _, _) when owned_lvalue fn base -> None
  | ArrayAssign _ -> Some "writes to an array it does not own"
  | FieldAssign (base, _, _) when owned_lvalue fn base -> None
  | FieldAssign (_, field, _) ->
      Some (Printf.sprintf "writes field `%s` of a record it does not own" field)
  | Free _ -> Some "frees memory"
  | Block stmts | Seq stmts -> List.find_map (direct_write fn) stmts
  | If (_, then_branch, else_branch) ->
      (match direct_write fn then_branch with
      | Some _ as write -> write
      | None -> direct_write fn else_branch)
  | While (_, _, body) -> direct_write fn body
  | Skip | Break | Continue | LocalDecl _ | ExprStmt _ | Assume _ | Assert _ | Return _ ->
      None

let dedup names = List.sort_uniq String.compare names

(* Maps each defined function that can write caller-visible state, directly
   or through a defined callee, to a description of how. *)
let effects_of_program (program : program) =
  let defined name =
    List.exists (fun (fn : function_def) -> String.equal fn.name name) program.functions
  in
  let callees (fn : function_def) =
    Strict_syntax.calls_in_stmt [] fn.body |> List.filter defined |> dedup
  in
  let direct =
    List.filter_map
      (fun (fn : function_def) ->
        Option.map (fun reason -> fn.name, reason) (direct_write fn fn.body))
      program.functions
  in
  (* Propagate up the call graph until nothing changes; a function inherits the
     reason of the first effectful callee it reaches. *)
  let rec saturate effects =
    let inherited =
      List.filter_map
        (fun (fn : function_def) ->
          if List.mem_assoc fn.name effects then None
          else
            List.find_map
              (fun callee ->
                Option.map
                  (fun reason ->
                    fn.name, Printf.sprintf "calls `%s`, which %s" callee reason)
                  (List.assoc_opt callee effects))
              (callees fn))
        program.functions
    in
    match inherited with
    | [] -> effects
    | _ -> saturate (effects @ inherited)
  in
  saturate direct

let rec statement_calls acc = function
  | ExprStmt expr -> Strict_syntax.calls_in_expr acc expr
  | Block stmts | Seq stmts -> List.fold_left statement_calls acc stmts
  | If (_, then_branch, else_branch) ->
      statement_calls (statement_calls acc then_branch) else_branch
  | While (_, _, body) -> statement_calls acc body
  | Skip | Break | Continue | LocalDecl _ | Assign _ | Store _ | ArrayAssign _
  | FieldAssign _ | Assume _ | Assert _ | Free _ | Return _ ->
      acc

let check_program (program : program) =
  let effects = effects_of_program program in
  let check_function (fn : function_def) =
    match
      List.find_map
        (fun callee ->
          Option.map (fun reason -> callee, reason) (List.assoc_opt callee effects))
        (statement_calls [] fn.body |> dedup)
    with
    | None -> Ok ()
    | Some (callee, reason) ->
        Error
          (Printf.sprintf
             "cannot verify the call statement to `%s` in `%s`: `%s` %s, and \
              Anvil does not model the side effects of calls"
             callee fn.name callee reason)
  in
  List.fold_left
    (fun result fn ->
      let* () = result in
      check_function fn)
    (Ok ()) program.functions
