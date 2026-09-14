open Ast

let param param_type param_name =
  { param_type; param_name = Some param_name }

let contracted ?(contract = empty_contract) name return_type params =
  { name; return_type; params; contract }

let method_fn ?contract class_name method_name return_type params =
  contracted ?contract
    (class_method_name class_name method_name)
    return_type
    ({ param_type = TPointer (TRecord class_name); param_name = Some method_this_name }
     :: params)

let rank_config = "vulcan__ns__rank_config"

let feature_store = "vulcan__ns__feature_store"

let max_add_listeners_arity = 10

let add_listeners_arity listener_count =
  let listeners =
    List.init listener_count (fun index -> param TInt (Printf.sprintf "listener_%d" (index + 1)))
  in
  method_fn rank_config "add_listeners" TVoid (param TInt "feature" :: listeners)

let listener_builtins =
  [
    contracted "vulcan__ns__listeners__ns__global__ns__Average" TInt [];
    contracted "vulcan__ns__listeners__ns__global__ns__MinMax" TInt [];
    contracted "vulcan__ns__listeners__ns__global__ns__RollingWindow" TInt [ param TInt "window" ];
    contracted
      "vulcan__ns__listeners__ns__global__ns__RollingPercentile"
      TInt
      [ param TInt "percentile" ];
    contracted
      "vulcan__ns__listeners__ns__global__ns__EWMA"
      TInt
      [ param TDouble "alpha" ];
    contracted
      "vulcan__ns__listeners__ns__global__ns__EWMA"
      TInt
      [ param TDouble "alpha_fast"; param TDouble "alpha_slow" ];
    contracted "vulcan__ns__listeners__ns__object__ns__Average" TInt [];
    contracted "vulcan__ns__listeners__ns__object__ns__MinMax" TInt [];
    contracted "vulcan__ns__listeners__ns__object__ns__RollingWindow" TInt [ param TInt "window" ];
    contracted
      "vulcan__ns__listeners__ns__object__ns__RollingPercentile"
      TInt
      [ param TInt "percentile" ];
    contracted
      "vulcan__ns__listeners__ns__object__ns__EWMA"
      TInt
      [ param TDouble "alpha" ];
    contracted
      "vulcan__ns__listeners__ns__object__ns__EWMA"
      TInt
      [ param TDouble "alpha_fast"; param TDouble "alpha_slow" ];
    contracted
      "vulcan__ns__listeners__ns__object__ns__PopulationPercentile"
      TInt
      [];
  ]

let feature_store_builtins =
  [
    method_fn feature_store "get_latest" TDouble [ param TInt "feature" ];
    method_fn feature_store "get_latest" TDouble [ param TInt "feature"; param TInt "obj_id" ];
    method_fn feature_store "get_avg" TDouble [ param TInt "feature" ];
    method_fn feature_store "get_avg" TDouble [ param TInt "feature"; param TInt "obj_id" ];
    method_fn feature_store "get_max" TDouble [ param TInt "feature" ];
    method_fn feature_store "get_max" TDouble [ param TInt "feature"; param TInt "obj_id" ];
    method_fn feature_store "get_min" TDouble [ param TInt "feature" ];
    method_fn feature_store "get_min" TDouble [ param TInt "feature"; param TInt "obj_id" ];
    method_fn feature_store "get_kth_recent" TDouble [ param TInt "feature"; param TInt "k" ];
    method_fn
      feature_store
      "get_kth_recent"
      TDouble
      [ param TInt "feature"; param TInt "obj_id"; param TInt "k" ];
    method_fn feature_store "get_percentile" TDouble [ param TInt "feature"; param TDouble "pct" ];
    method_fn
      feature_store
      "get_percentile"
      TDouble
      [ param TInt "feature"; param TInt "obj_id"; param TDouble "pct" ];
    method_fn feature_store "get_ewma" TDouble [ param TInt "feature"; param TDouble "alpha" ];
    method_fn
      feature_store
      "get_ewma"
      TDouble
      [ param TInt "feature"; param TInt "obj_id"; param TDouble "alpha" ];
  ]

let std_contract clauses =
  {
    empty_contract with
    require = List.map fst clauses;
    guarantee = List.map snd clauses;
  }

let std_builtins =
  [
    contracted
      ~contract:
        {
          empty_contract with
          guarantee =
            [ "result <= x"; "result <= y"; "(result == x) || (result == y)" ];
        }
      "std__ns__min"
      TDouble
      [ param TDouble "x"; param TDouble "y" ];
    contracted
      ~contract:
        {
          empty_contract with
          guarantee =
            [ "result <= x"; "result <= y"; "(result == x) || (result == y)" ];
        }
      "std__ns__min"
      TInt
      [ param TInt "x"; param TInt "y" ];
    contracted
      ~contract:
        {
          empty_contract with
          guarantee = [ "result >= 0" ];
        }
      "std__ns__abs"
      TDouble
      [ param TDouble "x" ];
    contracted
      ~contract:
        {
          empty_contract with
          require = [ "x >= 0" ];
          guarantee = [ "result >= 0" ];
        }
      "std__ns__sqrt"
      TDouble
      [ param TDouble "x" ];
    contracted
      ~contract:
        {
          empty_contract with
          require = [ "x > 0" ];
        }
      "std__ns__log"
      TDouble
      [ param TDouble "x" ];
    contracted "std__ns__pow" TDouble [ param TDouble "x"; param TDouble "y" ];
  ]

let builtin_imports =
  [
    {
      include_path = "";
      functions =
        listener_builtins
        @ feature_store_builtins
        @ List.init max_add_listeners_arity (fun index -> add_listeners_arity (index + 1))
        @ std_builtins;
    };
  ]

let same_signature
    (left : imported_function)
    (right : imported_function) =
  left.name = right.name
  && left.return_type = right.return_type
  && List.length left.params = List.length right.params
  && List.for_all2
       (fun (left_param : param) (right_param : param) ->
         left_param.param_type = right_param.param_type)
       left.params
       right.params

let add_imports imports =
  let existing =
    List.concat_map
      (fun (header : header_import) -> header.functions)
      imports
  in
  let missing_builtin_functions =
    List.concat_map
      (fun (header : header_import) -> header.functions)
      builtin_imports
    |> List.filter (fun builtin_fn ->
         not
           (List.exists
              (fun existing_fn -> same_signature builtin_fn existing_fn)
              existing))
  in
  match missing_builtin_functions with
  | [] ->
      imports
  | functions ->
      imports @ [ { include_path = ""; functions } ]
