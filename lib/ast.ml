type var = string

type func_name = string

type c_type =
  | TInt
  | TFloat
  | TDouble
  | TChar
  | TBool
  | TVoid
  | TRecord of string
  | TPointer of c_type
  | TArray of c_type * int
  | TReference of c_type
  | TConstReference of c_type

type field_def = {
  field_type : c_type;
  field_name : string;
}

type record_def = {
  record_name : string;
  fields : field_def list;
}

type global_def = {
  global_type : c_type;
  global_name : var;
}

type param = {
  param_type : c_type;
  param_name : string option;
}

type quantified_var = {
  quant_type : c_type;
  quant_name : string;
}

type ghost_binding = {
  ghost_type : c_type;
  ghost_name : string;
  ghost_value : string;
}

type contract = {
  ghosts : ghost_binding list;
  require : string list;
  guarantee : string list;
  safety : string list;
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
  | AddrOf of expr
  | Index of expr * expr
  | Deref of expr
  | Field of expr * string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Mod of expr * expr
  | FuncCall of func_name * expr list

type bexpr =
  | True
  | False
  | Forall of quantified_var list * bexpr
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
  | Block of stmt list
  | LocalDecl of global_def * expr option
  | Assign of var * expr
  | Store of expr * expr
  | ArrayAssign of expr * expr * expr
  | FieldAssign of expr * string * expr
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
  locals : global_def list;
  contract : contract option;
  body : stmt;
}

type program = {
  imports : header_import list;
  records : record_def list;
  globals : global_def list;
  functions : function_def list;
  main : function_def;
}

let namespace_separator = "__ns__"

let raw_namespace_separator = "::"

let overload_separator = "__ol__"

let overload_void_tag = "void"

let contains_substring ~sub s =
  let sub_len = String.length sub in
  let s_len = String.length s in
  let rec loop i =
    if i + sub_len > s_len then false
    else if String.sub s i sub_len = sub then true
    else loop (i + 1)
  in
  if sub_len = 0 then true else loop 0

let find_substring ~sub s =
  let sub_len = String.length sub in
  let s_len = String.length s in
  let rec loop i =
    if i + sub_len > s_len then None
    else if String.sub s i sub_len = sub then Some i
    else loop (i + 1)
  in
  if sub_len = 0 then Some 0 else loop 0

let split_on_substring ~sep s =
  let sep_len = String.length sep in
  let s_len = String.length s in
  let rec find_from start =
    if start + sep_len > s_len then None
    else if String.sub s start sep_len = sep then Some start
    else find_from (start + 1)
  in
  if sep_len = 0 then [ s ]
  else
    let rec loop start parts_rev =
      match find_from start with
      | None ->
          List.rev (String.sub s start (s_len - start) :: parts_rev)
      | Some i ->
          let part = String.sub s start (i - start) in
          loop (i + sep_len) (part :: parts_rev)
    in
    loop 0 []

let has_raw_namespace name =
  contains_substring ~sub:raw_namespace_separator name

let mangle_namespace_path = function
  | [] -> ""
  | components -> String.concat namespace_separator components

let mangle_raw_namespace_name name =
  mangle_namespace_path (split_on_substring ~sep:raw_namespace_separator name)

let namespace_qualify path name =
  match path with
  | [] -> name
  | _ -> mangle_namespace_path (path @ [ name ])

let namespace_path_of_name name =
  match List.rev (split_on_substring ~sep:namespace_separator name) with
  | [] -> []
  | _base :: rev_namespace -> List.rev rev_namespace

let rec overload_type_component = function
  | TInt -> "int"
  | TFloat -> "float"
  | TDouble -> "double"
  | TChar -> "char"
  | TBool -> "bool"
  | TVoid -> "void"
  | TRecord name -> "record_" ^ name
  | TPointer inner -> overload_type_component inner ^ "_ptr"
  | TArray (inner, size) ->
      Printf.sprintf "%s_array_%d" (overload_type_component inner) size
  | TReference inner ->
      overload_type_component inner ^ "_ref"
  | TConstReference inner ->
      overload_type_component inner ^ "_const_ref"

let overload_suffix_of_params params =
  let components =
    match params with
    | [] -> [ overload_void_tag ]
    | _ ->
        List.map (fun param -> overload_type_component param.param_type) params
  in
  String.concat "__" components

let overload_base_name name =
  match find_substring ~sub:overload_separator name with
  | None -> name
  | Some index ->
      String.sub name 0 index

let has_overload_suffix name =
  not (String.equal (overload_base_name name) name)

let method_this_name = "this"

let class_method_name class_name method_name =
  class_name ^ "__" ^ method_name

let method_dot_call_prefix = "__anvil_method_dot__"

let method_arrow_call_prefix = "__anvil_method_arrow__"

let method_dot_call_name method_name =
  method_dot_call_prefix ^ method_name

let method_arrow_call_name method_name =
  method_arrow_call_prefix ^ method_name

type method_call_kind =
  | Method_dot
  | Method_arrow

let parse_method_call_name name =
  let prefix_length prefix = String.length prefix in
  if String.length name > prefix_length method_dot_call_prefix
     && String.sub name 0 (prefix_length method_dot_call_prefix) = method_dot_call_prefix
  then
    Some
      ( Method_dot
      , String.sub
          name
          (prefix_length method_dot_call_prefix)
          (String.length name - prefix_length method_dot_call_prefix) )
  else if
    String.length name > prefix_length method_arrow_call_prefix
    && String.sub name 0 (prefix_length method_arrow_call_prefix) = method_arrow_call_prefix
  then
    Some
      ( Method_arrow
      , String.sub
          name
          (prefix_length method_arrow_call_prefix)
          (String.length name - prefix_length method_arrow_call_prefix) )
  else
    None

let parse_class_method_name name =
  let name = overload_base_name name in
  let rec find_last_double_underscore i last =
    if i + 1 >= String.length name then last
    else if name.[i] = '_' && name.[i + 1] = '_' then
      find_last_double_underscore (i + 1) (Some i)
    else
      find_last_double_underscore (i + 1) last
  in
  match find_last_double_underscore 0 None with
  | None -> None
  | Some sep ->
      let class_name = String.sub name 0 sep in
      let method_name =
        String.sub name (sep + 2) (String.length name - sep - 2)
      in
      if String.length class_name = 0 || String.length method_name = 0 then None
      else Some (class_name, method_name)

let overload_dispatch_params name params =
  match params with
  | { param_type = TPointer (TRecord class_name); param_name = Some receiver } :: rest ->
      (match parse_class_method_name name with
      | Some (name_class, _method_name)
        when String.equal receiver method_this_name && String.equal class_name name_class ->
          rest
      | Some _ | None ->
          params)
  | _ ->
      params

let mangle_overload_name name params =
  let params = overload_dispatch_params name params in
  overload_base_name name ^ overload_separator ^ overload_suffix_of_params params

let rec c_type_to_c = function
  | TInt -> "int"
  | TFloat -> "float"
  | TDouble -> "double"
  | TChar -> "char"
  | TBool -> "bool"
  | TVoid -> "void"
  | TRecord name -> "struct " ^ name
  | TPointer inner -> c_type_to_c inner ^ "*"
  | TArray (inner, size) ->
      Printf.sprintf "%s[%d]" (c_type_to_c inner) size
  | TReference inner -> c_type_to_c inner ^ "&"
  | TConstReference inner -> "const " ^ c_type_to_c inner ^ "&"

let type_with_name_to_c c_type name =
  match c_type with
  | TArray (inner, size) ->
      Printf.sprintf "%s %s[%d]" (c_type_to_c inner) name size
  | _ ->
      c_type_to_c c_type ^ " " ^ name

let global_names globals =
  List.map (fun global -> global.global_name) globals

let is_pointer_type = function
  | TPointer _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TArray _
  | TReference _ | TConstReference _ ->
      false

let is_reference_type = function
  | TReference _ | TConstReference _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _ | TArray _ ->
      false

let is_const_reference_type = function
  | TConstReference _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _ | TArray _
  | TReference _ ->
      false

let reference_inner_type = function
  | TReference inner | TConstReference inner -> Some inner
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _ | TArray _ ->
      None

let strip_reference_type = function
  | TReference inner | TConstReference inner -> inner
  | c_type -> c_type

let lower_reference_type = function
  | TReference inner | TConstReference inner -> TPointer inner
  | c_type -> c_type

let pointer_base_type = function
  | TPointer inner -> Some inner
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TArray _
  | TReference _ | TConstReference _ ->
      None

let pointer_object_byte_size = 8

let is_array_type = function
  | TArray _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _
  | TReference _ | TConstReference _ ->
      false

let array_element_type = function
  | TArray (inner, _) -> Some inner
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _
  | TReference _ | TConstReference _ ->
      None

let array_length = function
  | TArray (_, length) -> Some length
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TRecord _ | TPointer _
  | TReference _ | TConstReference _ ->
      None

let is_record_type = function
  | TRecord _ -> true
  | TInt | TFloat | TDouble | TChar | TBool | TVoid | TPointer _ | TArray _
  | TReference _ | TConstReference _ ->
      false

let is_real_type = function
  | TFloat | TDouble -> true
  | TInt | TChar | TBool | TVoid | TRecord _ | TPointer _ | TArray _
  | TReference _ | TConstReference _ ->
      false

let is_integer_like_type = function
  | TInt | TChar | TBool -> true
  | TFloat | TDouble | TVoid | TRecord _ | TPointer _ | TArray _
  | TReference _ | TConstReference _ ->
      false

let is_scalar_type = function
  | TInt | TFloat | TDouble | TChar | TBool -> true
  | TVoid | TRecord _ | TPointer _ | TArray _ | TReference _ | TConstReference _ -> false

let lookup_record records name =
  List.find_opt (fun record -> String.equal record.record_name name) records

let lookup_record_field records record_name field_name =
  match lookup_record records record_name with
  | None -> None
  | Some record ->
      List.find_opt (fun field -> String.equal field.field_name field_name) record.fields

let record_field_type records record_name field_name =
  Option.map
    (fun field -> field.field_type)
    (lookup_record_field records record_name field_name)

let rec c_type_object_byte_size records = function
  | TInt -> 4
  | TFloat -> 4
  | TDouble -> 8
  | TChar -> 1
  | TBool -> 1
  | TRecord name ->
      (match lookup_record records name with
      | None -> failwith ("unknown record type `" ^ name ^ "`")
      | Some record ->
          List.fold_left
            (fun acc field -> acc + c_type_object_byte_size records field.field_type)
            0
            record.fields)
  | TVoid -> failwith "void has no object byte size"
  | TPointer _ -> pointer_object_byte_size
  | TArray (inner, size) -> size * c_type_object_byte_size records inner
  | TReference _ | TConstReference _ ->
      failwith "reference types should be lowered before object-size queries"

let record_field_offset records record_name field_name =
  match lookup_record records record_name with
  | None -> None
  | Some record ->
      let rec loop offset = function
        | [] -> None
        | field :: rest ->
            if String.equal field.field_name field_name then Some offset
            else
              loop
                (offset + c_type_object_byte_size records field.field_type)
                rest
      in
      loop 0 record.fields

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
  | TVoid | TRecord _ | TPointer _ | TArray _ | TReference _ | TConstReference _ ->
      failwith "unsupported helper load type"

let load_ptr_block_helper_name = "__anvil_load_ptr_block"

let load_ptr_offset_helper_name = "__anvil_load_ptr_offset"

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

let expr_prec_add = 10

let expr_prec_mul = 20

let expr_prec_unary = 30

let expr_prec_postfix = 40

let expr_prec_atom = 50

let expr_precedence = function
  | Add _ | Sub _ -> expr_prec_add
  | Mul _ | Div _ | Mod _ -> expr_prec_mul
  | AddrOf _ | Deref _ -> expr_prec_unary
  | Index _ | Field _ | FuncCall _ -> expr_prec_postfix
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ -> expr_prec_atom

let parenthesize_if needed text =
  if needed then "(" ^ text ^ ")" else text

let rec expr_to_c_with_prec min_prec expr =
  let rendered =
    match expr with
    | Int i -> string_of_int i
    | FloatLit text
    | DoubleLit text ->
        text
    | CharLit value -> escape_char_code value
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | Var x -> x
    | AddrOf value ->
        "&" ^ expr_to_c_with_prec expr_prec_postfix value
    | Index (base, index) ->
        expr_to_c_with_prec expr_prec_postfix base
        ^ "[" ^ expr_to_c_with_prec 0 index ^ "]"
    | Deref value ->
        "*" ^ expr_to_c_with_prec expr_prec_unary value
    | Field (Deref base, field) ->
        expr_to_c_with_prec expr_prec_postfix base ^ "->" ^ field
    | Field (base, field) ->
        expr_to_c_with_prec expr_prec_postfix base ^ "." ^ field
    | Add (left, right) ->
        expr_to_c_with_prec expr_prec_add left
        ^ " + "
        ^ expr_to_c_with_prec (expr_prec_add + 1) right
    | Sub (left, right) ->
        expr_to_c_with_prec expr_prec_add left
        ^ " - "
        ^ expr_to_c_with_prec (expr_prec_add + 1) right
    | Mul (left, right) ->
        expr_to_c_with_prec expr_prec_mul left
        ^ " * "
        ^ expr_to_c_with_prec (expr_prec_mul + 1) right
    | Div (left, right) ->
        expr_to_c_with_prec expr_prec_mul left
        ^ " / "
        ^ expr_to_c_with_prec (expr_prec_mul + 1) right
    | Mod (left, right) ->
        expr_to_c_with_prec expr_prec_mul left
        ^ " % "
        ^ expr_to_c_with_prec (expr_prec_mul + 1) right
    | FuncCall (f, args) ->
        f ^ "(" ^ String.concat ", " (List.map (expr_to_c_with_prec 0) args) ^ ")"
  in
  parenthesize_if (expr_precedence expr < min_prec) rendered

let expr_to_c expr =
  expr_to_c_with_prec 0 expr

let postfix_receiver_to_c expr =
  expr_to_c_with_prec expr_prec_postfix expr

let quantified_var_to_c quantified =
  type_with_name_to_c quantified.quant_type quantified.quant_name

let rec bexpr_to_c = function
  | True -> "1"
  | False -> "0"
  | Forall (bindings, body) ->
      "forall("
      ^ String.concat ", " (List.map quantified_var_to_c bindings)
      ^ "). "
      ^ bexpr_to_c body
  | Eq (a, b) -> "(" ^ expr_to_c a ^ " == " ^ expr_to_c b ^ ")"
  | Neq (a, b) -> "(" ^ expr_to_c a ^ " != " ^ expr_to_c b ^ ")"
  | Lt (a, b) -> "(" ^ expr_to_c a ^ " < " ^ expr_to_c b ^ ")"
  | Le (a, b) -> "(" ^ expr_to_c a ^ " <= " ^ expr_to_c b ^ ")"
  | Gt (a, b) -> "(" ^ expr_to_c a ^ " > " ^ expr_to_c b ^ ")"
  | Ge (a, b) -> "(" ^ expr_to_c a ^ " >= " ^ expr_to_c b ^ ")"
  | Not p -> "(!" ^ bexpr_to_c p ^ ")"
  | And (p, q) -> "(" ^ bexpr_to_c p ^ " && " ^ bexpr_to_c q ^ ")"
  | Or (p, q) -> "(" ^ bexpr_to_c p ^ " || " ^ bexpr_to_c q ^ ")"

let rec bexpr_to_annotation = function
  | True -> "1"
  | False -> "0"
  | Forall (bindings, body) ->
      "forall("
      ^ String.concat ", " (List.map quantified_var_to_c bindings)
      ^ "). "
      ^ bexpr_to_annotation body
  | Eq (a, b) -> "(" ^ expr_to_c a ^ " == " ^ expr_to_c b ^ ")"
  | Neq (a, b) -> "(" ^ expr_to_c a ^ " != " ^ expr_to_c b ^ ")"
  | Lt (a, b) -> "(" ^ expr_to_c a ^ " < " ^ expr_to_c b ^ ")"
  | Le (a, b) -> "(" ^ expr_to_c a ^ " <= " ^ expr_to_c b ^ ")"
  | Gt (a, b) -> "(" ^ expr_to_c a ^ " > " ^ expr_to_c b ^ ")"
  | Ge (a, b) -> "(" ^ expr_to_c a ^ " >= " ^ expr_to_c b ^ ")"
  | Not p -> "(!" ^ bexpr_to_annotation p ^ ")"
  | And (p, q) -> "(" ^ bexpr_to_annotation p ^ " && " ^ bexpr_to_annotation q ^ ")"
  | Or (Not premise, conclusion) ->
      "(" ^ bexpr_to_annotation premise ^ " ==> " ^ bexpr_to_annotation conclusion
      ^ ")"
  | Or (p, q) -> "(" ^ bexpr_to_annotation p ^ " || " ^ bexpr_to_annotation q ^ ")"

let indent n = String.make (n * 2) ' '

let param_to_c param =
  match param.param_name with
  | None -> c_type_to_c param.param_type
  | Some name -> type_with_name_to_c param.param_type name

let params_to_c params =
  match params with
  | [] -> "void"
  | params -> String.concat ", " (List.map param_to_c params)

let function_signature_to_c fn =
  type_with_name_to_c fn.return_type fn.name
  ^ "(" ^ params_to_c fn.params ^ ")"

let function_prototype_to_c fn =
  function_signature_to_c fn ^ ";\n"

let local_decl_to_c ~indent_level local =
  indent indent_level
  ^ type_with_name_to_c local.global_type local.global_name
  ^ ";\n"

let field_def_to_c ~indent_level field =
  indent indent_level
  ^ type_with_name_to_c field.field_type field.field_name
  ^ ";\n"

let record_def_to_c record =
  "struct " ^ record.record_name ^ " {\n"
  ^ String.concat "" (List.map (field_def_to_c ~indent_level:1) record.fields)
  ^ "};\n"

let sort_uniq_strings names =
  List.sort_uniq String.compare names

let empty_contract = {
  ghosts = [];
  require = [];
  guarantee = [];
  safety = [];
}

let contract_is_empty contract =
  contract.ghosts = []
  && contract.require = []
  && contract.guarantee = []
  && contract.safety = []

let merge_contracts left right =
  {
    ghosts = left.ghosts @ right.ghosts;
    require = left.require @ right.require;
    guarantee = left.guarantee @ right.guarantee;
    safety = left.safety @ right.safety;
  }

let contract_to_c function_name = function
  | None -> ""
  | Some contract ->
      let ghost_lines =
        List.map
          (fun ghost ->
            " * @Ghost " ^ c_type_to_c ghost.ghost_type ^ " " ^ ghost.ghost_name
            ^ " = " ^ ghost.ghost_value ^ "\n")
          contract.ghosts
      in
      let clause_lines tag clauses =
        List.map (fun clause -> " * " ^ tag ^ " " ^ clause ^ "\n") clauses
      in
      "/* @Contract " ^ function_name ^ "\n"
      ^ String.concat ""
          (ghost_lines
          @ clause_lines "@Require" contract.require
          @ clause_lines "@Guarantee" contract.guarantee
          @ clause_lines "@Safety" contract.safety)
      ^ " */\n"

let zero_literal_for_type = function
  | TInt -> "0"
  | TFloat -> "0.0f"
  | TDouble -> "0.0"
  | TChar -> "'\\0'"
  | TBool -> "false"
  | TVoid -> failwith "void does not have a zero literal"
  | TRecord _ -> failwith "record values do not have a zero literal"
  | TPointer _ -> "0"
  | TArray _ -> failwith "array does not have a zero literal"
  | TReference _ | TConstReference _ ->
      failwith "reference values do not have a zero literal"

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

let compound_rhs_suffix target = function
  | Add (left, right) when left = target ->
      Some ("+=", right)
  | Sub (left, right) when left = target ->
      Some ("-=", right)
  | _ ->
      None

let rec stmt_to_c ~indent_level ~return_type = function
  | Skip -> indent indent_level ^ ";\n"
  | Block stmts ->
      indent indent_level ^ "{\n"
      ^ String.concat ""
          (List.map (stmt_to_c ~indent_level:(indent_level + 1) ~return_type) stmts)
      ^ indent indent_level ^ "}\n"
  | LocalDecl (local, init) ->
      let decl =
        indent indent_level
        ^ type_with_name_to_c local.global_type local.global_name
      in
      (match init with
      | None -> decl ^ ";\n"
      | Some expr -> decl ^ " = " ^ expr_to_c expr ^ ";\n")
  | Assign (x, e) ->
      (match compound_rhs_suffix (Var x) e with
      | Some (op, rhs) ->
          indent indent_level ^ x ^ " " ^ op ^ " " ^ expr_to_c rhs ^ ";\n"
      | None ->
          indent indent_level ^ x ^ " = " ^ expr_to_c e ^ ";\n")
  | Store (ptr, value) ->
      (match compound_rhs_suffix (Deref ptr) value with
      | Some (op, rhs) ->
          indent indent_level ^ "*" ^ expr_to_c ptr ^ " " ^ op ^ " " ^ expr_to_c rhs ^ ";\n"
      | None ->
          indent indent_level ^ "*" ^ expr_to_c ptr ^ " = " ^ expr_to_c value ^ ";\n")
  | ArrayAssign (base, index, value) ->
      (match compound_rhs_suffix (Index (base, index)) value with
      | Some (op, rhs) ->
          indent indent_level ^ expr_to_c base ^ "[" ^ expr_to_c index ^ "] "
          ^ op ^ " " ^ expr_to_c rhs ^ ";\n"
      | None ->
          indent indent_level ^ expr_to_c base ^ "[" ^ expr_to_c index ^ "] = "
          ^ expr_to_c value ^ ";\n")
  | FieldAssign (Deref base, field, value) ->
      (match compound_rhs_suffix (Field (Deref base, field)) value with
      | Some (op, rhs) ->
          indent indent_level ^ postfix_receiver_to_c base ^ "->" ^ field ^ " "
          ^ op ^ " " ^ expr_to_c rhs ^ ";\n"
      | None ->
          indent indent_level ^ postfix_receiver_to_c base ^ "->" ^ field ^ " = "
          ^ expr_to_c value ^ ";\n")
  | FieldAssign (base, field, value) ->
      (match compound_rhs_suffix (Field (base, field)) value with
      | Some (op, rhs) ->
          indent indent_level ^ postfix_receiver_to_c base ^ "." ^ field ^ " "
          ^ op ^ " " ^ expr_to_c rhs ^ ";\n"
      | None ->
          indent indent_level ^ postfix_receiver_to_c base ^ "." ^ field ^ " = "
          ^ expr_to_c value ^ ";\n")
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

let rec vars_in_expr = function
  | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ -> []
  | Var name -> [ name ]
  | AddrOf inner -> vars_in_expr inner
  | Index (base, index) ->
      vars_in_expr base @ vars_in_expr index
  | Deref inner -> vars_in_expr inner
  | Field (base, _) -> vars_in_expr base
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right)
  | Mod (left, right) ->
      vars_in_expr left @ vars_in_expr right
  | FuncCall (_, args) ->
      List.concat_map vars_in_expr args

let rec vars_in_bexpr = function
  | True | False -> []
  | Forall (bindings, body) ->
      let bound_names = List.map (fun binding -> binding.quant_name) bindings in
      List.filter
        (fun name ->
          not (List.exists (fun bound_name -> String.equal name bound_name) bound_names))
        (vars_in_bexpr body)
  | Eq (left, right)
  | Neq (left, right)
  | Lt (left, right)
  | Le (left, right)
  | Gt (left, right)
  | Ge (left, right) ->
      vars_in_expr left @ vars_in_expr right
  | Not inner -> vars_in_bexpr inner
  | And (left, right)
  | Or (left, right) ->
      vars_in_bexpr left @ vars_in_bexpr right

let rec vars_in_stmt = function
  | Skip -> []
  | Block stmts | Seq stmts ->
      List.concat_map vars_in_stmt stmts
  | LocalDecl (_, init) ->
      (match init with
      | None -> []
      | Some expr -> vars_in_expr expr)
  | Assign (name, expr) ->
      name :: vars_in_expr expr
  | Store (ptr, value) ->
      vars_in_expr ptr @ vars_in_expr value
  | ArrayAssign (base, index, value) ->
      vars_in_expr base @ vars_in_expr index @ vars_in_expr value
  | FieldAssign (base, _, value) ->
      vars_in_expr base @ vars_in_expr value
  | If (cond, then_branch, else_branch) ->
      vars_in_bexpr cond @ vars_in_stmt then_branch @ vars_in_stmt else_branch
  | While (invariant, cond, body) ->
      (match invariant with
      | None -> []
      | Some invariant -> vars_in_bexpr invariant)
      @ vars_in_bexpr cond
      @ vars_in_stmt body
  | Assume cond | Assert (_, cond) ->
      vars_in_bexpr cond
  | Free ptr ->
      vars_in_expr ptr
  | Return None -> []
  | Return (Some value) ->
      vars_in_expr value

let function_def_to_c fn =
  let signature = function_signature_to_c fn in
  let referenced_vars =
    sort_uniq_strings (vars_in_stmt fn.body)
  in
  let unused_params =
    fn.params
    |> List.filter_map (fun param ->
           match param.param_name with
           | Some name when not (List.mem name referenced_vars) ->
               Some (indent 1 ^ "(void) " ^ name ^ ";\n")
           | Some _ | None ->
               None)
    |> String.concat ""
  in
  let local_decls =
    String.concat "" (List.map (local_decl_to_c ~indent_level:1) fn.locals)
  in
  let unused_locals =
    fn.locals
    |> List.filter (fun local ->
           not (List.mem local.global_name referenced_vars))
    |> List.map (fun local ->
           indent 1 ^ "(void) " ^ local.global_name ^ ";\n")
    |> String.concat ""
  in
  let body = stmt_to_c ~indent_level:1 ~return_type:fn.return_type fn.body in
  contract_to_c fn.name fn.contract
  ^ signature ^ " {\n"
  ^ unused_params
  ^ local_decls
  ^ unused_locals
  ^ body
  ^ "}\n"

let helper_prototype name =
  match name with
  | "__anvil_load_int" -> "int __anvil_load_int(int block, int offset);\n"
  | "__anvil_load_float" -> "float __anvil_load_float(int block, int offset);\n"
  | "__anvil_load_double" -> "double __anvil_load_double(int block, int offset);\n"
  | "__anvil_load_char" -> "char __anvil_load_char(int block, int offset);\n"
  | "__anvil_load_bool" -> "bool __anvil_load_bool(int block, int offset);\n"
  | "__anvil_load_ptr_block" -> "int __anvil_load_ptr_block(int block, int offset);\n"
  | "__anvil_load_ptr_offset" -> "int __anvil_load_ptr_offset(int block, int offset);\n"
  | _ -> failwith ("unknown helper function " ^ name)

let helper_prototypes p =
  let rec helpers_in_expr acc = function
    | Int _ | FloatLit _ | DoubleLit _ | CharLit _ | BoolLit _ | Var _ ->
        acc
    | AddrOf inner -> helpers_in_expr acc inner
    | Index (base, index) ->
        helpers_in_expr (helpers_in_expr acc base) index
    | Deref inner -> helpers_in_expr acc inner
    | Field (base, _) -> helpers_in_expr acc base
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
    | Forall (_, body) -> helpers_in_bexpr acc body
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
    | Block stmts ->
        List.fold_left helpers_in_stmt acc stmts
    | LocalDecl (_, init) ->
        (match init with
        | None -> acc
        | Some expr -> helpers_in_expr acc expr)
    | Assign (_, expr) -> helpers_in_expr acc expr
    | Store (ptr, value) -> helpers_in_expr (helpers_in_expr acc ptr) value
    | ArrayAssign (base, index, value) ->
        helpers_in_expr
          (helpers_in_expr (helpers_in_expr acc base) index)
          value
    | FieldAssign (base, _, value) ->
        helpers_in_expr (helpers_in_expr acc base) value
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
  let records =
    match p.records with
    | [] -> ""
    | records ->
        String.concat "\n" (List.map record_def_to_c records) ^ "\n"
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
  let prototypes =
    match p.functions with
    | [] -> ""
    | functions ->
        String.concat "" (List.map function_prototype_to_c functions) ^ "\n"
  in
  let functions =
    match p.functions with
    | [] -> ""
    | functions ->
        String.concat "\n" (List.map function_def_to_c functions) ^ "\n"
  in
  let main = function_def_to_c p.main in
  header ^ helpers ^ imports ^ records ^ globals ^ prototypes ^ functions ^ main
