open Ast

exception Error of string

let fail fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

let read_all in_channel =
  let buffer = Buffer.create 1024 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    match input in_channel chunk 0 (Bytes.length chunk) with
    | 0 -> Buffer.contents buffer
    | n ->
        Buffer.add_subbytes buffer chunk 0 n;
        loop ()
  in
  loop ()

let read_file path =
  let in_channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr in_channel)
    (fun () -> read_all in_channel)

let starts_with ~prefix s =
  let prefix_len = String.length prefix in
  let s_len = String.length s in
  prefix_len <= s_len && String.sub s 0 prefix_len = prefix

let ends_with ~suffix s =
  let suffix_len = String.length suffix in
  let s_len = String.length s in
  suffix_len <= s_len
  && String.sub s (s_len - suffix_len) suffix_len = suffix

let find_substring ~sub s =
  let sub_len = String.length sub in
  let total_len = String.length s in
  let rec loop i =
    if i + sub_len > total_len then None
    else if String.sub s i sub_len = sub then Some i
    else loop (i + 1)
  in
  loop 0

let is_ident_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let compact_no_space s =
  let buffer = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | ' ' | '\t' | '\r' | '\n' -> ()
      | _ -> Buffer.add_char buffer c)
    s;
  Buffer.contents buffer

let rec pointer_type base = function
  | 0 -> base
  | depth -> TPointer (pointer_type base (depth - 1))

let is_qualified_ident text =
  let is_ident segment =
    segment <> ""
    && String.for_all
         (function
           | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
           | _ -> false)
         segment
  in
  split_on_substring ~sep:"::" text |> List.for_all is_ident

let parse_c_type text =
  let compact = compact_no_space text in
  let strip_trailing_char ch text =
    let rec loop count index =
      if index >= 0 && text.[index] = ch then
        loop (count + 1) (index - 1)
      else
        count, String.sub text 0 (index + 1)
    in
    loop 0 (String.length text - 1)
  in
  let is_const, compact =
    if starts_with ~prefix:"const" compact then
      true, String.sub compact 5 (String.length compact - 5)
    else
      false, compact
  in
  let ref_count, compact = strip_trailing_char '&' compact in
  if ref_count > 1 then
    fail "unsupported reference type `%s`" text;
  let star_count, compact = strip_trailing_char '*' compact in
  let base =
    match compact with
    | "int" -> TInt
    | "float" -> TFloat
    | "double" -> TDouble
    | "char" -> TChar
    | "bool" -> TBool
    | "void" -> TVoid
    | _ when starts_with ~prefix:"struct" compact ->
        let name = String.sub compact 6 (String.length compact - 6) in
        if name = "" then fail "unsupported C type `%s`" text else TRecord name
    | _ when is_qualified_ident compact ->
        TRecord compact
    | _ ->
        fail "unsupported C type `%s`" text
  in
  let base = pointer_type base star_count in
  match is_const, ref_count with
  | false, 0 -> base
  | false, 1 -> TReference base
  | true, 1 -> TConstReference base
  | true, 0 ->
      fail "only const references are supported in header contracts, got `%s`" text
  | _ ->
      fail "unsupported C type `%s`" text

let split_last_identifier text =
  let trimmed = String.trim text in
  let last = ref (String.length trimmed - 1) in
  while !last >= 0 && trimmed.[!last] = ' ' do
    decr last
  done;
  if !last < 0 || not (is_ident_char trimmed.[!last]) then None
  else
    let first = ref !last in
    while !first >= 0 && is_ident_char trimmed.[!first] do
      decr first
    done;
    let name =
      String.sub trimmed (!first + 1) (!last - !first)
    in
    let prefix = String.sub trimmed 0 (!first + 1) |> String.trim in
    Some (prefix, name)

let parse_param text =
  let trimmed = String.trim text in
  match split_last_identifier trimmed with
  | Some (type_part, name) when type_part <> "" ->
      { param_type = parse_c_type type_part; param_name = Some name }
  | _ ->
      { param_type = parse_c_type trimmed; param_name = None }

type pending_contract = {
  target_name : string option;
  require : string list;
  guarantee : string list;
  safety : string list;
}

type contract_fragment = {
  target_name : string option;
  contract : contract;
}

type named_contract = {
  line_number : int;
  contract : contract;
}

type function_signature = {
  name : func_name;
  return_type : c_type;
  params : param list;
}

let empty_pending_contract = {
  target_name = None;
  require = [];
  guarantee = [];
  safety = [];
}

let pending_has_clauses contract =
  contract.require <> []
  || contract.guarantee <> []
  || contract.safety <> []

let has_pending_contract (contract : pending_contract) =
  Option.is_some contract.target_name || pending_has_clauses contract

let take_tag_value ~tag line =
  if starts_with ~prefix:tag line then
    let rest =
      String.sub line (String.length tag) (String.length line - String.length tag)
      |> String.trim
    in
    let rest =
      if starts_with ~prefix:":" rest then
        String.sub rest 1 (String.length rest - 1) |> String.trim
      else rest
    in
    Some rest
  else None

let set_contract_target line_number header_path (contract : pending_contract) value =
  if value = "" then
    fail "empty @Contract in %s at line %d" header_path line_number;
  if not (is_qualified_ident value) then
    fail "unsupported @Contract target `%s` in %s at line %d" value header_path line_number;
  match contract.target_name with
  | Some _ ->
      fail "duplicate @Contract in %s at line %d" header_path line_number
  | None ->
      { contract with target_name = Some value }

let append_contract_field line_number header_path (contract : pending_contract) tag value =
  if value = "" then
    fail "empty %s in %s at line %d" tag header_path line_number;
  match tag with
  | "@Require" ->
      { contract with require = contract.require @ [ value ] }
  | "@Guarantee" ->
      { contract with guarantee = contract.guarantee @ [ value ] }
  | "@Safety" ->
      { contract with safety = contract.safety @ [ value ] }
  | _ -> contract

let consume_comment_line (contract : pending_contract) ~header_path ~line_number raw_line =
  let trimmed = String.trim raw_line in
  let trimmed =
    if starts_with ~prefix:"*" trimmed then
      String.sub trimmed 1 (String.length trimmed - 1) |> String.trim
    else trimmed
  in
  match take_tag_value ~tag:"@Contract" trimmed with
  | Some value ->
      set_contract_target line_number header_path contract value
  | None ->
      (match take_tag_value ~tag:"@Require" trimmed with
      | Some value ->
          append_contract_field line_number header_path contract "@Require" value
      | None ->
          (match take_tag_value ~tag:"@Guarantee" trimmed with
          | Some value ->
              append_contract_field line_number header_path contract "@Guarantee" value
          | None ->
              (match take_tag_value ~tag:"@Safety" trimmed with
              | Some value ->
                  append_contract_field line_number header_path contract "@Safety" value
              | None -> contract)))

let consume_comment_text (contract : pending_contract) ~header_path ~line_number text =
  String.split_on_char '\n' text
  |> List.fold_left
       (fun current line ->
         consume_comment_line current ~header_path ~line_number line)
       contract

let materialize_contract_block ~header_path ~line_number (pending : pending_contract) =
  if Option.is_some pending.target_name && not (pending_has_clauses pending) then
    let name = Option.value pending.target_name ~default:"<unknown>" in
    fail "empty contract block for function `%s` in %s at line %d" name header_path line_number
  else if not (pending_has_clauses pending) then
    None
  else
    Some
      {
        target_name = pending.target_name;
        contract =
          {
            require = pending.require;
            guarantee = pending.guarantee;
            safety = pending.safety;
          };
      }

let parse_params text =
  let trimmed = String.trim text in
  if trimmed = "" || trimmed = "void" then []
  else String.split_on_char ',' trimmed |> List.map parse_param

let parse_prototype_signature ~header_path ~line_number decl =
  let trimmed = String.trim decl in
  if not (ends_with ~suffix:";" trimmed) then
    fail "unterminated function declaration in %s at line %d" header_path line_number;
  let without_semi =
    String.sub trimmed 0 (String.length trimmed - 1) |> String.trim
  in
  let open_paren =
    match find_substring ~sub:"(" without_semi with
    | Some idx -> idx
    | None ->
        fail "expected function declaration in %s at line %d" header_path line_number
  in
  let close_paren =
    match find_substring ~sub:")" without_semi with
    | Some idx -> idx
    | None ->
        fail "expected closing `)` in %s at line %d" header_path line_number
  in
  let prefix = String.sub without_semi 0 open_paren |> String.trim in
  let suffix =
    String.sub without_semi (close_paren + 1)
      (String.length without_semi - close_paren - 1)
    |> String.trim
  in
  if suffix <> "" then
    fail "unsupported trailing tokens in %s at line %d" header_path line_number;
  let params_text =
    String.sub without_semi (open_paren + 1) (close_paren - open_paren - 1)
  in
  let return_type, name =
    match split_last_identifier prefix with
    | Some (type_part, name) when type_part <> "" -> parse_c_type type_part, name
    | _ ->
        fail "unsupported function declaration in %s at line %d" header_path line_number
  in
  if is_reference_type return_type then
    fail
      "reference return types are unsupported in %s at line %d"
      header_path
      line_number;
  { name; return_type; params = parse_params params_text }

let apply_contract (signature : function_signature) (contract : contract) =
  {
    name = signature.name;
    return_type = signature.return_type;
    params = signature.params;
    contract;
  }

let add_signature signatures signature =
  if List.exists (( = ) signature) signatures then signatures else signature :: signatures

let assoc_signature_opt signature bindings =
  List.find_map
    (fun (candidate, contract) ->
      if candidate = signature then Some contract else None)
    bindings

let add_signature_contract signature contract bindings =
  let rec loop acc = function
    | [] -> List.rev ((signature, contract) :: acc)
    | ((candidate, existing) as binding) :: rest ->
        if candidate = signature then
          List.rev_append acc ((signature, merge_contracts existing contract) :: rest)
        else
          loop (binding :: acc) rest
  in
  loop [] bindings

let assoc_named_contract name bindings =
  List.find_map
    (fun (candidate, entry) ->
      if String.equal candidate name then Some entry else None)
    bindings

let add_named_contract line_number name contract bindings =
  let rec loop acc = function
    | [] -> List.rev ((name, { line_number; contract }) :: acc)
    | ((candidate, entry) as binding) :: rest ->
        if String.equal candidate name then
          List.rev_append acc ((name, { entry with contract = merge_contracts entry.contract contract }) :: rest)
        else
          loop (binding :: acc) rest
  in
  loop [] bindings

let finalize_contracts ~source_path signatures_rev legacy_contracts named_contracts =
  let signatures = List.rev signatures_rev in
  List.iter
    (fun (name, entry) ->
      let matches =
        List.filter (fun (signature : function_signature) -> String.equal signature.name name) signatures
      in
      match matches with
      | [] ->
          fail
            "contract for unknown function `%s` in %s at line %d"
            name
            source_path
            entry.line_number
      | [ _ ] ->
          ()
      | _ ->
          fail
            "named contract for overloaded function `%s` in %s at line %d is ambiguous"
            name
            source_path
            entry.line_number)
    named_contracts;
  signatures
  |> List.filter_map (fun signature ->
         let legacy =
           Option.value (assoc_signature_opt signature legacy_contracts) ~default:empty_contract
         in
         let named =
           match assoc_named_contract signature.name named_contracts with
           | Some entry -> entry.contract
           | None -> empty_contract
         in
         let contract = merge_contracts legacy named in
         if contract_is_empty contract then None else Some (apply_contract signature contract))

let is_local_include_line line =
  let trimmed = String.trim line in
  if trimmed = "" || trimmed.[0] <> '#' then None
  else
    let rest =
      String.sub trimmed 1 (String.length trimmed - 1) |> String.trim
    in
    if not (starts_with ~prefix:"include" rest) then None
    else
      let after_include =
        String.sub rest 7 (String.length rest - 7) |> String.trim
      in
      if not (starts_with ~prefix:"\"" after_include) then None
      else
        match find_substring ~sub:"\"" (String.sub after_include 1 (String.length after_include - 1)) with
        | Some idx ->
            Some (String.sub after_include 1 idx)
        | None -> fail "malformed local include line `%s`" line

let resolve_include ~base_dir include_path =
  if Filename.is_relative include_path then Filename.concat base_dir include_path
  else include_path

let parse_header_file ~base_dir include_path =
  let header_path = resolve_include ~base_dir include_path in
  let source =
    try read_file header_path with
    | Sys_error msg -> fail "failed to read header %s: %s" include_path msg
  in
  let lines = String.split_on_char '\n' source in
  let signatures_rev = ref [] in
  let legacy_contracts = ref [] in
  let named_contracts = ref [] in
  let pending_legacy = ref empty_contract in
  let in_block_comment = ref false in
  let block_start_line = ref 1 in
  let block_buffer = Buffer.create 128 in
  let decl_buffer = Buffer.create 128 in
  let decl_start_line = ref None in
  let ingest_comment_fragment ~line_number text =
    let fragment =
      consume_comment_text empty_pending_contract ~header_path:include_path ~line_number text
    in
    match materialize_contract_block ~header_path:include_path ~line_number fragment with
    | None -> ()
    | Some { target_name = Some name; contract } ->
        named_contracts :=
          add_named_contract line_number name contract !named_contracts
    | Some { target_name = None; contract } ->
        pending_legacy := merge_contracts !pending_legacy contract
  in
  let clear_decl () =
    Buffer.clear decl_buffer;
    decl_start_line := None
  in
  let append_decl line_number line =
    let trimmed = String.trim line in
    if trimmed <> "" then begin
      if Buffer.length decl_buffer = 0 then decl_start_line := Some line_number
      else Buffer.add_char decl_buffer ' ';
      Buffer.add_string decl_buffer trimmed
    end
  in
  let maybe_finish_decl () =
    let decl = Buffer.contents decl_buffer in
    if decl <> "" && ends_with ~suffix:";" decl then begin
      let line_number = Option.value !decl_start_line ~default:1 in
      let signature =
        parse_prototype_signature ~header_path:include_path ~line_number decl
      in
      signatures_rev := add_signature !signatures_rev signature;
      if not (contract_is_empty !pending_legacy) then
        legacy_contracts :=
          add_signature_contract signature !pending_legacy !legacy_contracts;
      pending_legacy := empty_contract;
      clear_decl ()
    end
  in
  List.iteri
    (fun idx raw_line ->
      let line_number = idx + 1 in
      let trimmed = String.trim raw_line in
      if !in_block_comment then
        match find_substring ~sub:"*/" raw_line with
        | Some end_idx ->
            Buffer.add_string block_buffer (String.sub raw_line 0 end_idx);
            ingest_comment_fragment
              ~line_number:!block_start_line
              (Buffer.contents block_buffer);
            Buffer.clear block_buffer;
            in_block_comment := false;
            let rest =
              String.sub raw_line (end_idx + 2)
                (String.length raw_line - end_idx - 2)
              |> String.trim
            in
            if rest <> "" then begin
              append_decl line_number rest;
              maybe_finish_decl ()
            end
        | None ->
            Buffer.add_string block_buffer raw_line;
            Buffer.add_char block_buffer '\n'
      else if trimmed = "" then ()
      else
        match is_local_include_line trimmed with
        | Some _ -> ()
        | None ->
            if trimmed.[0] = '#' then ()
            else if starts_with ~prefix:"//" trimmed then
              ingest_comment_fragment
                ~line_number
                (String.sub trimmed 2 (String.length trimmed - 2))
            else if starts_with ~prefix:"/*" trimmed then
              (match find_substring ~sub:"*/" trimmed with
              | Some end_idx when end_idx >= 2 ->
                  let body = String.sub trimmed 2 (end_idx - 2) in
                  ingest_comment_fragment ~line_number body;
                  let rest =
                    String.sub trimmed (end_idx + 2)
                      (String.length trimmed - end_idx - 2)
                    |> String.trim
                  in
                  if rest <> "" then begin
                    append_decl line_number rest;
                    maybe_finish_decl ()
                  end
              | _ ->
                  in_block_comment := true;
                  block_start_line := line_number;
                  Buffer.clear block_buffer;
                  Buffer.add_string block_buffer
                    (String.sub trimmed 2 (String.length trimmed - 2));
                  Buffer.add_char block_buffer '\n')
            else if Buffer.length decl_buffer > 0 || find_substring ~sub:"(" trimmed <> None then begin
              append_decl line_number trimmed;
              maybe_finish_decl ()
            end else if not (contract_is_empty !pending_legacy) then
              pending_legacy := empty_contract)
    lines;
  if !in_block_comment then
    fail "unterminated block comment in %s" include_path;
  if Buffer.length decl_buffer > 0 then
    fail "unterminated function declaration in %s" include_path;
  {
    include_path;
    functions =
      finalize_contracts
        ~source_path:include_path
        !signatures_rev
        !legacy_contracts
        !named_contracts;
  }

let load_imports ~base_dir source =
  String.split_on_char '\n' source
  |> List.filter_map is_local_include_line
  |> List.map (parse_header_file ~base_dir)

let parse_definition_signature ~source_path ~line_number decl =
  let trimmed = String.trim decl in
  if not (ends_with ~suffix:"{" trimmed) then
    fail "unterminated function definition in %s at line %d" source_path line_number;
  let prototype =
    String.sub trimmed 0 (String.length trimmed - 1)
    |> String.trim
    |> fun text -> text ^ ";"
  in
  parse_prototype_signature ~header_path:source_path ~line_number prototype

type definition_scan_mode =
  | Code
  | Preprocessor
  | Line_comment of {
      capture : bool;
      start_line : int;
      buffer : Buffer.t;
    }
  | Block_comment of {
      capture : bool;
      start_line : int;
      buffer : Buffer.t;
    }

let load_defined_contracts ~source_path source =
  let signatures_rev = ref [] in
  let legacy_contracts = ref [] in
  let named_contracts = ref [] in
  let pending_legacy = ref empty_contract in
  let brace_depth = ref 0 in
  let line_number = ref 1 in
  let top_buffer = Buffer.create 128 in
  let top_start_line = ref None in
  let ingest_comment_fragment ~line_number text =
    let fragment =
      consume_comment_text empty_pending_contract ~header_path:source_path ~line_number text
    in
    match materialize_contract_block ~header_path:source_path ~line_number fragment with
    | None -> ()
    | Some { target_name = Some name; contract } ->
        named_contracts :=
          add_named_contract line_number name contract !named_contracts
    | Some { target_name = None; contract } ->
        pending_legacy := merge_contracts !pending_legacy contract
  in
  let add_top_char c =
    let is_space =
      match c with
      | ' ' | '\t' | '\r' | '\n' -> true
      | _ -> false
    in
    if !top_start_line = None && is_space then ()
    else begin
      if !top_start_line = None then top_start_line := Some !line_number;
      Buffer.add_char top_buffer (if c = '\n' then ' ' else c)
    end
  in
  let clear_top () =
    Buffer.clear top_buffer;
    top_start_line := None
  in
  let finalize_top terminator =
    add_top_char terminator;
    let decl = Buffer.contents top_buffer |> String.trim in
    let decl_line = Option.value !top_start_line ~default:!line_number in
    if decl <> "" then
      if terminator = '{' && find_substring ~sub:"(" decl <> None then begin
        let signature =
          parse_definition_signature ~source_path ~line_number:decl_line decl
        in
        signatures_rev := add_signature !signatures_rev signature;
        if not (contract_is_empty !pending_legacy) then
          legacy_contracts :=
            add_signature_contract signature !pending_legacy !legacy_contracts;
        pending_legacy := empty_contract
      end else if not (contract_is_empty !pending_legacy) then
        pending_legacy := empty_contract;
    clear_top ()
  in
  let finish_comment capture start_line buffer =
    if capture then
      ingest_comment_fragment ~line_number:start_line (Buffer.contents buffer)
  in
  let length = String.length source in
  let rec loop i mode =
    if i >= length then begin
      (match mode with
      | Code | Preprocessor -> ()
      | Line_comment { capture; start_line; buffer } ->
          finish_comment capture start_line buffer
      | Block_comment _ ->
          fail "unterminated block comment in %s" source_path);
      finalize_contracts
        ~source_path
        !signatures_rev
        !legacy_contracts
        !named_contracts
    end else
      match mode with
      | Code ->
          let c = source.[i] in
          if c = '\n' then begin
            if !brace_depth = 0 then add_top_char c;
            incr line_number;
            loop (i + 1) Code
          end else if c = '/' && i + 1 < length && source.[i + 1] = '/' then
            let capture = !brace_depth = 0 && Buffer.length top_buffer = 0 in
            let buffer = Buffer.create 32 in
            loop (i + 2) (Line_comment { capture; start_line = !line_number; buffer })
          else if c = '/' && i + 1 < length && source.[i + 1] = '*' then
            let capture = !brace_depth = 0 && Buffer.length top_buffer = 0 in
            let buffer = Buffer.create 64 in
            loop (i + 2) (Block_comment { capture; start_line = !line_number; buffer })
          else if !brace_depth = 0 && c = '#' && Buffer.length top_buffer = 0 then begin
            if not (contract_is_empty !pending_legacy) then
              pending_legacy := empty_contract;
            loop (i + 1) Preprocessor
          end else begin
            if !brace_depth = 0 then begin
              if c = '{' then begin
                finalize_top c;
                brace_depth := 1
              end else if c = ';' then
                finalize_top c
              else
                add_top_char c
            end else if c = '{' then
              incr brace_depth
            else if c = '}' then
              decr brace_depth;
            loop (i + 1) Code
          end
      | Preprocessor ->
          if source.[i] = '\n' then begin
            incr line_number;
            loop (i + 1) Code
          end else
            loop (i + 1) Preprocessor
      | Line_comment { capture; start_line; buffer } ->
          if source.[i] = '\n' then begin
            finish_comment capture start_line buffer;
            incr line_number;
            loop (i + 1) Code
          end else begin
            if capture then Buffer.add_char buffer source.[i];
            loop (i + 1) (Line_comment { capture; start_line; buffer })
          end
      | Block_comment { capture; start_line; buffer } ->
          if source.[i] = '*' && i + 1 < length && source.[i + 1] = '/' then begin
            finish_comment capture start_line buffer;
            loop (i + 2) Code
          end else begin
            if source.[i] = '\n' then incr line_number;
            if capture then Buffer.add_char buffer source.[i];
            loop (i + 1) (Block_comment { capture; start_line; buffer })
          end
  in
  loop 0 Code
