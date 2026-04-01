type raw_invariant = {
  line_number : int;
  text : string;
}

exception Error of string

let fail fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

let starts_with ~prefix s =
  let prefix_len = String.length prefix in
  let s_len = String.length s in
  prefix_len <= s_len && String.sub s 0 prefix_len = prefix

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

let consume_comment_line invariant ~source_path ~line_number raw_line =
  let trimmed = String.trim raw_line in
  let trimmed =
    if starts_with ~prefix:"*" trimmed then
      String.sub trimmed 1 (String.length trimmed - 1) |> String.trim
    else
      trimmed
  in
  match take_tag_value ~tag:"@Invariant" trimmed with
  | None -> invariant
  | Some value ->
      if value = "" then
        fail "empty @Invariant in %s at line %d" source_path line_number;
      (match invariant with
      | None -> Some { line_number; text = value }
      | Some _ ->
          fail "duplicate @Invariant in %s at line %d" source_path line_number)

let consume_comment_text invariant ~source_path ~line_number text =
  String.split_on_char '\n' text
  |> List.fold_left
       (fun current line ->
         consume_comment_line current ~source_path ~line_number line)
       invariant

type mode =
  | Code
  | Preprocessor
  | Line_comment of {
      start_line : int;
      buffer : Buffer.t;
    }
  | Block_comment of {
      start_line : int;
      buffer : Buffer.t;
    }

let load ~source_path source =
  let pending = ref None in
  let invariants_rev = ref [] in
  let line_number = ref 1 in
  let at_line_start = ref true in
  let only_spaces_on_line = ref true in
  let length = String.length source in
  let push_while () =
    invariants_rev := !pending :: !invariants_rev;
    pending := None
  in
  let ensure_not_pending identifier =
    match !pending with
    | None -> ()
    | Some invariant ->
        fail
          "@Invariant at line %d in %s is not attached to a while; saw `%s` instead"
          invariant.line_number
          source_path
          identifier
  in
  let finish_comment start_line buffer =
    pending :=
      consume_comment_text !pending ~source_path ~line_number:start_line
        (Buffer.contents buffer)
  in
  let rec parse_identifier j =
    if j < length then
      match source.[j] with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> parse_identifier (j + 1)
      | _ -> j
    else
      j
  in
  let rec loop i mode =
    if i >= length then begin
      (match mode with
      | Code | Preprocessor -> ()
      | Line_comment { start_line; buffer } ->
          finish_comment start_line buffer
      | Block_comment _ ->
          fail "unterminated block comment in %s" source_path);
      (match !pending with
      | None -> List.rev !invariants_rev
      | Some invariant ->
          fail
            "@Invariant at line %d in %s is not attached to a while"
            invariant.line_number
            source_path)
    end else
      match mode with
      | Code ->
          let c = source.[i] in
          (match c with
          | ' ' | '\t' | '\r' ->
              loop (i + 1) Code
          | '\n' ->
              incr line_number;
              at_line_start := true;
              only_spaces_on_line := true;
              loop (i + 1) Code
          | '#' when !at_line_start || !only_spaces_on_line ->
              ensure_not_pending "#";
              at_line_start := false;
              only_spaces_on_line := false;
              loop (i + 1) Preprocessor
          | '/' when i + 1 < length && source.[i + 1] = '/' ->
              at_line_start := false;
              only_spaces_on_line := false;
              loop (i + 2) (Line_comment { start_line = !line_number; buffer = Buffer.create 32 })
          | '/' when i + 1 < length && source.[i + 1] = '*' ->
              at_line_start := false;
              only_spaces_on_line := false;
              loop (i + 2) (Block_comment { start_line = !line_number; buffer = Buffer.create 64 })
          | 'a' .. 'z' | 'A' .. 'Z' | '_' ->
              let j = parse_identifier (i + 1) in
              let ident = String.sub source i (j - i) in
              if String.equal ident "while" then
                push_while ()
              else
                ensure_not_pending ident;
              at_line_start := false;
              only_spaces_on_line := false;
              loop j Code
          | _ ->
              ensure_not_pending (String.make 1 c);
              at_line_start := false;
              only_spaces_on_line := false;
              loop (i + 1) Code)
      | Preprocessor ->
          if source.[i] = '\n' then begin
            incr line_number;
            at_line_start := true;
            only_spaces_on_line := true;
            loop (i + 1) Code
          end else
            loop (i + 1) Preprocessor
      | Line_comment { start_line; buffer } ->
          if source.[i] = '\n' then begin
            finish_comment start_line buffer;
            incr line_number;
            at_line_start := true;
            only_spaces_on_line := true;
            loop (i + 1) Code
          end else begin
            Buffer.add_char buffer source.[i];
            loop (i + 1) (Line_comment { start_line; buffer })
          end
      | Block_comment { start_line; buffer } ->
          if source.[i] = '*' && i + 1 < length && source.[i + 1] = '/' then begin
            finish_comment start_line buffer;
            loop (i + 2) Code
          end else begin
            if source.[i] = '\n' then incr line_number;
            Buffer.add_char buffer source.[i];
            loop (i + 1) (Block_comment { start_line; buffer })
          end
  in
  loop 0 Code
