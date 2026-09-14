let starts_with ~prefix text =
  let prefix_len = String.length prefix in
  String.length text >= prefix_len
  && String.sub text 0 prefix_len = prefix

let is_ident_start = function
  | 'A' .. 'Z' | 'a' .. 'z' | '_' -> true
  | _ -> false

let is_ident_char = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true
  | _ -> false

let assoc_opt key bindings =
  List.find_map
    (fun (name, value) ->
      if String.equal name key then Some value else None)
    bindings

let substitute_identifiers defines line =
  let len = String.length line in
  let buffer = Buffer.create len in
  let rec loop i =
    if i >= len then
      Buffer.contents buffer
    else if is_ident_start line.[i] then
      let j = ref (i + 1) in
      while !j < len && is_ident_char line.[!j] do
        incr j
      done;
      let ident = String.sub line i (!j - i) in
      Buffer.add_string
        buffer
        (Option.value (assoc_opt ident defines) ~default:ident);
      loop !j
    else (
      Buffer.add_char buffer line.[i];
      loop (i + 1))
  in
  loop 0

let parse_define_line line =
  let trimmed = String.trim line in
  if not (starts_with ~prefix:"#define" trimmed) then
    None
  else
    let rest =
      String.sub trimmed 7 (String.length trimmed - 7)
      |> String.trim
    in
    if rest = "" then
      None
    else
      let split_at =
        let rec loop i =
          if i >= String.length rest then None
          else
            match rest.[i] with
            | ' ' | '\t' -> Some i
            | '(' -> None
            | _ -> loop (i + 1)
        in
        loop 0
      in
      match split_at with
      | None -> None
      | Some index ->
          let name = String.sub rest 0 index in
          let value =
            String.sub rest index (String.length rest - index)
            |> String.trim
          in
          if name = "" || value = "" then None else Some (name, value)

let preprocess source =
  let lines = String.split_on_char '\n' source in
  let rec loop defines_rev processed_rev = function
    | [] ->
        String.concat "\n" (List.rev processed_rev)
    | line :: rest ->
        let trimmed = String.trim line in
        if starts_with ~prefix:"#include" trimmed then
          loop defines_rev (line :: processed_rev) rest
        else
          (match parse_define_line line with
          | Some (name, value) ->
              let defines = List.rev defines_rev in
              let value = substitute_identifiers defines value in
              loop ((name, value) :: defines_rev) ("" :: processed_rev) rest
          | None ->
              let defines = List.rev defines_rev in
              let line =
                if starts_with ~prefix:"#define" trimmed then line
                else substitute_identifiers defines line
              in
              loop defines_rev (line :: processed_rev) rest)
  in
  loop [] [] lines
