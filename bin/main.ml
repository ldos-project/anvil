open Anvil

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

let read_input = function
  | None -> read_all stdin
  | Some path ->
      let in_channel = open_in_bin path in
      Fun.protect
        ~finally:(fun () -> close_in_noerr in_channel)
        (fun () -> read_all in_channel)

let usage () =
  prerr_endline "Usage: anvil [--verify] [FILE]";
  prerr_endline "Default mode pretty-prints the instrumented C program.";
  prerr_endline "With --verify, checks the program with Z3.";
  prerr_endline "Reads from FILE if provided, otherwise from stdin.";
  exit 2

let () =
  let verify_mode, input_path =
    match Array.to_list Sys.argv with
    | [_] -> false, None
    | [_; "--verify"] -> true, None
    | [_; path] -> false, Some path
    | [_; "--verify"; path] -> true, Some path
    | _ -> usage ()
  in
  try
    let source = read_input input_path in
    let base_dir =
      match input_path with
      | None -> Sys.getcwd ()
      | Some path -> Filename.dirname path
    in
    let source_name = Option.value input_path ~default:"<stdin>" in
    match Ast_parser.parse_program ~base_dir ~source_name source with
    | Ok program ->
        if verify_mode then
          (match Verify.verify_program program with
          | Ok Verify.Verified ->
              print_endline (Verify.format_outcome Verify.Verified)
          | Ok (Verify.Counterexample failure) ->
              prerr_endline (Verify.format_outcome (Verify.Counterexample failure));
              exit 1
          | Ok (Verify.Inconclusive details) ->
              prerr_endline (Verify.format_outcome (Verify.Inconclusive details));
              exit 1
          | Error message ->
              prerr_endline ("Verification error: " ^ message);
              exit 1)
        else
          (match Instrument.instrument_program program with
          | Ok instrumented -> print_string (Ast.program_to_c instrumented)
          | Error message ->
              prerr_endline ("Instrumentation error: " ^ message);
              exit 1)
    | Error message ->
        prerr_endline ("Parse error: " ^ message);
        exit 1
  with
  | Sys_error message ->
      prerr_endline ("I/O error: " ^ message);
      exit 2
