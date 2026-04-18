open Core
open Quickcheck
open Anvil
open Ast
open Ast_parser

module G = Base_quickcheck.Generator

let gen_var = G.of_list ["x"; "y"; "z"; "w"; "t"]

let rec gen_expr size =
  if size <= 0 then
    G.union
      [ G.int_inclusive (-10) 10 |> G.map ~f:(fun i -> Int i)
      ; gen_var |> G.map ~f:(fun v -> Var v)
      ]
  else
    let smaller = gen_expr (size / 2) in
    G.union
      [ G.int_inclusive (-10) 10 |> G.map ~f:(fun i -> Int i)
      ; gen_var |> G.map ~f:(fun v -> Var v)
      ; G.map2 smaller smaller ~f:(fun a b -> Add (a, b))
      ; G.map2 smaller smaller ~f:(fun a b -> Sub (a, b))
      ; G.map2 smaller smaller ~f:(fun a b -> Mul (a, b))
      ; G.map2 smaller smaller ~f:(fun a b -> Div (a, b))
      ; G.map2 smaller smaller ~f:(fun a b -> Mod (a, b))
      ; G.bind (G.int_uniform_inclusive 0 3) ~f:(fun length ->
          G.map (G.list_with_length smaller ~length) ~f:(fun args -> FuncCall ("f", args)))
      ]

let rec gen_bexpr size =
  if size <= 0 then
    G.union
      [ G.return True
      ; G.return False
      ; G.map2 (gen_expr 0) (gen_expr 0) ~f:(fun a b -> Eq (a, b))
      ; G.map2 (gen_expr 0) (gen_expr 0) ~f:(fun a b -> Neq (a, b))
      ]
  else
    let smaller = gen_bexpr (size / 2) in
    G.union
      [ G.map2 (gen_expr (size / 2)) (gen_expr (size / 2)) ~f:(fun a b -> Lt (a, b))
      ; G.map2 (gen_expr (size / 2)) (gen_expr (size / 2)) ~f:(fun a b -> Le (a, b))
      ; G.map2 (gen_expr (size / 2)) (gen_expr (size / 2)) ~f:(fun a b -> Gt (a, b))
      ; G.map2 (gen_expr (size / 2)) (gen_expr (size / 2)) ~f:(fun a b -> Ge (a, b))
      ; G.map smaller ~f:(fun p -> Not p)
      ; G.map2 smaller smaller ~f:(fun a b -> And (a, b))
      ; G.map2 smaller smaller ~f:(fun a b -> Or (a, b))
      ; G.return True
      ; G.return False
      ]

let rec gen_stmt size =
  if size <= 0 then
    G.union
      [ G.return Skip
      ; G.map2 gen_var (gen_expr 0) ~f:(fun v e -> Assign (v, e))
      ]
  else
    let smaller = gen_stmt (size / 2) in
    let smaller_b = gen_bexpr (size / 2) in
    G.union
      [ G.return Skip
      ; G.map2 gen_var (gen_expr (size / 2)) ~f:(fun v e -> Assign (v, e))
      ; G.map2 smaller smaller ~f:(fun a b -> Seq [a; b])
      ; G.map3 smaller_b smaller smaller ~f:(fun c t e -> If (c, t, e))
      ; G.map2 smaller_b smaller ~f:(fun c b -> While (None, c, b))
      ; G.map smaller_b ~f:(fun c -> Assume c)
      ; G.map smaller_b ~f:(fun c -> Assert (Source_assert, c))
      ]

let gen_program size =
  G.bind (G.int_uniform_inclusive 0 3) ~f:(fun length ->
      G.map2
        (G.list_with_length gen_var ~length)
        (gen_stmt size)
        ~f:(fun globals body ->
          {
            imports = [];
            records = [];
            globals =
              List.map globals ~f:(fun global_name ->
                  { global_type = TInt; global_name });
            functions = [];
            main =
              {
                name = "main";
                return_type = TInt;
                params = [];
                locals = [];
                contract = None;
                body = Seq [ body; Return (Some (Int 0)) ];
              };
          }))

let assert_header_import_roundtrip () =
  let header_path = Stdlib.Filename.temp_file "anvil_contracts" ".h" in
  Fun.protect
    ~finally:(fun () ->
      try Stdlib.Sys.remove header_path with
      | _ -> ())
    (fun () ->
      Out_channel.write_all header_path
        ~data:
          "/* @Require x >= 0\n\
           * @Guarantee result >= x\n\
           * @Safety x >= 0\n\
           */\n\
           int inc(int x);\n";
      let base_dir = Stdlib.Filename.dirname header_path in
      let include_name = Stdlib.Filename.basename header_path in
      let source =
        "#include \"" ^ include_name ^ "\"\n"
        ^ "#include <stdlib.h>\n"
        ^ "#include <stdio.h>\n\n"
        ^ "int x;\n\n"
        ^ "int main(void) {\n"
        ^ "  x = inc(1);\n"
        ^ "  return 0;\n"
        ^ "}\n"
      in
      match parse_program ~base_dir source with
      | Error e -> failwith ("Header import parse failed: " ^ e)
      | Ok p ->
          if List.length p.imports <> 1 then
            failwith "Expected exactly one imported header";
          match parse_program ~base_dir (program_to_c p) with
          | Error e -> failwith ("Header roundtrip parse failed: " ^ e)
          | Ok p2 ->
              if not (equal_program p p2) then
                failwith "Header import roundtrip mismatch")

let assert_contract_instrumentation () =
  let header_path = Stdlib.Filename.temp_file "anvil_instrument" ".h" in
  Fun.protect
    ~finally:(fun () ->
      try Stdlib.Sys.remove header_path with
      | _ -> ())
    (fun () ->
      Out_channel.write_all header_path
        ~data:
          "/* @Require x >= 0\n\
           * @Guarantee result >= x\n\
           * @Safety x <= 10\n\
           */\n\
           int inc(int x);\n";
      let base_dir = Stdlib.Filename.dirname header_path in
      let include_name = Stdlib.Filename.basename header_path in
      let source =
        "#include \"" ^ include_name ^ "\"\n"
        ^ "#include <stdlib.h>\n"
        ^ "#include <stdio.h>\n\n"
        ^ "int x;\n\n"
        ^ "int main(void) {\n"
        ^ "  x = inc(1);\n"
        ^ "  return 0;\n"
        ^ "}\n"
      in
      match parse_program ~base_dir source with
      | Error e -> failwith ("Instrumentation parse failed: " ^ e)
      | Ok program ->
          (match Instrument.instrument_program program with
          | Error e -> failwith ("Instrumentation failed: " ^ e)
          | Ok instrumented ->
              if
                not
                  (List.exists instrumented.globals ~f:(fun global ->
                       String.is_prefix global.global_name
                         ~prefix:"__anvil_contract_result_"))
              then
                failwith "Expected an instrumentation temp global";
              (match instrumented.main.body with
              | Seq [ Assert (_, Ge (Int 1, Int 0))
                    ; Assign (tmp, FuncCall ("inc", [ Int 1 ]))
                    ; Assume (Ge (Var result_var, Int 1))
                    ; Assume (Le (Int 1, Int 10))
                    ; Assign ("x", Var assigned_var)
                    ; Return (Some (Int 0))
                    ] ->
                  if not (String.equal tmp result_var && String.equal tmp assigned_var) then
                    failwith "Expected the temp result variable to thread through instrumentation"
              | _ ->
                  failwith
                    ("Unexpected instrumented body:\n" ^ program_to_c instrumented))))

let assert_local_contract_roundtrip_and_instrumentation () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "/* @Require y >= 0\n"
    ^ " * @Guarantee result > y\n"
    ^ " * @Safety y >= 0\n"
    ^ " */\n"
    ^ "int inc(int y) {\n"
    ^ "  return (y + 1);\n"
    ^ "}\n\n"
    ^ "int main(void) {\n"
    ^ "  x = inc(1);\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Local contract parse failed: " ^ e)
  | Ok program ->
      (match program.functions with
      | [ { contract = Some _; _ } ] -> ()
      | _ -> failwith "Expected a contracted local helper function");
      (match parse_program (program_to_c program) with
      | Error e -> failwith ("Local contract roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Local contract roundtrip mismatch");
      (match Instrument.instrument_program program with
      | Error e -> failwith ("Local contract instrumentation failed: " ^ e)
      | Ok instrumented ->
          (match instrumented.functions with
          | [ { body =
                  Seq [ Assume (Ge (Var "y", Int 0))
                      ; Assert (_, Ge (Var "y", Int 0))
                      ; Assert (_, Gt (Add (Var "y", Int 1), Var "y"))
                      ; Return (Some (Add (Var "y", Int 1)))
                      ]
              ; _ } ] ->
              ()
          | _ ->
              failwith
                ("Unexpected instrumented helper body:\n" ^ program_to_c instrumented));
          match instrumented.main.body with
          | Seq [ Assert (_, Ge (Int 1, Int 0))
                ; Assign (tmp, FuncCall ("inc", [ Int 1 ]))
                ; Assume (Gt (Var result_var, Int 1))
                ; Assume (Ge (Int 1, Int 0))
                ; Assign ("x", Var assigned_var)
                ; Return (Some (Int 0))
                ] ->
              if not (String.equal tmp result_var && String.equal tmp assigned_var) then
                failwith "Expected local contract temp threading through main"
          | _ ->
              failwith
                ("Unexpected instrumented main body:\n" ^ program_to_c instrumented));
      (match Verify.verify_program program with
      | Error e -> failwith ("Verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected local contract example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_verifier_reports_counterexample () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "int main(void) {\n"
    ^ "  if (!(x >= 0)) { abort(); }\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Counterexample parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Counterexample verification failed: " ^ e)
      | Ok (Verify.Counterexample { condition_name; bindings; _ }) ->
          if not (String.equal condition_name "main: entry") then
            failwith "Expected main entry counterexample";
          if not (List.exists bindings ~f:(fun (name, value) -> String.equal name "x" && String.equal value "-1")) then
            failwith "Expected counterexample assignment x = -1"
      | Ok outcome ->
          failwith
            ("Expected a counterexample, got:\n" ^ Verify.format_outcome outcome))

let assert_counterexample_reports_require_location () =
  let header_path = Stdlib.Filename.temp_file "anvil_require_report" ".h" in
  Fun.protect
    ~finally:(fun () ->
      try Stdlib.Sys.remove header_path with
      | _ -> ())
    (fun () ->
      Out_channel.write_all header_path
        ~data:
          "/* @Require x >= 0\n\
           * @Guarantee result >= x\n\
           * @Safety 1\n\
           */\n\
           int inc(int x);\n";
      let base_dir = Stdlib.Filename.dirname header_path in
      let include_name = Stdlib.Filename.basename header_path in
      let source =
        "#include \"" ^ include_name ^ "\"\n"
        ^ "#include <stdlib.h>\n"
        ^ "#include <stdio.h>\n\n"
        ^ "int x;\n\n"
        ^ "int main(void) {\n"
        ^ "  x = inc(-1);\n"
        ^ "  return 0;\n"
        ^ "}\n"
      in
      match parse_program ~base_dir source with
      | Error e -> failwith ("Require-report parse failed: " ^ e)
      | Ok program ->
          (match Verify.verify_program program with
          | Error e -> failwith ("Require-report verification failed: " ^ e)
          | Ok (Verify.Counterexample { location; program_bindings; _ }) ->
              if not (Option.value_map location ~default:false ~f:(String.equal "`inc`'s @Require was violated")) then
                failwith "Expected @Require violation location";
              if not (List.exists program_bindings ~f:(fun (name, value) -> String.equal name "x" && String.equal value "0")) then
                failwith "Expected program variable snapshot for x"
          | Ok outcome ->
              failwith
                ("Expected @Require counterexample, got:\n"
                ^ Verify.format_outcome outcome)))

let assert_counterexample_reports_guarantee_location () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "/* @Require y >= 0\n"
    ^ " * @Guarantee result > y\n"
    ^ " * @Safety y >= 0\n"
    ^ " */\n"
    ^ "int bad(int y) {\n"
    ^ "  return y;\n"
    ^ "}\n\n"
    ^ "int main(void) {\n"
    ^ "  x = bad(1);\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Guarantee-report parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Guarantee-report verification failed: " ^ e)
      | Ok (Verify.Counterexample { location; program_bindings; _ }) ->
          if not (Option.value_map location ~default:false ~f:(String.equal "`bad` could not prove its @Guarantee")) then
            failwith "Expected @Guarantee violation location";
          if not (List.exists program_bindings ~f:(fun (name, value) -> String.equal name "y" && String.equal value "0")) then
            failwith "Expected program variable snapshot for y"
      | Ok outcome ->
          failwith
            ("Expected @Guarantee counterexample, got:\n"
            ^ Verify.format_outcome outcome))

let assert_verifier_accepts_loop_post_invariant () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "int main(void) {\n"
    ^ "  if (!(x >= 0)) { return 0; }\n"
    ^ "  while ((x > 0)) {\n"
    ^ "    x = (x - 1);\n"
    ^ "  }\n"
    ^ "  if (!(x >= 0)) { abort(); }\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Loop verification parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Loop verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected loop example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_generated_c_compiles source =
  if Stdlib.Sys.command "command -v gcc >/dev/null 2>&1" <> 0 then ()
  else
    let c_path = Stdlib.Filename.temp_file "anvil-generated" ".c" in
    let o_path = Stdlib.Filename.temp_file "anvil-generated" ".o" in
    let stderr_path = Stdlib.Filename.temp_file "anvil-generated" ".stderr" in
    Fun.protect
      ~finally:(fun () ->
        List.iter [ c_path; o_path; stderr_path ] ~f:(fun path ->
          try Stdlib.Sys.remove path with
          | _ -> ()))
      (fun () ->
        Out_channel.write_all c_path ~data:source;
        let command =
          Printf.sprintf
            "gcc -std=c11 -Wall -Wextra -Werror -c %s -o %s 2>%s"
            (Stdlib.Filename.quote c_path)
            (Stdlib.Filename.quote o_path)
            (Stdlib.Filename.quote stderr_path)
        in
        if Stdlib.Sys.command command <> 0 then
          failwith
            ("Generated C did not compile:\n"
            ^ In_channel.read_all stderr_path
            ^ "\nGenerated source:\n"
            ^ source))

let assert_loop_invariant_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "int main(void) {\n"
    ^ "  if (!(x >= 0)) { return 0; }\n"
    ^ "  /* @Invariant x >= 0 */\n"
    ^ "  while ((x > 0)) {\n"
    ^ "    x = (x - 1);\n"
    ^ "  }\n"
    ^ "  if (!(x == 0)) { abort(); }\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Loop invariant parse failed: " ^ e)
  | Ok program ->
      (match program.main.body with
      | Seq [ Assume _
            ; While (Some (Ge (Var "x", Int 0)), Gt (Var "x", Int 0), _)
            ; Assert (_, Eq (Var "x", Int 0))
            ; Return (Some (Int 0))
            ] ->
          ()
      | _ ->
          failwith
            ("Expected parsed loop invariant in main:\n" ^ program_to_c program));
      (match parse_program (program_to_c program) with
      | Error e -> failwith ("Loop invariant roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Loop invariant roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Loop invariant verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected annotated loop example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_memory_safe_program_verifies () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int *p;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  p = malloc(16);\n"
    ^ "  *(p + 1) = 7;\n"
    ^ "  free(p);\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Memory-safe parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Memory-safe verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected safe memory example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_memory_unsafe_program_reports_counterexample () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int *p;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  p = malloc(4);\n"
    ^ "  free(p);\n"
    ^ "  *p = 1;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Memory-unsafe parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Memory-unsafe verification failed: " ^ e)
      | Ok (Verify.Counterexample _) -> ()
      | Ok outcome ->
          failwith
            ("Expected unsafe memory example to fail verification, got:\n"
            ^ Verify.format_outcome outcome))

let assert_memory_too_small_allocation_reports_counterexample () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int *p;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  p = malloc(1);\n"
    ^ "  *p = 1;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Too-small allocation parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Too-small allocation verification failed: " ^ e)
      | Ok (Verify.Counterexample _) -> ()
      | Ok outcome ->
          failwith
            ("Expected too-small allocation example to fail verification, got:\n"
            ^ Verify.format_outcome outcome))

let assert_local_scope_shadowing_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n\n"
    ^ "int x;\n\n"
    ^ "int main(void) {\n"
    ^ "  int y;\n"
    ^ "  y = 1;\n"
    ^ "  {\n"
    ^ "    int y;\n"
    ^ "    y = 2;\n"
    ^ "    x = y;\n"
    ^ "    if (!(x == 2)) { abort(); }\n"
    ^ "  }\n"
    ^ "  x = y;\n"
    ^ "  if (!(x == 1)) { abort(); }\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Local scope parse failed: " ^ e)
  | Ok program ->
      if List.length program.main.locals <> 2 then
        failwith "Expected two resolved locals from scoped shadowing";
      (match parse_program (program_to_c program) with
      | Error e -> failwith ("Local scope roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Local scope roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Local scope verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected local scope example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_local_array_memory_examples () =
  let safe_source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "int out;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  int xs[2];\n"
    ^ "  int *p;\n"
    ^ "  p = &xs[0];\n"
    ^ "  p[1] = 7;\n"
    ^ "  out = xs[1];\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  let unsafe_source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  int xs[2];\n"
    ^ "  int i;\n"
    ^ "  i = 2;\n"
    ^ "  xs[i] = 7;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  (match parse_program safe_source with
  | Error e -> failwith ("Local array safe parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Local array safe verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected local array safe example to verify, got:\n"
            ^ Verify.format_outcome outcome)));
  match parse_program unsafe_source with
  | Error e -> failwith ("Local array unsafe parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Local array unsafe verification failed: " ^ e)
      | Ok (Verify.Counterexample _) -> ()
      | Ok outcome ->
          failwith
            ("Expected local array unsafe example to fail verification, got:\n"
            ^ Verify.format_outcome outcome))

let assert_array_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "int xs[4];\n"
    ^ "int *p;\n"
    ^ "int y;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  p = &xs[1];\n"
    ^ "  xs[0] = 3;\n"
    ^ "  xs[1] = (xs[0] + 4);\n"
    ^ "  p[1] = (xs[1] + 1);\n"
    ^ "  y = p[1];\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Array parse failed: " ^ e)
  | Ok program ->
      (match parse_program (program_to_c program) with
      | Error e -> failwith ("Array roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Array roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Array verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected array example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_array_out_of_bounds_reports_counterexample () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "int xs[2];\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  xs[2] = 7;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Array OOB parse failed: " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Array OOB verification failed: " ^ e)
      | Ok (Verify.Counterexample _) -> ()
      | Ok outcome ->
          failwith
            ("Expected array bounds example to fail verification, got:\n"
            ^ Verify.format_outcome outcome))

let assert_record_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "struct Leaf {\n"
    ^ "  int value;\n"
    ^ "};\n\n"
    ^ "struct Node {\n"
    ^ "  struct Leaf leaf;\n"
    ^ "  struct Leaf leaves[2];\n"
    ^ "  int slots[2];\n"
    ^ "  struct Leaf *next;\n"
    ^ "};\n\n"
    ^ "struct Leaf leaf0;\n"
    ^ "struct Node node;\n"
    ^ "struct Node *np;\n"
    ^ "struct Leaf *lp;\n"
    ^ "int out;\n\n"
    ^ "/* @Require 1\n"
    ^ " * @Guarantee 1\n"
    ^ " * @Safety heap_ok()\n"
    ^ " */\n"
    ^ "int main(void) {\n"
    ^ "  node.leaf.value = 1;\n"
    ^ "  node.leaves[0].value = 2;\n"
    ^ "  node.slots[0] = 3;\n"
    ^ "  np = &node;\n"
    ^ "  np->leaves[1].value = (node.slots[0] + node.leaf.value);\n"
    ^ "  out = np->leaf.value;\n"
    ^ "  out = node.leaves[1].value;\n"
    ^ "  lp = &node.leaf;\n"
    ^ "  out = lp->value;\n"
    ^ "  node.next = &leaf0;\n"
    ^ "  lp = node.next;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Record parse failed: " ^ e)
  | Ok program ->
      (match parse_program (program_to_c program) with
      | Error e -> failwith ("Record roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Record roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Record verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected record example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_compound_assignment_roundtrip () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "struct Counter {\n"
    ^ "  int value;\n"
    ^ "};\n\n"
    ^ "int x;\n"
    ^ "int xs[2];\n"
    ^ "int *p;\n"
    ^ "struct Counter c;\n"
    ^ "struct Counter *cp;\n\n"
    ^ "int main(void) {\n"
    ^ "  p = &x;\n"
    ^ "  cp = &c;\n"
    ^ "  x += 1;\n"
    ^ "  x -= 2;\n"
    ^ "  xs[0] += 3;\n"
    ^ "  xs[1] -= 4;\n"
    ^ "  c.value += 5;\n"
    ^ "  cp->value -= 6;\n"
    ^ "  *p += 7;\n"
    ^ "  *p -= 8;\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Compound assignment parse failed: " ^ e)
  | Ok program ->
      let desugared = program_to_c program in
      if not (String.is_substring desugared ~substring:"x += 1;") then
        failwith "Expected variable `+=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"x -= 2;") then
        failwith "Expected variable `-=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"xs[0] += 3;") then
        failwith "Expected array `+=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"xs[1] -= 4;") then
        failwith "Expected array `-=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"c.value += 5;") then
        failwith "Expected field `+=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"cp->value -= 6;") then
        failwith "Expected arrow-field `-=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"*p += 7;") then
        failwith "Expected dereference `+=` to roundtrip through the pretty-printer";
      if not (String.is_substring desugared ~substring:"*p -= 8;") then
        failwith "Expected dereference `-=` to roundtrip through the pretty-printer";
      (match parse_program desugared with
      | Error e -> failwith ("Compound assignment roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Compound assignment roundtrip mismatch")

let assert_class_desugaring_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "class Counter {\n"
    ^ "  int value;\n"
    ^ "  int put(int next) {\n"
    ^ "    value = next;\n"
    ^ "    return get();\n"
    ^ "  }\n"
    ^ "  int get() {\n"
    ^ "    return value;\n"
    ^ "  }\n"
    ^ "};\n\n"
    ^ "Counter c;\n"
    ^ "Counter *cp;\n"
    ^ "int out;\n\n"
    ^ "int main(void) {\n"
    ^ "  out = c.put(7);\n"
    ^ "  cp = &c;\n"
    ^ "  out = cp->get();\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Class parse failed: " ^ e)
  | Ok program ->
      if not (List.exists program.records ~f:(fun record -> String.equal record.record_name "Counter")) then
        failwith "Expected class desugaring to introduce `struct Counter`";
      let method_names = List.map program.functions ~f:(fun fn -> fn.name) in
      if not (List.mem method_names "Counter__put" ~equal:String.equal) then
        failwith "Expected `Counter__put` in desugared methods";
      if not (List.mem method_names "Counter__get" ~equal:String.equal) then
        failwith "Expected `Counter__get` in desugared methods";
      let desugared = program_to_c program in
      if String.is_substring desugared ~substring:"class Counter" then
        failwith "Expected pretty-printer to emit desugared C, not class syntax";
      if not (String.is_substring desugared ~substring:"Counter__put(&c, 7)") then
        failwith "Expected dot-call desugaring to pass `&c` to `Counter__put`";
      if not (String.is_substring desugared ~substring:"Counter__get(cp)") then
        failwith "Expected arrow-call desugaring to pass `cp` to `Counter__get`";
      if not (String.is_substring desugared ~substring:"return Counter__get(this);") then
        failwith "Expected implicit method call to desugar through `this`";
      (match parse_program desugared with
      | Error e -> failwith ("Class desugared roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Class desugared roundtrip mismatch");
      (match Instrument.instrument_program program with
      | Error e -> failwith ("Class instrumentation failed: " ^ e)
      | Ok instrumented ->
          assert_generated_c_compiles (program_to_c instrumented));
      (match Verify.verify_program program with
      | Error e -> failwith ("Class verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected class example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_namespace_resolution_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "namespace math {\n"
    ^ "  struct Pair {\n"
    ^ "    int left;\n"
    ^ "    int right;\n"
    ^ "  };\n"
    ^ "  Pair pair;\n"
    ^ "  int helper(Pair *p) {\n"
    ^ "    return (p->left + p->right);\n"
    ^ "  }\n"
    ^ "  namespace detail {\n"
    ^ "    int twice(int x) {\n"
    ^ "      return (x + x);\n"
    ^ "    }\n"
    ^ "  }\n"
    ^ "  int sum(void) {\n"
    ^ "    return detail::twice(helper(&pair));\n"
    ^ "  }\n"
    ^ "}\n\n"
    ^ "int out;\n\n"
    ^ "int main(void) {\n"
    ^ "  math::pair.left = 2;\n"
    ^ "  math::pair.right = 5;\n"
    ^ "  out = math::sum();\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Namespace parse failed: " ^ e)
  | Ok program ->
      if not (List.exists program.records ~f:(fun record -> String.equal record.record_name "math__ns__Pair")) then
        failwith "Expected namespaced record to be flattened to `math__ns__Pair`";
      if not (List.exists program.globals ~f:(fun global -> String.equal global.global_name "math__ns__pair")) then
        failwith "Expected namespaced global to be flattened to `math__ns__pair`";
      let function_names = List.map program.functions ~f:(fun fn -> fn.name) in
      if not (List.mem function_names "math__ns__helper" ~equal:String.equal) then
        failwith "Expected `math__ns__helper` in flattened functions";
      if not (List.mem function_names "math__ns__detail__ns__twice" ~equal:String.equal) then
        failwith "Expected nested namespace function to flatten to `math__ns__detail__ns__twice`";
      if not (List.mem function_names "math__ns__sum" ~equal:String.equal) then
        failwith "Expected `math__ns__sum` in flattened functions";
      let desugared = program_to_c program in
      if String.is_substring desugared ~substring:"namespace math" then
        failwith "Expected pretty-printer to emit flattened C, not namespace syntax";
      if not (String.is_substring desugared ~substring:"return math__ns__detail__ns__twice(math__ns__helper(&math__ns__pair));") then
        failwith "Expected namespace references to resolve in function bodies";
      if not (String.is_substring desugared ~substring:"math__ns__pair.left = 2;") then
        failwith "Expected explicit qualified global access to flatten";
      (match parse_program desugared with
      | Error e -> failwith ("Namespace roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Namespace roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Namespace verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected namespace example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_namespaced_class_desugaring_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "namespace box {\n"
    ^ "  class Counter {\n"
    ^ "    int value;\n"
    ^ "    int put(int next) {\n"
    ^ "      value = next;\n"
    ^ "      return get();\n"
    ^ "    }\n"
    ^ "    int get() {\n"
    ^ "      return value;\n"
    ^ "    }\n"
    ^ "  };\n"
    ^ "}\n\n"
    ^ "box::Counter c;\n"
    ^ "box::Counter *cp;\n"
    ^ "int out;\n\n"
    ^ "int main(void) {\n"
    ^ "  out = c.put(7);\n"
    ^ "  cp = &c;\n"
    ^ "  out = cp->get();\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Namespaced class parse failed: " ^ e)
  | Ok program ->
      if
        not
          (List.exists program.records ~f:(fun record ->
               String.equal record.record_name "box__ns__Counter"))
      then
        failwith "Expected namespaced class desugaring to introduce `struct box__ns__Counter`";
      let method_names = List.map program.functions ~f:(fun fn -> fn.name) in
      if not (List.mem method_names "box__ns__Counter__put" ~equal:String.equal) then
        failwith "Expected `box__ns__Counter__put` in desugared methods";
      if not (List.mem method_names "box__ns__Counter__get" ~equal:String.equal) then
        failwith "Expected `box__ns__Counter__get` in desugared methods";
      let desugared = program_to_c program in
      if String.is_substring desugared ~substring:"namespace box" then
        failwith "Expected pretty-printer to emit flattened C, not namespace syntax";
      if String.is_substring desugared ~substring:"class Counter" then
        failwith "Expected pretty-printer to emit desugared C, not class syntax";
      if not (String.is_substring desugared ~substring:"box__ns__Counter__put(&c, 7)") then
        failwith "Expected dot-call desugaring to preserve the namespaced class name";
      if not (String.is_substring desugared ~substring:"box__ns__Counter__get(cp)") then
        failwith "Expected arrow-call desugaring to preserve the namespaced class name";
      if not (String.is_substring desugared ~substring:"return box__ns__Counter__get(this);") then
        failwith "Expected implicit method call to desugar through the namespaced class receiver";
      (match parse_program desugared with
      | Error e -> failwith ("Namespaced class roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Namespaced class roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Namespaced class verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected namespaced class example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_function_overloading_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "int x;\n"
    ^ "int out;\n"
    ^ "bool flag;\n\n"
    ^ "int pick(int value) {\n"
    ^ "  return (value + 1);\n"
    ^ "}\n\n"
    ^ "int pick(bool high) {\n"
    ^ "  if (high) {\n"
    ^ "    return 7;\n"
    ^ "  } else {\n"
    ^ "    return 3;\n"
    ^ "  }\n"
    ^ "}\n\n"
    ^ "int main(void) {\n"
    ^ "  flag = true;\n"
    ^ "  x = pick(4);\n"
    ^ "  out = pick(flag);\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Function overloading parse failed: " ^ e)
  | Ok program ->
      let function_names = List.map program.functions ~f:(fun fn -> fn.name) in
      if not (List.mem function_names "pick__ol__int" ~equal:String.equal) then
        failwith "Expected `pick__ol__int` in overloaded functions";
      if not (List.mem function_names "pick__ol__bool" ~equal:String.equal) then
        failwith "Expected `pick__ol__bool` in overloaded functions";
      let desugared = program_to_c program in
      if not (String.is_substring desugared ~substring:"int pick__ol__int(int value)") then
        failwith "Expected the `int` overload to be mangled in the pretty-printer";
      if not (String.is_substring desugared ~substring:"int pick__ol__bool(bool high)") then
        failwith "Expected the `bool` overload to be mangled in the pretty-printer";
      if not (String.is_substring desugared ~substring:"x = pick__ol__int(4);") then
        failwith "Expected the `int` call site to resolve to `pick__ol__int`";
      if not (String.is_substring desugared ~substring:"out = pick__ol__bool(flag);") then
        failwith "Expected the `bool` call site to resolve to `pick__ol__bool`";
      (match parse_program desugared with
      | Error e -> failwith ("Function overloading roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Function overloading roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Function overloading verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected overloaded free-function example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_method_overloading_roundtrip_and_verification () =
  let source =
    "#include <stdlib.h>\n"
    ^ "#include <stdio.h>\n"
    ^ "#include <stdbool.h>\n\n"
    ^ "class Counter {\n"
    ^ "  int value;\n"
    ^ "  int put(int next) {\n"
    ^ "    value = next;\n"
    ^ "    return get();\n"
    ^ "  }\n"
    ^ "  int put(bool bump) {\n"
    ^ "    if (bump) {\n"
    ^ "      value = (value + 1);\n"
    ^ "    }\n"
    ^ "    return get();\n"
    ^ "  }\n"
    ^ "  int get() {\n"
    ^ "    return value;\n"
    ^ "  }\n"
    ^ "};\n\n"
    ^ "Counter c;\n"
    ^ "Counter *cp;\n"
    ^ "int out;\n"
    ^ "bool flag;\n\n"
    ^ "int main(void) {\n"
    ^ "  out = c.put(7);\n"
    ^ "  flag = true;\n"
    ^ "  out = c.put(flag);\n"
    ^ "  cp = &c;\n"
    ^ "  out = cp->put(false);\n"
    ^ "  return 0;\n"
    ^ "}\n"
  in
  match parse_program source with
  | Error e -> failwith ("Method overloading parse failed: " ^ e)
  | Ok program ->
      let method_names = List.map program.functions ~f:(fun fn -> fn.name) in
      if not (List.mem method_names "Counter__put__ol__int" ~equal:String.equal) then
        failwith "Expected `Counter__put__ol__int` in overloaded methods";
      if not (List.mem method_names "Counter__put__ol__bool" ~equal:String.equal) then
        failwith "Expected `Counter__put__ol__bool` in overloaded methods";
      if not (List.mem method_names "Counter__get" ~equal:String.equal) then
        failwith "Expected unique method `Counter__get` to remain unmangled";
      let desugared = program_to_c program in
      if not (String.is_substring desugared ~substring:"Counter__put__ol__int(&c, 7)") then
        failwith "Expected the dot-call `int` overload to resolve to `Counter__put__ol__int`";
      if not (String.is_substring desugared ~substring:"Counter__put__ol__bool(&c, flag)") then
        failwith "Expected the dot-call `bool` overload to resolve to `Counter__put__ol__bool`";
      if not (String.is_substring desugared ~substring:"Counter__put__ol__bool(cp, false)") then
        failwith "Expected the arrow-call `bool` overload to resolve to `Counter__put__ol__bool`";
      if not (String.is_substring desugared ~substring:"return Counter__get(this);") then
        failwith "Expected implicit `get()` calls to resolve through the unmangled unique method";
      (match parse_program desugared with
      | Error e -> failwith ("Method overloading roundtrip failed: " ^ e)
      | Ok roundtripped ->
          if not (equal_program program roundtripped) then
            failwith "Method overloading roundtrip mismatch");
      (match Verify.verify_program program with
      | Error e -> failwith ("Method overloading verification failed: " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected overloaded method example to verify, got:\n"
            ^ Verify.format_outcome outcome))

let assert_example_file_verifies file_name =
  let path = "test/e2e_cases/" ^ file_name in
  let source = In_channel.read_all path in
  match parse_program ~base_dir:"test/e2e_cases" ~source_name:path source with
  | Error e -> failwith ("Example parse failed for " ^ file_name ^ ": " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Example verification failed for " ^ file_name ^ ": " ^ e)
      | Ok Verify.Verified -> ()
      | Ok outcome ->
          failwith
            ("Expected example to verify for "
            ^ file_name
            ^ ", got:\n"
            ^ Verify.format_outcome outcome))

let assert_example_file_reports_counterexample file_name =
  let path = "test/e2e_cases/" ^ file_name in
  let source = In_channel.read_all path in
  match parse_program ~base_dir:"test/e2e_cases" ~source_name:path source with
  | Error e -> failwith ("Example parse failed for " ^ file_name ^ ": " ^ e)
  | Ok program ->
      (match Verify.verify_program program with
      | Error e -> failwith ("Example verification failed for " ^ file_name ^ ": " ^ e)
      | Ok (Verify.Counterexample _) -> ()
      | Ok outcome ->
          failwith
            ("Expected example to report a counterexample for "
            ^ file_name
            ^ ", got:\n"
            ^ Verify.format_outcome outcome))

let assert_typed_memory_examples_verify () =
  List.iter
    [ "memory_safe_int_expression.c"
    ; "memory_safe_float_expression.c"
    ; "memory_safe_double_expression.c"
    ; "memory_safe_char_expression.c"
    ; "memory_safe_bool_expression.c"
    ; "memory_safe_array_expression.c"
    ; "memory_safe_record_expression.c"
    ; "record_pointer_field_deref.c"
    ]
    ~f:assert_example_file_verifies

let assert_typed_memory_negative_examples_fail () =
  List.iter
    [ "memory_unsafe_int_too_small.c"
    ; "memory_unsafe_float_too_small.c"
    ; "memory_unsafe_double_too_small.c"
    ; "memory_unsafe_char_out_of_bounds.c"
    ; "memory_unsafe_bool_out_of_bounds.c"
    ; "memory_unsafe_array_out_of_bounds.c"
    ]
    ~f:assert_example_file_reports_counterexample

let () =
  assert_header_import_roundtrip ();
  assert_contract_instrumentation ();
  assert_local_contract_roundtrip_and_instrumentation ();
  assert_verifier_reports_counterexample ();
  assert_counterexample_reports_require_location ();
  assert_counterexample_reports_guarantee_location ();
  assert_verifier_accepts_loop_post_invariant ();
  assert_loop_invariant_roundtrip_and_verification ();
  assert_memory_safe_program_verifies ();
  assert_memory_unsafe_program_reports_counterexample ();
  assert_memory_too_small_allocation_reports_counterexample ();
  assert_local_scope_shadowing_roundtrip_and_verification ();
  assert_local_array_memory_examples ();
  assert_array_roundtrip_and_verification ();
  assert_array_out_of_bounds_reports_counterexample ();
  assert_record_roundtrip_and_verification ();
  assert_compound_assignment_roundtrip ();
  assert_class_desugaring_roundtrip_and_verification ();
  assert_namespace_resolution_roundtrip_and_verification ();
  assert_namespaced_class_desugaring_roundtrip_and_verification ();
  assert_function_overloading_roundtrip_and_verification ();
  assert_method_overloading_roundtrip_and_verification ();
  assert_typed_memory_examples_verify ();
  assert_typed_memory_negative_examples_fail ();
  Quickcheck.test
    ~trials:300
    ~sexp_of:(fun _ -> Sexp.Atom "program")
    (gen_program 4)
    ~f:(fun p ->
      let code = program_to_c p in
      match parse_program code with
      | Error e -> failwith ("Parse failed: " ^ e ^ "\nGenerated code:\n" ^ code)
      | Ok p2 ->
          if not (equal_program p p2) then
            failwith
              ("Roundtrip mismatch:\ninput="
              ^ code
              ^ "\nparsed:\n"
              ^ program_to_c p2)
    )
