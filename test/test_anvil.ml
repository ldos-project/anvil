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
            globals =
              List.map globals ~f:(fun global_name ->
                  { global_type = TInt; global_name });
            functions = [];
            main =
              {
                name = "main";
                return_type = TInt;
                params = [];
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
  assert_array_roundtrip_and_verification ();
  assert_array_out_of_bounds_reports_counterexample ();
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
