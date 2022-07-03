open OUnit2

let taut_theorem _ =
  let tests = Corpus.Pelletier.propositional @ Corpus.DeMorgan.all in
  List.iter
    (fun (id, src) ->
      let status, dataform = Prover.App.parse_and_solve (module Prover.TautTheorem.S) id (Lexing.from_string src) in
      let () = assert_equal ~printer:Core.SZS.string_of_status Core.SZS.(Success Theorem) status in
      let size =
        match dataform with
        | Core.SZS.Proof { lines; _ } -> List.length lines
        | _ -> assert_failure "dataform is not Proof"
      in
      Printf.printf "proved %s in %d steps\n%!" id size)
    tests

let suite = "Prover.TautTheorem" >::: [ "taut_theorem" >:: taut_theorem ]
let () = run_test_tt_main suite
