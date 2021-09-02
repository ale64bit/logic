open Lib.Proof
open Lib.Fol
open OUnit2

let check_conclusion c want =
  let msg = Printf.sprintf "proving %s" (string_of_formula want) in
  match c with
  | Ok (proof, got) ->
      let () = if want = got then () else print_proof stdout proof in
      let () = assert_equal ~printer:string_of_formula ~msg want got in
      Printf.printf "proved %s in %d steps\n" (string_of_formula want)
        (Calculus.proof_length proof)
  | Error err -> assert_failure (Printf.sprintf "%s: invalid proof: %s" msg err)
