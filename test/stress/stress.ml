open Lib.Fol

let shoenfield_ch3_ex2 rng k =
  let e = Const "e" in
  let e_eq_e = Atom ("=", [ e; e ]) in
  let rec f = function
    | Atom (p, bs) -> Atom (p, List.map (fun _ -> e) bs)
    | Neg a -> Neg (f a)
    | Or (a, b) -> Or (f a, f b)
    | Exists (_, a) -> f a
  in
  let rec aux rng k =
    if k = 0 then ()
    else
      let a = Lib.Proof.Calculus.random_theorem ~max_steps:100 rng in
      if is_tautological_consequence [ e_eq_e ] (f a) then
        let () = Printf.printf "OK: %s\n%!" (extended_string_of_formula a) in
        aux rng (k - 1)
      else
        Printf.printf "BAD: %s\n%s\n%!"
          (extended_string_of_formula a)
          (extended_string_of_formula (f a))
  in
  aux rng k

let tautology_is_theorem rng k =
  let open Lib.Proof in
  let module P = Lib.Prover.ShoenfieldTaut in
  let rec aux rng k =
    if k = 0 then ()
    else
      let a =
        random_formula ~max_depth:16
          ~variables:(List.init 6 (Printf.sprintf "x%d"))
          rng
      in
      if is_tautology a then
        match P.prove Base.empty_proof a with
        | Ok _ ->
            let () =
              Printf.printf "OK: %s: tautology is provable\n%!"
                (extended_string_of_formula a)
            in
            aux rng (k - 1)
        | Error msg ->
            Printf.printf "BAD: %s: no proof found for tautology: %s\n%!"
              (extended_string_of_formula a)
              msg
      else aux rng k
  in
  aux rng k

let () =
  let rng = Random.State.make_self_init () in
  shoenfield_ch3_ex2 rng 10000;
  tautology_is_theorem rng 100
