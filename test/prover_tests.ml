open Lib
open OUnit2

let shoenfield _ =
  let tests =
    [
      Theorems.Pelletier1986.p1;
      Theorems.Pelletier1986.p2;
      Theorems.Pelletier1986.p3;
      Theorems.Pelletier1986.p4;
      Theorems.Pelletier1986.p5;
      Theorems.Pelletier1986.p6;
      Theorems.Pelletier1986.p7;
      Theorems.Pelletier1986.p8;
      Theorems.Pelletier1986.p9;
      Theorems.Pelletier1986.p10;
      Theorems.Pelletier1986.p11;
      Theorems.Pelletier1986.p12;
      Theorems.Pelletier1986.p13;
      Theorems.Pelletier1986.p14;
      Theorems.Pelletier1986.p15;
      Theorems.Pelletier1986.p16;
      Theorems.Pelletier1986.p17;
      Theorems.Shoenfield1967.ch2_5a;
      (* TODO(has quantifiers): Theorems.Shoenfield1967.ch2_5b; *)
      Theorems.Shoenfield1967.ch2_5c;
      (* TODO(has quantifiers): Theorems.Shoenfield1967.ch2_5d; *)
      Theorems.Shoenfield1967.ch2_5e;
      Theorems.Shoenfield1967.ch2_5f;
      Theorems.Shoenfield1967.ch2_5g;
      Theorems.Shoenfield1967.ch2_5h;
      (* TODO(has quantifiers): Theorems.Shoenfield1967.ch2_5i; *)
      Theorems.DeMorgan.conj;
      Theorems.DeMorgan.disj;
    ]
  in
  List.iter
    (fun want ->
      let ctx = Proof.Base.empty_proof in
      let proof = Prover.Shoenfield.prove ctx want in
      TestUtil.check_conclusion proof want)
    tests

let suite = "ProverTests" >::: [ "shoenfield" >:: shoenfield ]

let () = run_test_tt_main suite
