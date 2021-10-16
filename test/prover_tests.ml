open Lib
open OUnit2

let shoenfield _ =
  let tests =
    [
      Theorems.P75.p1;
      Theorems.P75.p2;
      Theorems.P75.p3;
      Theorems.P75.p4;
      Theorems.P75.p5;
      Theorems.P75.p6;
      Theorems.P75.p7;
      Theorems.P75.p8;
      Theorems.P75.p9;
      (* TODO(needs premises): Theorems.P75.p10; *)
      Theorems.P75.p11;
      Theorems.P75.p12;
      Theorems.P75.p13;
      Theorems.P75.p14;
      Theorems.P75.p15;
      Theorems.P75.p16;
      Theorems.P75.p17;
      Theorems.Shoenfield.ch2_5a;
      (* TODO(has quantifiers): Theorems.Shoenfield.ch2_5b; *)
      Theorems.Shoenfield.ch2_5c;
      (* TODO(has quantifiers): Theorems.Shoenfield.ch2_5d; *)
      Theorems.Shoenfield.ch2_5e;
      Theorems.Shoenfield.ch2_5f;
      Theorems.Shoenfield.ch2_5g;
      Theorems.Shoenfield.ch2_5h;
      (* TODO(has quantifiers): Theorems.Shoenfield.ch2_5i; *)
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
