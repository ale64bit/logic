open Lib
open Lib.Fol
open OUnit2
open Proof
open Proof.Calculus

let shoenfield_ch2_5a _ =
  let proof =
    let open Theorems.Common in
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.propositional ctx (Neg (Atom ("=", [ x; x ]))) in
    proves ctx s1
  in
  let want = Theorems.Shoenfield.ch2_5a in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5b _ =
  let proof =
    let open Theorems.Common in
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.substitution ctx (Atom ("=", [ x; x ])) "x" x in
    proves ctx s1
  in
  let want = Theorems.Shoenfield.ch2_5b in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5c _ =
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.identity ctx "x" in
    proves ctx s1
  in
  let want = Theorems.Shoenfield.ch2_5c in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5d _ =
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.pequality ctx [ ("x", "y"); ("x", "z") ] "=" in
    proves ctx s1
  in
  let want = Theorems.Shoenfield.ch2_5d in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5e _ =
  let proof =
    let open Theorems.Common in
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.identity ctx "x" in
    let* ctx, s2 = Rule.expansion ctx (Neg x_eq_x) s1 in
    let* ctx, s3 = Rule.expansion ctx x_eq_x s2 in
    proves ctx s3
  in
  let want = Theorems.Shoenfield.ch2_5e in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5fh _ =
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.identity ctx "x" in
    let* ctx, s2 = Meta.dneg_intro ctx s1 in
    proves ctx s2
  in
  let want = Theorems.Shoenfield.ch2_5f in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5g _ =
  let proof =
    let open Theorems.Common in
    let b = Or (Neg x_eq_x, Neg x_eq_x) in
    let ctx = empty_proof in
    let* ctx, _ = Axiom.identity ctx "x" in
    let* ctx, s2 = Axiom.propositional ctx b in
    let* ctx, s3 = Rule.associative ctx s2 in
    let* ctx, s4 = Rule.expansion ctx (Or (Neg b, Neg x_eq_x)) x_eq_x in
    let* ctx, s5 = Meta.commute ctx s3 in
    let* ctx, s6 = Meta.commute ctx s4 in
    let* ctx, s7 = Rule.cut ctx s6 s5 in
    let* ctx, s8 = Rule.contraction ctx s7 in
    let* ctx, s9 = Rule.expansion ctx (Neg b) x_eq_x in
    let* ctx, s10 = Meta.commute ctx s8 in
    let* ctx, s11 = Meta.commute ctx s9 in
    let* ctx, s12 = Rule.cut ctx s11 s10 in
    let* ctx, s13 = Rule.contraction ctx s12 in
    proves ctx s13
  in
  let want = Theorems.Shoenfield.ch2_5g in
  TestUtil.check_conclusion proof want

let shoenfield_ch2_5i _ =
  let proof =
    let open Theorems.Common in
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.propositional ctx (Neg x_eq_x) in
    let* ctx, s2 = Rule.e_introduction ctx "y" s1 in
    proves ctx s2
  in
  let want = Theorems.Shoenfield.ch2_5i in
  TestUtil.check_conclusion proof want

let commute _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx (Or (px, qx)) in
    let* ctx, s2 = Meta.commute ctx s1 in
    proves ctx s2
  in
  let want = Or (qx, px) in
  TestUtil.check_conclusion proof want

let modus_ponens _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx px in
    let* ctx, s2 = premise ctx (Defined.impl px qx) in
    let* ctx, s3 = Meta.modus_ponens ctx s1 s2 in
    proves ctx s3
  in
  let want = qx in
  TestUtil.check_conclusion proof want

let taut_theorem_case_b _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx (Or (px, qx)) in
    let* ctx, s2 = Meta.disj_dneg ctx s1 in
    proves ctx s2
  in
  let want = Or (Neg (Neg px), qx) in
  TestUtil.check_conclusion proof want

let taut_theorem_case_c _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx (Or (Neg px, rx)) in
    let* ctx, s2 = premise ctx (Or (Neg qx, rx)) in
    let* ctx, s3 = Axiom.propositional ctx (Or (px, qx)) in
    let* ctx, s4 = Rule.associative ctx s3 in
    let* ctx, s5 = Meta.commute ctx s4 in
    let* ctx, s6 = Rule.cut ctx s5 s2 in
    let* ctx, s7 = Meta.commute ctx s6 in
    let* ctx, s8 = Rule.associative ctx s7 in
    let* ctx, s9 = Meta.commute ctx s8 in
    let* ctx, s10 = Rule.cut ctx s9 s1 in
    let* ctx, s11 = Meta.commute ctx s10 in
    let* ctx, s12 = Rule.associative ctx s11 in
    let* ctx, s13 = Meta.commute ctx s12 in
    let* ctx, s14 = Meta.disj_contraction ctx s13 in
    proves ctx s14
  in
  let want = Or (Neg (Or (px, qx)), rx) in
  TestUtil.check_conclusion proof want

let general_expansion _ =
  let x = Var "x" in
  let p i = Atom (Printf.sprintf "p%d" i, [ x ]) in
  let tests =
    [
      ([ p 1 ], [ p 1 ]);
      ([ p 1 ], [ p 1; p 2 ]);
      ([ p 2 ], [ p 1; p 2 ]);
      ([ p 1 ], [ p 1; p 2; p 3 ]);
      ([ p 2 ], [ p 1; p 2; p 3 ]);
      ([ p 3 ], [ p 1; p 2; p 3 ]);
      ([ p 1 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 2 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 3 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 2 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 3 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 2; p 3 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 2; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 3; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 2; p 3 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 2; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 3; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 2; p 3; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 1; p 2; p 3; p 4 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 4; p 1; p 2; p 3 ], [ p 1; p 2; p 3; p 4 ]);
      ([ p 4; p 3; p 2; p 1 ], [ p 1; p 2; p 3; p 4 ]);
    ]
  in
  List.iter
    (fun (a', a) ->
      let want = disj_of_list a in
      let proof =
        let ctx = empty_proof in
        let* ctx, _ = premise ctx (disj_of_list a') in
        let* ctx, s2 = Meta.general_expansion ctx a' a in
        proves ctx s2
      in
      TestUtil.check_conclusion proof want)
    tests

let substitution_rule _ =
  let open Theorems.Common in
  let e i = Const (Printf.sprintf "e%d" i) in
  let tests =
    [
      (x_eq_x, Atom ("=", [ e 1; e 1 ]));
      (x_eq_y, Atom ("=", [ e 1; e 1 ]));
      (x_eq_y, Atom ("=", [ e 2; e 1 ]));
    ]
  in
  List.iter
    (fun (a, a') ->
      let proof =
        let ctx = empty_proof in
        let* ctx, _ = premise ctx a in
        let* ctx, s2 = Meta.substitution ctx a a' in
        proves ctx s2
      in
      TestUtil.check_conclusion proof a')
    tests

let e_distribution _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx (Defined.impl px qx) in
    let* ctx, s2 = Meta.e_distribution ctx "x" s1 in
    proves ctx s2
  in
  let want = Defined.impl (Exists ("x", px)) (Exists ("x", qx)) in
  TestUtil.check_conclusion proof want

let a_distribution _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx (Defined.impl px qx) in
    let* ctx, s2 = Meta.a_distribution ctx "x" s1 in
    proves ctx s2
  in
  let want = Defined.impl (Defined.forall "x" px) (Defined.forall "x" qx) in
  TestUtil.check_conclusion proof want

let shoenfield_ch3_5_exists _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = premise ctx py in
    let* ctx, s2 = Axiom.substitution ctx s1 "x" x in
    let* ctx, s3 = Axiom.propositional ctx py in
    let* ctx, s4 = Rule.e_introduction ctx "x" s3 in
    let* ctx, s5 = Meta.conj ctx s2 s4 in
    proves ctx s5
  in
  let want = Defined.eq py (Exists ("x", py)) in
  TestUtil.check_conclusion proof want

let shoenfield_ch3_6a _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.substitution ctx pxy "x" x in
    let* ctx, s2 = Axiom.substitution ctx (Exists ("x", pxy)) "y" y in
    let* ctx, s3 = Meta.detachment_transitivity ctx s1 s2 in
    let* ctx, s4 = Rule.e_introduction ctx "y" s3 in
    let* ctx, s5 = Rule.e_introduction ctx "x" s4 in
    let* ctx, s1' = Axiom.substitution ctx pxy "y" y in
    let* ctx, s2' = Axiom.substitution ctx (Exists ("y", pxy)) "x" x in
    let* ctx, s3' = Meta.detachment_transitivity ctx s1' s2' in
    let* ctx, s4' = Rule.e_introduction ctx "x" s3' in
    let* ctx, s5' = Rule.e_introduction ctx "y" s4' in
    let* ctx, s6 = Meta.conj ctx s5 s5' in
    proves ctx s6
  in
  let want =
    Defined.eq
      (Exists ("x", Exists ("y", pxy)))
      (Exists ("y", Exists ("x", pxy)))
  in
  TestUtil.check_conclusion proof want

let shoenfield_ch3_6c _ =
  let open Theorems.Common in
  let proof =
    let ctx = empty_proof in
    let* ctx, s1 = Axiom.substitution ctx pxy "x" x in
    let* ctx, s2 = Meta.a_distribution ctx "y" s1 in
    let* ctx, s3 = Rule.e_introduction ctx "x" s2 in
    proves ctx s3
  in
  let want =
    Defined.impl
      (Exists ("x", Defined.forall "y" pxy))
      (Defined.forall "y" (Exists ("x", pxy)))
  in
  TestUtil.check_conclusion proof want

let suite =
  "ProofTests"
  >::: [
         "shoenfield_ch2_5a" >:: shoenfield_ch2_5a;
         "shoenfield_ch2_5b" >:: shoenfield_ch2_5b;
         "shoenfield_ch2_5c" >:: shoenfield_ch2_5c;
         "shoenfield_ch2_5d" >:: shoenfield_ch2_5d;
         "shoenfield_ch2_5e" >:: shoenfield_ch2_5e;
         "shoenfield_ch2_5fh" >:: shoenfield_ch2_5fh;
         "shoenfield_ch2_5g" >:: shoenfield_ch2_5g;
         "shoenfield_ch2_5i" >:: shoenfield_ch2_5i;
         "commute" >:: commute;
         "modus_ponens" >:: modus_ponens;
         "taut_theorem_case_b" >:: taut_theorem_case_b;
         "taut_theorem_case_c" >:: taut_theorem_case_c;
         "general_expansion" >:: general_expansion;
         "substitution_rule" >:: substitution_rule;
         "e_distribution" >:: e_distribution;
         "a_distribution" >:: a_distribution;
         "shoenfield_ch3_5_exists" >:: shoenfield_ch3_5_exists;
         "shoenfield_ch3_6a" >:: shoenfield_ch3_6a;
         "shoenfield_ch3_6c" >:: shoenfield_ch3_6c;
       ]

let () = run_test_tt_main suite
