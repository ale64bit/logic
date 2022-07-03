module LANG = Lang.Shoenfield.S
module SYS = System.Shoenfield.Base
open LANG
open Lang.Shoenfield.Syntax (LANG)
open Lang.OperatorSyntax.Make (LANG)
open SYS
open OUnit2

let check_conclusion proof got want =
  let msg = Printf.sprintf "proving %s" (string_of_formula want) in
  let status, dataform = SYS.export (proof, got) in
  let () = assert_equal Core.SZS.(Success Theorem) status in
  let () = assert_equal ~printer:extended_string_of_formula ~msg want got in
  let size = match dataform with Core.SZS.Proof { lines; _ } -> List.length lines | _ -> -1 in
  Printf.printf "proved %s in %d steps\n" (extended_string_of_formula want) size

let shoenfield_ch2_5a _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got = pseq [ !x_eq_x => !x_eq_x <<= Axiom.propositional !x_eq_x ] empty in
  let want = !x_eq_x => !x_eq_x in
  check_conclusion proof got want

let shoenfield_ch2_5b _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got = pseq [ x_eq_x => exists "x" x_eq_x <<= Axiom.substitution x_eq_x "x" (var "x") ] empty in
  let want = x_eq_x => exists "x" x_eq_x in
  check_conclusion proof got want

let shoenfield_ch2_5c _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got = pseq [ x_eq_x <<= Axiom.identity "x" ] empty in
  let want = x_eq_x in
  check_conclusion proof got want

let shoenfield_ch2_5d _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let x_eq_y = atom "=" [ var "x"; var "y" ] in
  let x_eq_z = atom "=" [ var "x"; var "z" ] in
  let y_eq_z = atom "=" [ var "y"; var "z" ] in
  let proof, got =
    pseq [ x_eq_y => (x_eq_z => (x_eq_x => y_eq_z)) <<= Axiom.pequality [ ("x", "y"); ("x", "z") ] "=" ] empty
  in
  let want = x_eq_y => (x_eq_z => (x_eq_x => y_eq_z)) in
  check_conclusion proof got want

let shoenfield_ch2_5e _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got =
    pseq
      [
        x_eq_x <<= Axiom.identity "x";
        x_eq_x => x_eq_x <<= Rule.expansion !x_eq_x x_eq_x;
        (x_eq_x || x_eq_x => x_eq_x) <<= Rule.expansion x_eq_x (x_eq_x => x_eq_x);
      ]
      empty
  in
  let want = x_eq_x || x_eq_x => x_eq_x in
  check_conclusion proof got want

let shoenfield_ch2_5fh _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got = pseq [ x_eq_x <<= Axiom.identity "x"; !(!x_eq_x) <<= Meta.dneg_introduction x_eq_x ] empty in
  let want = !(!x_eq_x) in
  check_conclusion proof got want

let shoenfield_ch2_5g _ =
  let xex = atom "=" [ var "x"; var "x" ] in
  let proof, got =
    pseq
      [
        xex <<= Axiom.identity "x";
        (!(!xex || !xex) || !xex || !xex) <<= Axiom.propositional (!xex || !xex);
        ((!(!xex || !xex) || !xex) || !xex) <<= Rule.associative (!(!xex || !xex) || !xex || !xex);
        ((!(!xex || !xex) || !xex) || xex) <<= Rule.expansion (!(!xex || !xex) || !xex) xex;
        (!xex || !(!xex || !xex) || !xex) <<= Meta.disj_commute ((!(!xex || !xex) || !xex) || !xex);
        (xex || !(!xex || !xex) || !xex) <<= Meta.disj_commute ((!(!xex || !xex) || !xex) || xex);
        ((!(!xex || !xex) || !xex) || !(!xex || !xex) || !xex)
        <<= Rule.cut (xex || !(!xex || !xex) || !xex) (!xex || !(!xex || !xex) || !xex);
        (!(!xex || !xex) || !xex) <<= Rule.contraction ((!(!xex || !xex) || !xex) || !(!xex || !xex) || !xex);
        (!(!xex || !xex) || xex) <<= Rule.expansion !(!xex || !xex) xex;
        (!xex || !(!xex || !xex)) <<= Meta.disj_commute (!(!xex || !xex) || !xex);
        (xex || !(!xex || !xex)) <<= Meta.disj_commute (!(!xex || !xex) || xex);
        (!(!xex || !xex) || !(!xex || !xex)) <<= Rule.cut (xex || !(!xex || !xex)) (!xex || !(!xex || !xex));
        !(!xex || !xex) <<= Rule.contraction (!(!xex || !xex) || !(!xex || !xex));
      ]
      empty
  in
  let want = !(!xex || !xex) in
  check_conclusion proof got want

let shoenfield_ch2_5i _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let proof, got =
    pseq
      [
        !x_eq_x => !x_eq_x <<= Axiom.propositional !x_eq_x;
        exists "y" !x_eq_x => !x_eq_x <<= Rule.e_introduction "y" (!x_eq_x => !x_eq_x);
      ]
      empty
  in
  let want = exists "y" !x_eq_x => !x_eq_x in
  check_conclusion proof got want

let commute _ =
  let p = atom "p" [] in
  let q = atom "q" [] in
  let proof, got = pseq [ (p || q) <<= premise (p || q); (q || p) <<= Meta.disj_commute (p || q) ] empty in
  let want = q || p in
  check_conclusion proof got want

let detachment _ =
  let p = atom "p" [] in
  let q = atom "q" [] in
  let proof, got = pseq [ p <<= premise p; p => q <<= premise (p => q); q <<= Meta.detachment p (p => q) ] empty in
  let want = q in
  check_conclusion proof got want

let taut_theorem_case_b _ =
  let p = atom "p" [] in
  let q = atom "q" [] in
  let proof, got = pseq [ (p || q) <<= premise (p || q); (!(!p) || q) <<= Meta.disj_dneg (p || q) ] empty in
  let want = !(!p) || q in
  check_conclusion proof got want

let taut_theorem_case_c _ =
  let p = atom "p" [] in
  let q = atom "q" [] in
  let r = atom "r" [] in
  let proof, got =
    pseq
      [
        p => r <<= premise (p => r);
        q => r <<= premise (q => r);
        (!(p || q) || p || q) <<= Axiom.propositional (p || q);
        ((!(p || q) || p) || q) <<= Rule.associative (!(p || q) || p || q);
        (q || !(p || q) || p) <<= Meta.disj_commute ((!(p || q) || p) || q);
        ((!(p || q) || p) || r) <<= Rule.cut (q || !(p || q) || p) (q => r);
        (r || !(p || q) || p) <<= Meta.disj_commute ((!(p || q) || p) || r);
        ((r || !(p || q)) || p) <<= Rule.associative (r || !(p || q) || p);
        (p || r || !(p || q)) <<= Meta.disj_commute ((r || !(p || q)) || p);
        ((r || !(p || q)) || r) <<= Rule.cut (p || r || !(p || q)) (p => r);
        (r || r || !(p || q)) <<= Meta.disj_commute ((r || !(p || q)) || r);
        ((r || r) || !(p || q)) <<= Rule.associative (r || r || !(p || q));
        (!(p || q) || r || r) <<= Meta.disj_commute ((r || r) || !(p || q));
        (p || q) => r <<= Meta.disj_contraction (!(p || q) || r || r);
      ]
      empty
  in
  let want = (p || q) => r in
  check_conclusion proof got want

let general_expansion _ =
  let x = var "x" in
  let p i = atom (Printf.sprintf "p%d" i) [ x ] in
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
      let proof, got =
        pseq [ disj_of_list a' <<= premise (disj_of_list a'); disj_of_list a <<= Meta.general_expansion a' a ] empty
      in
      let want = disj_of_list a in
      check_conclusion proof got want)
    tests

let substitution_rule _ =
  let x_eq_x = atom "=" [ var "x"; var "x" ] in
  let x_eq_y = atom "=" [ var "x"; var "y" ] in
  let e i = const (Printf.sprintf "e%d" i) in
  let tests = [ (x_eq_x, atom "=" [ e 1; e 1 ]); (x_eq_y, atom "=" [ e 1; e 1 ]); (x_eq_y, atom "=" [ e 2; e 1 ]) ] in
  List.iter
    (fun (a, a') ->
      let proof, got = pseq [ a <<= premise a; a' <<= Meta.substitution_rule a a' ] empty in
      check_conclusion proof got a')
    tests

let e_distribution _ =
  let px = atom "p" [ var "x" ] in
  let qx = atom "q" [ var "x" ] in
  let proof, got =
    pseq
      [ px => qx <<= premise (px => qx); exists "x" px => exists "x" qx <<= Meta.e_distribution "x" (px => qx) ]
      empty
  in
  let want = exists "x" px => exists "x" qx in
  check_conclusion proof got want

let a_distribution _ =
  let px = atom "p" [ var "x" ] in
  let qx = atom "q" [ var "x" ] in
  let proof, got =
    pseq
      [ px => qx <<= premise (px => qx); forall "x" px => forall "x" qx <<= Meta.a_distribution "x" (px => qx) ]
      empty
  in
  let want = forall "x" px => forall "x" qx in
  check_conclusion proof got want

let shoenfield_ch3_5_exists _ =
  let py = atom "p" [ var "y" ] in
  let proof, got =
    pseq
      [
        py <<= premise py;
        py => exists "x" py <<= Axiom.substitution py "x" (var "x");
        py => py <<= Axiom.propositional py;
        exists "x" py => py <<= Rule.e_introduction "x" (py => py);
        py <=> exists "x" py <<= Meta.conj (py => exists "x" py) (exists "x" py => py);
      ]
      empty
  in
  let want = py <=> exists "x" py in
  check_conclusion proof got want

let shoenfield_ch3_6a _ =
  let pxy = atom "p" [ var "x"; var "y" ] in
  let proof, got =
    pseq
      [
        pxy => exists "x" pxy <<= Axiom.substitution pxy "x" (var "x");
        exists "x" pxy => exists "y" (exists "x" pxy) <<= Axiom.substitution (exists "x" pxy) "y" (var "y");
        pxy
        => exists "y" (exists "x" pxy)
        <<= Meta.detachment_transitivity (pxy => exists "x" pxy) (exists "x" pxy => exists "y" (exists "x" pxy));
        exists "y" pxy => exists "y" (exists "x" pxy) <<= Rule.e_introduction "y" (pxy => exists "y" (exists "x" pxy));
        exists "x" (exists "y" pxy)
        => exists "y" (exists "x" pxy)
        <<= Rule.e_introduction "x" (exists "y" pxy => exists "y" (exists "x" pxy));
        pxy => exists "y" pxy <<= Axiom.substitution pxy "y" (var "y");
        exists "y" pxy => exists "x" (exists "y" pxy) <<= Axiom.substitution (exists "y" pxy) "x" (var "x");
        pxy
        => exists "x" (exists "y" pxy)
        <<= Meta.detachment_transitivity (pxy => exists "y" pxy) (exists "y" pxy => exists "x" (exists "y" pxy));
        exists "x" pxy => exists "x" (exists "y" pxy) <<= Rule.e_introduction "x" (pxy => exists "x" (exists "y" pxy));
        exists "y" (exists "x" pxy)
        => exists "x" (exists "y" pxy)
        <<= Rule.e_introduction "y" (exists "x" pxy => exists "x" (exists "y" pxy));
        exists "x" (exists "y" pxy)
        <=> exists "y" (exists "x" pxy)
        <<= Meta.conj
              (exists "x" (exists "y" pxy) => exists "y" (exists "x" pxy))
              (exists "y" (exists "x" pxy) => exists "x" (exists "y" pxy));
      ]
      empty
  in
  let want = exists "x" (exists "y" pxy) <=> exists "y" (exists "x" pxy) in
  check_conclusion proof got want

let shoenfield_ch3_6c _ =
  let pxy = atom "p" [ var "x"; var "y" ] in
  let proof, got =
    pseq
      [
        pxy => exists "x" pxy <<= Axiom.substitution pxy "x" (var "x");
        forall "y" pxy => forall "y" (exists "x" pxy) <<= Meta.a_distribution "y" (pxy => exists "x" pxy);
        exists "x" (forall "y" pxy)
        => forall "y" (exists "x" pxy)
        <<= Rule.e_introduction "x" (forall "y" pxy => forall "y" (exists "x" pxy));
      ]
      empty
  in
  let want = exists "x" (forall "y" pxy) => forall "y" (exists "x" pxy) in
  check_conclusion proof got want

let witness _ =
  let two = const "2" in
  let proof, got = pseq [ exists "x" (atom "=" [ var "x"; two ]) <<= Meta.witness "x" two ] empty in
  let want = exists "x" (atom "=" [ var "x"; two ]) in
  check_conclusion proof got want

let substitution_theorem_e _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let e1 = var "e1" in
  let e2 = var "e2" in
  let e3 = var "e3" in
  let pxyz = atom "p" [ x; y; z ] in
  let pe1e2e3 = atom "p" [ e1; e2; e3 ] in
  let proof, got =
    pseq
      [
        pe1e2e3
        => exists "x" (exists "y" (exists "z" pxyz))
        <<= Meta.substitution_theorem_e pxyz [ ("x", e1); ("y", e2); ("z", e3) ];
      ]
      empty
  in
  let want = pe1e2e3 => exists "x" (exists "y" (exists "z" pxyz)) in
  check_conclusion proof got want

let substitution_theorem_a _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let e1 = var "e1" in
  let e2 = var "e2" in
  let e3 = var "e3" in
  let pxyz = atom "p" [ x; y; z ] in
  let pe1e2e3 = atom "p" [ e1; e2; e3 ] in
  let proof, got =
    pseq
      [
        forall "x" (forall "y" (forall "z" pxyz))
        => pe1e2e3
        <<= Meta.substitution_theorem_a pxyz [ ("x", e1); ("y", e2); ("z", e3) ];
      ]
      empty
  in
  let want = forall "x" (forall "y" (forall "z" pxyz)) => pe1e2e3 in
  check_conclusion proof got want

let equivalence_theorem _ =
  let b = atom "b" [ var "x" ] in
  let b' = atom "b'" [ var "x" ] in
  let a = exists "x" (disj (atom "p" []) b) in
  let a' = exists "x" (disj (atom "p" []) b') in
  let proof, got =
    pseq [ b <=> b' <<= premise (b <=> b'); a <=> a' <<= Meta.equivalence_theorem (a <=> a') (b <=> b') ] empty
  in
  let want = a <=> a' in
  check_conclusion proof got want

let factor_disj_quantifier _ =
  let x = var "x" in
  let p = atom "p" [] in
  let q = atom "q" [] in
  let px = atom "p" [ x ] in
  let qx = atom "q" [ x ] in
  let tests =
    [
      (Meta.factor_disj_left_quantifier_e, exists "x" px || q, (exists "x" px || q) <=> exists "x" (px || q));
      (Meta.factor_disj_right_quantifier_e, p || exists "x" qx, (p || exists "x" qx) <=> exists "x" (p || qx));
      (Meta.factor_disj_left_quantifier_a, forall "x" px || q, (forall "x" px || q) <=> forall "x" (px || q));
      (Meta.factor_disj_right_quantifier_a, p || forall "x" qx, (p || forall "x" qx) <=> forall "x" (p || qx));
    ]
  in
  List.iter
    (fun (inf, a, a') ->
      let proof, got = pseq [ a' <<= inf a ] empty in
      check_conclusion proof got a')
    tests

let pelletier18 _ =
  let x = "x" in
  let y = "y" in
  let fx = atom "F" [ var x ] in
  let fy = atom "F" [ var y ] in
  let proof, got =
    pseq ~scope:"pelletier18"
      [
        forall x fx <=> forall y fy <<= Meta.variant_equivalence_a fx x y;
        forall y fy => forall x fx
        <<= Meta.tautology_theorem [ forall x fx <=> forall y fy ] (forall y fy => forall x fx);
        (exists y !fy || forall x fx)
        <<= Meta.tautology_theorem [ forall y fy => forall x fx ] (exists y !fy || forall x fx);
        (exists y !fy || forall x fx)
        <=> exists y (fy => forall x fx)
        <<= Meta.factor_disj_left_quantifier_e (exists y !fy || forall x fx);
        exists y (fy => forall x fx)
        <<= Meta.tautology_theorem
              [ exists y !fy || forall x fx; (exists y !fy || forall x fx) <=> exists y (fy => forall x fx) ]
              (exists y (fy => forall x fx));
        fy => forall x fx <=> forall x (fy => fx) <<= Meta.factor_disj_right_quantifier_a (fy => forall x fx);
        exists y (fy => forall x fx)
        <=> exists y (forall x (fy => fx))
        <<= Meta.equivalence_theorem
              (exists y (fy => forall x fx) <=> exists y (forall x (fy => fx)))
              (fy => forall x fx <=> forall x (fy => fx));
        exists y (forall x (fy => fx))
        <<= Meta.tautology_theorem
              [ exists y (fy => forall x fx); exists y (fy => forall x fx) <=> exists y (forall x (fy => fx)) ]
              (exists y (forall x (fy => fx)));
      ]
      empty
  in
  let want = exists "y" (forall "x" (fy => fx)) in
  check_conclusion proof got want

let suite =
  "System.Shoenfield"
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
         "detachment" >:: detachment;
         "taut_theorem_case_b" >:: taut_theorem_case_b;
         "taut_theorem_case_c" >:: taut_theorem_case_c;
         "general_expansion" >:: general_expansion;
         "substitution_rule" >:: substitution_rule;
         "e_distribution" >:: e_distribution;
         "a_distribution" >:: a_distribution;
         "shoenfield_ch3_5_exists" >:: shoenfield_ch3_5_exists;
         "shoenfield_ch3_6a" >:: shoenfield_ch3_6a;
         "shoenfield_ch3_6c" >:: shoenfield_ch3_6c;
         "witness" >:: witness;
         "substitution_theorem_e" >:: substitution_theorem_e;
         "substitution_theorem_a" >:: substitution_theorem_a;
         "equivalence_theorem" >:: equivalence_theorem;
         "factor_disj_quantifier" >:: factor_disj_quantifier;
         "pelletier18" >:: pelletier18;
       ]

let () = run_test_tt_main suite
