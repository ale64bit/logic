open Lib.Fol
open OUnit2

let disj_list _ =
  let string_of_formula_list xs =
    Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_formula xs))
  in
  let x = Var "x" in
  let p i = Atom (Printf.sprintf "p%d" i, [ x ]) in
  let tests =
    [
      ([ p 1 ], p 1);
      ([ p 1; p 2 ], Or (p 1, p 2));
      ([ p 1; p 2; p 3 ], Or (p 1, Or (p 2, p 3)));
      ([ p 1; p 2; p 3; p 4 ], Or (p 1, Or (p 2, Or (p 3, p 4))));
    ]
  in
  List.iter
    (fun (xs, a) ->
      assert_equal ~printer:string_of_formula a (disj_of_list xs);
      assert_equal ~printer:string_of_formula_list (list_of_disj a) xs)
    tests

let is_quantifier_free _ =
  let x = Var "x" in
  let a = Atom ("=", [ x; x ]) in
  assert_equal (is_quantifier_free a) true

let variables _ =
  let x = Var "x" in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let a = Or (x_eq_x, Exists ("x", x_eq_x)) in
  assert_equal (variables a) ([ "x" ], [ "x" ])

let closure _ =
  let x = Var "x" in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let a = Or (x_eq_x, x_eq_x) in
  let b = closure a in
  assert_equal ~printer:string_of_formula b (Defined.forall "x" a)

let string_of_formula _ =
  let x = Var "x" in
  let px = Atom ("p", [ x ]) in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let tests =
    [
      (x_eq_x, "(x = x)");
      (px, "p(x)");
      ( Atom ("f", [ Fun ("g", [ Var "x"; Const "e" ]); Var "y" ]),
        "f(g(x, e), y)" );
      (Neg x_eq_x, "¬(x = x)");
      (Neg (Neg x_eq_x), "¬¬(x = x)");
      (Or (px, px), "p(x) ∨ p(x)");
      (Or (px, Or (px, px)), "p(x) ∨ (p(x) ∨ p(x))");
      (Or (Or (px, px), px), "(p(x) ∨ p(x)) ∨ p(x)");
      (Exists ("x", px), "∃x p(x)");
      (Exists ("x", Neg px), "∃x ¬p(x)");
      (Exists ("x", Or (px, px)), "∃x (p(x) ∨ p(x))");
      (Or (Exists ("x", px), px), "∃x p(x) ∨ p(x)");
      (Or (x_eq_x, Neg (Neg x_eq_x)), "(x = x) ∨ ¬¬(x = x)");
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = string_of_formula a in
      assert_equal ~printer:Fun.id want got)
    tests

let suite =
  "FolTests"
  >::: [
         "is_quantifier_free" >:: is_quantifier_free;
         "variables" >:: variables;
         "closure" >:: closure;
         "disj_list" >:: disj_list;
         "string_of_formula" >:: string_of_formula;
       ]

let () = run_test_tt_main suite
