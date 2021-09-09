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

let is_open _ =
  let x = Var "x" in
  let a = Atom ("=", [ x; x ]) in
  assert_equal (is_open a) true

let variables _ =
  let x = Var "x" in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let a = Or (x_eq_x, Exists ("x", x_eq_x)) in
  assert_equal (variables a) ([ "x" ], [ "x" ])

let closure _ =
  let x = Var "x" in
  let y = Var "y" in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let y_eq_x = Atom ("=", [ y; x ]) in
  let tests =
    [
      (Or (x_eq_x, x_eq_x), Defined.forall "x" (Or (x_eq_x, x_eq_x)));
      ( Or (y_eq_x, y_eq_x),
        Defined.forall "x" (Defined.forall "y" (Or (y_eq_x, y_eq_x))) );
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = closure a in
      assert_equal ~printer:string_of_formula want got)
    tests

let is_instance _ =
  let x = Var "x" in
  let y = Var "y" in
  let e = Const "e" in
  let x_eq_x = Atom ("=", [ x; x ]) in
  let x_eq_y = Atom ("=", [ x; y ]) in
  let e_eq_e = Atom ("=", [ e; e ]) in
  let fxy = Fun ("f", [ x; y ]) in
  let tests =
    [
      (x_eq_x, x_eq_x, ([], true));
      (e_eq_e, x_eq_x, ([ ("x", e) ], true));
      (Atom ("=", [ x; e ]), x_eq_x, ([], false));
      (Atom ("=", [ e; x ]), x_eq_x, ([], false));
      (e_eq_e, x_eq_y, ([ ("x", e); ("y", e) ], true));
      (Atom ("=", [ fxy; y ]), x_eq_y, ([ ("x", fxy) ], true));
      (Atom ("=", [ x; fxy ]), x_eq_y, ([ ("y", fxy) ], true));
    ]
  in
  let printer (m, res) =
    Printf.sprintf "([%s], %B)"
      (String.concat ", "
         (List.map
            (fun (x, t) -> Printf.sprintf "%s -> %s" x (string_of_term t))
            m))
      res
  in
  List.iter
    (fun (a', a, want) -> assert_equal ~printer want (is_instance a' a))
    tests

let substitute _ =
  let x = Var "x" in
  let y = Var "y" in
  let z = Var "z" in
  let tests =
    [
      ( Exists ("y", Atom ("=", [ x; Fun ("*", [ Const "2"; y ]) ])),
        "x",
        Fun ("+", [ z; Const "1" ]),
        Exists
          ( "y",
            Atom
              ("=", [ Fun ("+", [ z; Const "1" ]); Fun ("*", [ Const "2"; y ]) ])
          ) );
    ]
  in
  List.iter
    (fun (a, x, t, want) ->
      let got = substitute a x t in
      assert_equal ~printer:string_of_formula want got)
    tests

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
         "is_open" >:: is_open;
         "variables" >:: variables;
         "closure" >:: closure;
         "disj_list" >:: disj_list;
         "string_of_formula" >:: string_of_formula;
         "is_instance" >:: is_instance;
         "substitute" >:: substitute;
       ]

let () = run_test_tt_main suite
