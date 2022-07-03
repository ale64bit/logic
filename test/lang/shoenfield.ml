module L = Lang.Shoenfield.S
open L
open Lang.Shoenfield.Syntax (L)
open OUnit2

let disj_list _ =
  let string_of_formula_list xs = Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_formula xs)) in
  let x = var "x" in
  let p i = atom (Printf.sprintf "p%d" i) [ x ] in
  let tests =
    [
      ([ p 1 ], p 1);
      ([ p 1; p 2 ], disj (p 1) (p 2));
      ([ p 1; p 2; p 3 ], disj (p 1) (disj (p 2) (p 3)));
      ([ p 1; p 2; p 3; p 4 ], disj (p 1) (disj (p 2) (disj (p 3) (p 4))));
    ]
  in
  List.iter
    (fun (xs, a) ->
      assert_equal ~printer:string_of_formula a (disj_of_list xs);
      assert_equal ~printer:string_of_formula_list (list_of_disj a) xs)
    tests

let is_open _ =
  let x = var "x" in
  let a = atom "=" [ x; x ] in
  assert_equal (is_open a) true

let height _ =
  let x = var "x" in
  let a = atom "=" [ x; x ] in
  let tests = [ (a, 0); (neg a, 1); (disj a a, 1); (exists "x" a, 1); (neg (exists "x" (disj a a)), 3) ] in
  List.iter
    (fun (a, want) ->
      let got = height a in
      assert_equal ~printer:string_of_int want got)
    tests

let variable_occurrences _ =
  let x = var "x" in
  let x_eq_x = atom "=" [ x; x ] in
  let a = disj x_eq_x (exists "x" x_eq_x) in
  assert_equal (variable_occurrences a) ([ "x" ], [ "x" ])

let closure _ =
  let x = var "x" in
  let y = var "y" in
  let x_eq_x = atom "=" [ x; x ] in
  let y_eq_x = atom "=" [ y; x ] in
  let tests =
    [
      (disj x_eq_x x_eq_x, forall "x" (disj x_eq_x x_eq_x));
      (disj y_eq_x y_eq_x, forall "x" (forall "y" (disj y_eq_x y_eq_x)));
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = closure a in
      assert_equal ~printer:string_of_formula want got)
    tests

let is_instance _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let e = const "e" in
  let e1 = const "e1" in
  let e2 = const "e2" in
  let e3 = const "e3" in
  let x_eq_x = atom "=" [ x; x ] in
  let x_eq_y = atom "=" [ x; y ] in
  let e_eq_e = atom "=" [ e; e ] in
  let fxy = func "f" [ x; y ] in
  let px = atom "p" [ x ] in
  let pe = atom "p" [ e ] in
  let pxyz = atom "p" [ x; y; z ] in
  let pe1e2e3 = atom "p" [ e1; e2; e3 ] in
  let tests =
    [
      (x_eq_x, x_eq_x, Some []);
      (e_eq_e, x_eq_x, Some [ ("x", e) ]);
      (atom "=" [ x; e ], x_eq_x, None);
      (atom "=" [ e; x ], x_eq_x, None);
      (e_eq_e, x_eq_y, Some [ ("x", e); ("y", e) ]);
      (atom "=" [ fxy; y ], x_eq_y, Some [ ("x", fxy) ]);
      (atom "=" [ x; fxy ], x_eq_y, Some [ ("y", fxy) ]);
      (pe, px, Some [ ("x", e) ]);
      (impl pe (exists "x" px), impl px (exists "x" px), Some [ ("x", e) ]);
      ( impl pe1e2e3 (exists "x" (exists "y" (exists "z" pxyz))),
        impl pxyz (exists "x" (exists "y" (exists "z" pxyz))),
        Some [ ("x", e1); ("y", e2); ("z", e3) ] );
    ]
  in
  let printer = function
    | Some m ->
        Printf.sprintf "Some [%s]"
          (String.concat ", " (List.map (fun (x, t) -> Printf.sprintf "%s -> %s" x (string_of_term t)) m))
    | None -> "None"
  in
  List.iter (fun (a', a, want) -> assert_equal ~printer want (is_instance a' a)) tests

let substitute _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let tests =
    [
      ( exists "y" (atom "=" [ x; func "*" [ const "2"; y ] ]),
        [ ("x", func "+" [ z; const "1" ]) ],
        exists "y" (atom "=" [ func "+" [ z; const "1" ]; func "*" [ const "2"; y ] ]) );
      (atom "p" [ x; y ], [ ("x", y); ("y", x) ], atom "p" [ y; x ]);
    ]
  in
  List.iter
    (fun (a, s, want) ->
      let got = substitute a s in
      assert_equal ~printer:string_of_formula want got)
    tests

let variant _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let x_eq_z = atom "=" [ x; z ] in
  let y_eq_z = atom "=" [ y; z ] in
  let tests =
    [
      (exists "x" x_eq_z, "x", "y", exists "y" y_eq_z);
      (exists "x" x_eq_z, "y", "z", exists "x" x_eq_z);
      (disj x_eq_z (exists "x" x_eq_z), "x", "y", disj x_eq_z (exists "y" y_eq_z));
    ]
  in
  List.iter
    (fun (a, x, y, want) ->
      let got = variant a x y in
      assert_equal ~printer:string_of_formula want got)
    tests

let prenex _ =
  let x = var "x" in
  let y = var "y" in
  let x' = var "x'" in
  let y' = var "y'" in
  let x_eq_y = atom "=" [ x; y ] in
  let x_eq_0 = atom "=" [ x; const "0" ] in
  let tests =
    [
      (x_eq_y, x_eq_y);
      (exists "x" x_eq_y, exists "x" x_eq_y);
      (forall "x" x_eq_y, forall "x" x_eq_y);
      ( impl (exists "x" x_eq_y)
          (exists "x" (disj (atom "=" [ x; const "0" ]) (neg (exists "y" (atom "<" [ y; const "0" ]))))),
        forall "x'"
          (exists "x" (forall "y'" (impl (atom "=" [ x'; y ]) (disj x_eq_0 (neg (atom "<" [ y'; const "0" ])))))) );
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = prenex a in
      assert_equal ~printer:string_of_formula want got)
    tests

let is_tautology _ =
  let x = var "x" in
  let px = atom "p" [ x ] in
  let qx = atom "q" [ x ] in
  let rx = atom "r" [ x ] in
  let x_eq_x = atom "=" [ x; x ] in
  let tests = [ (disj px (neg px), true); (x_eq_x, false); (impl (impl px rx) (impl (neg (impl px qx)) rx), true) ] in
  List.iter
    (fun (a, want) ->
      let got = is_tautology a in
      assert_equal ~printer:string_of_bool want got)
    tests

let is_tautological_consequence _ =
  let x = var "x" in
  let px = atom "p" [ x ] in
  let qx = atom "q" [ x ] in
  let tests = [ (conj px (neg px), qx, true); (disj px (neg px), qx, false) ] in
  List.iter
    (fun (b, a, want) ->
      let got = is_tautological_consequence [ b ] a in
      assert_equal ~printer:string_of_bool want got)
    tests

let herbrandize _ =
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in
  let px = atom "p" [ x ] in
  let tests =
    [
      (px, atom "p" [ const "f0" ]);
      (exists "x" px, exists "x" px);
      ( exists "x" (forall "y" (exists "z" (atom "p" [ x; y; z ]))),
        exists "x" (exists "z" (atom "p" [ x; func "f0" [ x ]; z ])) );
      (atom "p" [ x; y; z ], atom "p" [ const "f0"; const "f1"; const "f2" ]);
      ( exists "x1" (forall "x2" (exists "x3" (forall "x4" (atom "p" [ var "x1"; var "x2"; var "x3"; var "x4" ])))),
        exists "x1"
          (exists "x3" (atom "p" [ var "x1"; func "f0" [ var "x1" ]; var "x3"; func "f1" [ var "x1"; var "x3" ] ])) );
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = herbrandize a in
      assert_equal ~printer:string_of_formula want got)
    tests

let string_of_formula _ =
  let x = var "x" in
  let px = atom "p" [ x ] in
  let x_eq_x = atom "=" [ x; x ] in
  let tests =
    [
      (x_eq_x, "(x = x)");
      (px, "p(x)");
      (atom "f" [ func "g" [ var "x"; const "e" ]; var "y" ], "f(g(x, e), y)");
      (neg x_eq_x, "¬(x = x)");
      (neg (neg x_eq_x), "¬¬(x = x)");
      (disj px px, "p(x) ∨ p(x)");
      (disj px (disj px px), "p(x) ∨ (p(x) ∨ p(x))");
      (disj (disj px px) px, "(p(x) ∨ p(x)) ∨ p(x)");
      (exists "x" px, "∃x p(x)");
      (exists "x" (neg px), "∃x ¬p(x)");
      (exists "x" (disj px px), "∃x (p(x) ∨ p(x))");
      (disj (exists "x" px) px, "∃x p(x) ∨ p(x)");
      (disj x_eq_x (neg (neg x_eq_x)), "(x = x) ∨ ¬¬(x = x)");
    ]
  in
  List.iter
    (fun (a, want) ->
      let got = string_of_formula a in
      assert_equal ~printer:Fun.id want got)
    tests

let extended_string_of_formula _ =
  let x = var "x" in
  let px = atom "p" [ x ] in
  let qx = atom "q" [ x ] in
  let tests =
    [ (impl px qx, "p(x) → q(x)"); (eq px qx, "p(x) ↔ q(x)"); (conj px qx, "p(x) ∧ q(x)"); (forall "x" px, "∀x p(x)") ]
  in
  List.iter
    (fun (a, want) ->
      let got = extended_string_of_formula a in
      assert_equal ~printer:Fun.id want got)
    tests

let suite =
  "Lang.Shoenfield"
  >::: [
         "is_open" >:: is_open;
         "height" >:: height;
         "variable_occurrences" >:: variable_occurrences;
         "closure" >:: closure;
         "disj_list" >:: disj_list;
         "is_instance" >:: is_instance;
         "substitute" >:: substitute;
         "variant" >:: variant;
         "prenex" >:: prenex;
         "is_tautology" >:: is_tautology;
         "is_tautological_consequence" >:: is_tautological_consequence;
         "herbrandize" >:: herbrandize;
         "string_of_formula" >:: string_of_formula;
         "extended_string_of_formula" >:: extended_string_of_formula;
       ]

let () = run_test_tt_main suite
