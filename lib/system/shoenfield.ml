module Common = struct
  open Lang.Shoenfield.S
  open Lang.Shoenfield.Syntax (Lang.Shoenfield.S)

  type formula = Lang.Shoenfield.S.formula
  type proof_line = { index : int; refs : int list; reason : string }
  type proof = proof_line FormulaMap.t
  type conclusion = proof * formula

  let empty = FormulaMap.empty
  let already_proven ctx a = FormulaMap.mem a ctx

  let add a premises reason ctx =
    let () =
      if not (List.for_all (already_proven ctx) premises) then (
        let missing = List.filter (fun a -> not (already_proven ctx a)) premises in
        Printf.printf "FATAL: missing premise(s):\n\tinference: %s\n\tconclusion: %s\n\tmissing: [%s]\n%!" reason
          (extended_string_of_formula a)
          (String.concat "; " (List.map extended_string_of_formula missing));
        failwith "missing premise")
    in
    if already_proven ctx a then (ctx, a)
    else
      let l =
        {
          index = 1 + FormulaMap.cardinal ctx;
          refs = List.map (fun a -> (FormulaMap.find a ctx).index) premises;
          reason;
        }
      in
      (ctx |> FormulaMap.add a l, a)

  let premise a = add a [] "premise"

  let export_internal system (ctx, formula) =
    assert (FormulaMap.cardinal ctx > 0);
    let module IntSet = Set.Make (Int) in
    let root = (FormulaMap.find formula ctx).index in
    let fs = List.sort (fun (_, { index = i; _ }) (_, { index = j; _ }) -> j - i) (FormulaMap.bindings ctx) in
    let _, lines =
      List.fold_left
        (fun (needed, acc) (a, { index; refs; reason }) ->
          if IntSet.mem index needed then
            let line =
              Core.SZS.
                {
                  index;
                  formula = extended_string_of_formula a;
                  name = None;
                  premises = refs;
                  inference = reason;
                  message = None;
                }
            in
            (IntSet.add_seq (List.to_seq refs) needed, line :: acc)
          else (needed, acc))
        (IntSet.singleton root, [])
        fs
    in
    Core.SZS.(Success Theorem, Proof { system; lines })

  let ( <<= ) a inf = (a, inf)

  let pseq ?(scope = "-") steps ctx =
    assert (List.length steps > 0);
    let rec aux i steps (ctx, conclusion) =
      match steps with
      | [] -> (ctx, conclusion)
      | (want, inf) :: tl -> (
          try
            let ctx, got = inf ctx in
            if want <> got then
              failwith
                (Printf.sprintf "unexpected conclusion: scope=%s got=%s want=%s" scope (string_of_formula conclusion)
                   (string_of_formula want))
            else aux (i + 1) tl (ctx, got)
          with e ->
            let () = Printf.printf "proof step %d failure in scope: %s\n" i scope in
            raise e)
    in
    aux 0 steps (ctx, atom "IMPOSSIBLE" [])
end

module Base = struct
  include Common
  open Lang.Shoenfield.S
  open Lang.Shoenfield.Syntax (Lang.Shoenfield.S)
  open Util

  let export = export_internal "Shoenfield.Base"

  module Axiom = struct
    let propositional a = add (disj (neg a) a) [] "propositional axiom"
    let substitution a x t = add (impl (substitute a [ (x, t) ]) (exists x a)) [] "substitution axiom"
    let identity x = add (atom "=" [ var x; var x ]) [] "identity axiom"

    let fequality xys f =
      let xs, ys = List.split xys in
      let fx = func f (List.map var xs) in
      let fy = func f (List.map var ys) in
      add
        (List.fold_left (fun acc (x, y) -> impl (atom "=" [ var x; var y ]) acc) (atom "=" [ fx; fy ]) (List.rev xys))
        [] "equality axiom"

    let pequality xys p =
      let xs, ys = List.split xys in
      let px = atom p (List.map var xs) in
      let py = atom p (List.map var ys) in
      add
        (List.fold_left (fun acc (x, y) -> impl (atom "=" [ Var x; Var y ]) acc) (impl px py) (List.rev xys))
        [] "equality axiom"
  end

  module Rule = struct
    open Lang.Shoenfield.Repr

    let expansion b a = add (disj b a) [ a ] "expansion rule"

    let contraction = function
      | Disj (b, b') as a when b = b' -> add b [ a ] "contraction rule"
      | a -> failwith (Printf.sprintf "invalid contraction: %s" (string_of_formula a))

    let associative = function
      | Disj (a', Disj (b', c')) as a -> add (Disj (Disj (a', b'), c')) [ a ] "associative rule"
      | a -> failwith (Printf.sprintf "invalid association: %s" (string_of_formula a))

    let cut b c =
      match (b, c) with
      | Disj (a, b'), Disj (Neg a', c') when a = a' -> add (Disj (b', c')) [ b; c ] "cut rule"
      | _ -> failwith (Printf.sprintf "invalid cut: (%s) and (%s)" (string_of_formula b) (string_of_formula c))

    let e_introduction x a =
      match a with
      | Disj (Neg a', b') when not (is_free x b') -> add (impl (Exists (x, a')) b') [ a ] "∃-introduction rule"
      | _ -> failwith (Printf.sprintf "invalid ∃-introduction: %s and %s" x (string_of_formula a))
  end

  module Meta = struct
    open Lang.Shoenfield.Repr
    open Lang.OperatorSyntax.Make (Lang.Shoenfield.S)

    let disj_commute = function
      | Disj (a, b) ->
          pseq ~scope:"disj_commute" [ (!a || a) <<= Axiom.propositional a; (b || a) <<= Rule.cut (a || b) (!a || a) ]
      | a -> failwith (Printf.sprintf "invalid disj_commute: %s" (string_of_formula a))

    let detachment a a_to_b =
      match a_to_b with
      | Disj (Neg a', b) when a = a' ->
          pseq ~scope:"detachment"
            [
              (b || a) <<= Rule.expansion b a;
              (a || b) <<= disj_commute (b || a);
              (b || b) <<= Rule.cut (a || b) (a => b);
              b <<= Rule.contraction (b || b);
            ]
      | a -> failwith (Printf.sprintf "invalid detachment: %s and %s" (string_of_formula a) (string_of_formula a_to_b))

    let conj a b =
      pseq ~scope:"conj"
        [
          ((a && b) || !a || !b) <<= Axiom.propositional (!a || !b);
          (((a && b) || !a) || !b) <<= Rule.associative ((a && b) || !a || !b);
          b => ((a && b) || !a) <<= disj_commute (((a && b) || !a) || !b);
          ((a && b) || !a) <<= detachment b (b => ((a && b) || !a));
          a => (a && b) <<= disj_commute ((a && b) || !a);
          (a && b) <<= detachment a (a => (a && b));
        ]

    let dneg_introduction a =
      pseq ~scope:"dneg_introduction"
        [
          (!(!a) || a) <<= Rule.expansion !(!a) a;
          (!(!(!a)) || !(!a)) <<= Axiom.propositional !(!a);
          (a || !(!a)) <<= Rule.cut (!(!a) || a) (!(!(!a)) || !(!a));
          (!(!a) || !a) <<= Axiom.propositional !a;
          (!a || !(!a)) <<= Rule.cut (!(!a) || !a) (!(!(!a)) || !(!a));
          (!(!a) || !(!a)) <<= Rule.cut (a || !(!a)) (!a || !(!a));
          !(!a) <<= Rule.contraction (!(!a) || !(!a));
        ]

    let dneg_elimination = function
      | Neg (Neg a) ->
          pseq ~scope:"dneg_elimination"
            [
              (!(!(!a)) || !(!a)) <<= Axiom.propositional !(!a);
              (!a || a) <<= Axiom.propositional a;
              (!(!a) || !(!(!a))) <<= disj_commute (!(!(!a)) || !(!a));
              (a || !(!(!a))) <<= Rule.cut (!a || a) (!(!a) || !(!(!a)));
              !(!a) => a <<= disj_commute (a || !(!(!a)));
              a <<= detachment !(!a) (!(!a) => a);
            ]
      | a -> failwith (Printf.sprintf "invalid double-negation elimination: %s" (string_of_formula a))

    let disj_dneg = function
      | Disj (a, b) ->
          pseq ~scope:"disj_dneg"
            [
              (!(!a) || !a) <<= Axiom.propositional !a;
              (!a || !(!a)) <<= disj_commute (!(!a) || !a);
              (b || !(!a)) <<= Rule.cut (a || b) (!a || !(!a));
              (!(!a) || b) <<= disj_commute (b || !(!a));
            ]
      | a -> failwith (Printf.sprintf "invalid disjuction neg neg: %s" (string_of_formula a))

    let disj_contraction = function
      | Disj (a, Disj (b, b')) when b = b' ->
          pseq ~scope:"disj_contraction"
            [
              ((a || b) || b) <<= Rule.associative (a || b || b);
              (b || a || b) <<= disj_commute ((a || b) || b);
              (a || b || a || b) <<= Rule.expansion a (b || a || b);
              ((a || b) || a || b) <<= Rule.associative (a || b || a || b);
              (a || b) <<= Rule.contraction ((a || b) || a || b);
            ]
      | a -> failwith (Printf.sprintf "invalid disj_contraction: %s" (string_of_formula a))

    let associative_right = function
      | Disj (Disj (a, b), c) ->
          pseq ~scope:"associative_right"
            [
              (c || a || b) <<= disj_commute ((a || b) || c);
              ((c || a) || b) <<= Rule.associative (c || a || b);
              (b || c || a) <<= disj_commute ((c || a) || b);
              ((b || c) || a) <<= Rule.associative (b || c || a);
              (a || b || c) <<= disj_commute ((b || c) || a);
            ]
      | a -> failwith (Printf.sprintf "invalid right association: %s" (string_of_formula a))

    (* ¬A ∨ C, ¬B ∨ C ⊢ ¬(A ∨ B) ∨ C *)
    let taut_theorem_result_c f g =
      match (f, g) with
      | Disj (Neg a, c), Disj (Neg b, c') when c = c' ->
          pseq ~scope:"taut_theorem_result_c"
            [
              (!(a || b) || a || b) <<= Axiom.propositional (a || b);
              ((!(a || b) || a) || b) <<= Rule.associative (!(a || b) || a || b);
              (b || !(a || b) || a) <<= disj_commute ((!(a || b) || a) || b);
              ((!(a || b) || a) || c) <<= Rule.cut (b || !(a || b) || a) (!b || c);
              (c || !(a || b) || a) <<= disj_commute ((!(a || b) || a) || c);
              ((c || !(a || b)) || a) <<= Rule.associative (c || !(a || b) || a);
              (a || c || !(a || b)) <<= disj_commute ((c || !(a || b)) || a);
              ((c || !(a || b)) || c) <<= Rule.cut (a || c || !(a || b)) (!a || c);
              (c || c || !(a || b)) <<= disj_commute ((c || !(a || b)) || c);
              ((c || c) || !(a || b)) <<= Rule.associative (c || c || !(a || b));
              (!(a || b) || c || c) <<= disj_commute ((c || c) || !(a || b));
              (!(a || b) || c) <<= disj_contraction (!(a || b) || c || c);
            ]
      | a, b ->
          failwith
            (Printf.sprintf "invalid taut_theorem_result_c: %s and %s" (string_of_formula a) (string_of_formula b))

    (*
      If {Ai1, ... , Aim} is a subset of {A1, ... , An}, constructs a proof of ⊢ (Ai1 ∨ ... ∨ Aim) → (A1 ∨ ... ∨ An).

      In the base case of m=1, it first expands Ai1 to (A1 ∨ ( A2 ∨ ... ) ) ∨ Ai1 and then commutes and expands the rest of the terms.

      In the general case, it first proves ⊢ Aij → (A1 ∨ ... ∨ An) for 1 <= j <= m and then combines the results using
      case (C) of the tautology theorem, as presented in Shoenfield's "Mathematical Logic".
    *)
    let rec general_expansion_implication a' a ctx =
      assert (List.length a' > 0);
      if ListUtil.is_subset a' a then
        match List.rev a' with
        | [ ai ] ->
            let left, right = ListUtil.split_at ai a in
            let ctx, s1 =
              pseq ~scope:"general_expansion_implication: case [A]"
                (if right = [] then [ (!ai || ai) <<= Axiom.propositional ai; (ai || !ai) <<= disj_commute (!ai || ai) ]
                else
                  let b = disj_of_list right in
                  [
                    (!ai || ai) <<= Axiom.propositional ai;
                    (b || !ai || ai) <<= Rule.expansion b (!ai || ai);
                    ((b || !ai) || ai) <<= Rule.associative (b || !ai || ai);
                    (ai || b || !ai) <<= disj_commute ((b || !ai) || ai);
                    ((ai || b) || !ai) <<= Rule.associative (ai || b || !ai);
                  ])
                ctx
            in
            let ctx, s2 =
              List.fold_left
                (fun (ctx, b) ai ->
                  let ctx, _ = Rule.expansion ai b ctx in
                  Rule.associative (ai || b) ctx)
                (ctx, s1) (List.rev left)
            in
            pseq [ disj_of_list (!ai :: a) <<= disj_commute s2 ] ctx
        | am :: a'' ->
            let ctx, sm = general_expansion_implication [ am ] a ctx in
            List.fold_left
              (fun (ctx, b) ai ->
                let ctx, s1 = general_expansion_implication [ ai ] a ctx in
                taut_theorem_result_c s1 b ctx)
              (ctx, sm) a''
        | [] -> failwith "impossible general expansion implication"
      else
        failwith
          (Printf.sprintf "invalid general expansion implication: [%s] -> [%s]"
             (String.concat ", " (List.map string_of_formula a'))
             (String.concat ", " (List.map string_of_formula a)))

    let general_expansion a' a =
      if ListUtil.is_subset a' a then
        let b' = disj_of_list a' in
        let b = disj_of_list a in
        pseq ~scope:"general_expansion"
          [ b' => b <<= general_expansion_implication a' a; b <<= detachment b' (b' => b) ]
      else
        failwith
          (Printf.sprintf "invalid general expansion: [%s] -> [%s]"
             (String.concat ", " (List.map string_of_formula a'))
             (String.concat ", " (List.map string_of_formula a)))

    let tautology_theorem fs a ctx =
      let () = assert (is_tautological_consequence fs a) in
      (* Find complementary literals A and ¬A *)
      let find_compl pos neg = List.find_opt (fun a -> List.exists (fun b -> Neg a = b) neg) pos in
      let rec prove a =
        let bs = list_of_disj a in
        let pos, neg = List.partition (function Neg _ -> false | _ -> true) bs in
        let all_elementary = List.for_all (function Neg a -> is_elementary a | a -> is_elementary a) bs in
        if all_elementary then prove_elementary bs pos neg else prove_non_elementary a
      and prove_elementary bs pos neg =
        match find_compl pos neg with
        | Some a when ListUtil.is_sublist [ !a; a ] bs ->
            pseq ~scope:"prove_elementary: case [¬A; A] subseq of B"
              [ (!a || a) <<= Axiom.propositional a; disj_of_list bs <<= general_expansion [ !a; a ] bs ]
        | Some a ->
            pseq ~scope:"prove_elementary: case [A; ¬A] subseq of B"
              [
                (!a || a) <<= Axiom.propositional a;
                (a || !a) <<= disj_commute (!a || a);
                disj_of_list bs <<= general_expansion [ a; !a ] bs;
              ]
        | None -> failwith "BAD STUFF: can't prove elementary disjunction: not a tautological consequence?"
      and prove_non_elementary a =
        match list_of_disj a with
        | Disj (b, c) :: a' ->
            let d = disj_of_list (b :: c :: a') in
            pseq ~scope:"prove_non_elementary: case (B∨C) ∨ A1 ∨ ... ∨ An" [ d <<= prove d; a <<= Rule.associative d ]
        | [ Neg (Neg b) ] ->
            pseq ~scope:"prove_non_elementary: case ¬¬B" [ b <<= prove b; !(!b) <<= dneg_introduction b ]
        | Neg (Neg b) :: a' ->
            let c = disj_of_list (b :: a') in
            pseq ~scope:"prove_non_elementary: case ¬¬B ∨ A1 ∨ ... ∨ An" [ c <<= prove c; a <<= disj_dneg c ]
        | [ Neg (Disj (b, c)) ] ->
            pseq ~scope:"prove_non_elementary: case ¬(B∨C)"
              [
                !b <<= prove !b;
                !c <<= prove !c;
                (!(b || c) || b || c) <<= Axiom.propositional (b || c);
                ((!(b || c) || b) || c) <<= Rule.associative (!(b || c) || b || c);
                (c || !(b || c) || b) <<= disj_commute ((!(b || c) || b) || c);
                (!(!c) || !(b || c) || b) <<= disj_dneg (c || !(b || c) || b);
                (!(b || c) || b) <<= detachment !c (!c => (!(b || c) || b));
                (b || !(b || c)) <<= disj_commute (!(b || c) || b);
                (!(!b) || !(b || c)) <<= disj_dneg (b || !(b || c));
                !(b || c) <<= detachment !b (!b => !(b || c));
              ]
        | Neg (Disj (b, c)) :: a' ->
            let disj_a' = disj_of_list a' in
            let negb_a' = disj_of_list (!b :: a') in
            let negc_a' = disj_of_list (!c :: a') in
            pseq ~scope:"prove_non_elementary: case ¬(B∨C) ∨ A1 ∨ ... ∨ An"
              [
                negb_a' <<= prove negb_a';
                negc_a' <<= prove negc_a';
                (!(b || c) || b || c) <<= Axiom.propositional (b || c);
                ((!(b || c) || b) || c) <<= Rule.associative (!(b || c) || b || c);
                (c || !(b || c) || b) <<= disj_commute ((!(b || c) || b) || c);
                disj_of_list ((!(b || c) || b) :: a') <<= Rule.cut (c || !(b || c) || b) negc_a';
                (disj_a' || !(b || c) || b) <<= disj_commute (disj_of_list ((!(b || c) || b) :: a'));
                ((disj_a' || !(b || c)) || b) <<= Rule.associative (disj_a' || !(b || c) || b);
                (b || disj_a' || !(b || c)) <<= disj_commute ((disj_a' || !(b || c)) || b);
                ((disj_a' || !(b || c)) || disj_a') <<= Rule.cut (b || disj_a' || !(b || c)) negb_a';
                (disj_a' || disj_a' || !(b || c)) <<= disj_commute ((disj_a' || !(b || c)) || disj_a');
                ((disj_a' || disj_a') || !(b || c)) <<= Rule.associative (disj_a' || disj_a' || !(b || c));
                (!(b || c) || disj_a' || disj_a') <<= disj_commute ((disj_a' || disj_a') || !(b || c));
                a <<= disj_contraction (!(b || c) || disj_a' || disj_a');
              ]
        | [ b; c ] ->
            pseq ~scope:"prove_non_elementary: case B ∨ C"
              [ (c || b) <<= prove_non_elementary (c || b); a <<= disj_commute (c || b) ]
        | b :: bs ->
            let b' = disj_of_list (bs @ [ b ]) in
            pseq ~scope:"prove_non_elementary: case B ∨ A1 ∨ ... ∨ An"
              [ b' <<= prove_non_elementary b'; a <<= general_expansion (bs @ [ b ]) (b :: bs) ]
        | _ -> failwith (Printf.sprintf "invalid prove_non_elementary: %s" (string_of_formula a))
      in
      let fs_to_a = impl_of_list (fs @ [ a ]) in
      let ctx, _ = prove fs_to_a ctx in
      (* Use detachment to eliminate the premises from the implication and obtain the conjecture *)
      List.fold_left (fun (ctx, conclusion) fi -> detachment fi conclusion ctx) (ctx, fs_to_a) fs

    let contrapositive = function
      | Disj (Neg a, b) ->
          pseq ~scope:"contrapositive" [ (b || !a) <<= disj_commute (a => b); !b => !a <<= disj_dneg (b || !a) ]
      | a -> failwith (Printf.sprintf "invalid reverse implication: %s" (string_of_formula a))

    let a_introduction x = function
      | Disj (Neg a, b) when not (is_free x a) ->
          pseq ~scope:"a_introduction"
            [
              !b => !a <<= contrapositive (a => b);
              exists x !b => !a <<= Rule.e_introduction x (!b => !a);
              a => forall x b <<= disj_commute (exists x !b => !a);
            ]
      | a -> failwith (Printf.sprintf "invalid ∀-introduction: %s %s" x (string_of_formula a))

    let generalization x a =
      pseq ~scope:"generalization"
        [
          !(forall x a) => a <<= Rule.expansion !(!(forall x a)) a;
          !(forall x a) => forall x a <<= a_introduction x (!(forall x a) => a);
          (!(!(forall x a)) || !(!(forall x a))) <<= contrapositive (!(forall x a) => forall x a);
          !(!(forall x a)) <<= Rule.contraction (!(!(forall x a)) || !(!(forall x a)));
          forall x a <<= dneg_elimination !(!(forall x a));
        ]

    let rec substitution_rule a a' ctx =
      match is_instance a' a with
      | Some [] ->
          assert (a = a');
          (ctx, a')
      | Some [ (x, t) ] ->
          pseq ~scope:"substitution"
            [
              forall x a <<= generalization x a;
              substitute !a [ (x, t) ] => exists x !a <<= Axiom.substitution !a x t;
              forall x a => !(substitute !a [ (x, t) ]) <<= contrapositive (substitute !a [ (x, t) ] => exists x !a);
              !(substitute !a [ (x, t) ]) <<= detachment (forall x a) (forall x a => !(substitute !a [ (x, t) ]));
              a' <<= dneg_elimination !(substitute !a [ (x, t) ]);
            ]
            ctx
      | Some m ->
          let xs, ts = List.split m in
          (* The intermediate variables [ys] are needed since the terms can
             contain some of the free variables *)
          let ys = gen_fresh_vars (List.length m) [ a; a' ] in
          (* First pass: substitute xi with yi *)
          let ctx, s1 =
            List.fold_left
              (fun (ctx, ai) (xi, yi) -> substitution_rule ai (substitute ai [ (xi, var yi) ]) ctx)
              (ctx, a) (List.combine xs ys)
          in
          (* Second pass: substitute the yi introduced in first pass with ti *)
          let ctx, s2 =
            List.fold_left
              (fun (ctx, ai) (yi, ti) -> substitution_rule ai (substitute ai [ (yi, ti) ]) ctx)
              (ctx, s1) (List.combine ys ts)
          in
          (ctx, s2)
      | None ->
          failwith
            (Printf.sprintf "invalid substitution rule: %s is not an instance of %s" (string_of_formula a')
               (string_of_formula a))

    let detachment_transitivity f g =
      match (f, g) with
      | Disj (Neg a, b), Disj (Neg b', c) when b = b' ->
          pseq ~scope:"detachment_transitivity"
            [ (b || !a) <<= disj_commute (a => b); a => c <<= Rule.cut (b || !a) (b => c) ]
      | _ ->
          failwith
            (Printf.sprintf "invalid detachment transitivity: %s and %s" (string_of_formula f) (string_of_formula g))

    let e_distribution x = function
      | Disj (Neg a, b) ->
          pseq ~scope:"e_distribution"
            [
              b => exists x b <<= Axiom.substitution b x (var x);
              a => exists x b <<= detachment_transitivity (a => b) (b => exists x b);
              exists x a => exists x b <<= Rule.e_introduction x (a => exists x b);
            ]
      | a -> failwith (Printf.sprintf "invalid ∃-distribution: %s" (string_of_formula a))

    let a_distribution x = function
      | Disj (Neg a, b) ->
          pseq ~scope:"a_distribution"
            [
              !(!a) => b <<= disj_dneg (a => b);
              !a => exists x !a <<= Axiom.substitution !a x (var x);
              forall x a => !(!a) <<= contrapositive (!a => exists x !a);
              forall x a => b <<= detachment_transitivity (forall x a => !(!a)) (!(!a) => b);
              forall x a => forall x b <<= a_introduction x (forall x a => b);
            ]
      | a -> failwith (Printf.sprintf "invalid ∀-distribution: %s" (string_of_formula a))

    let witness x t =
      let free, _ = variable_occurrences (Atom ("p", [ t ])) in
      if free = [] then
        let x_eq_x = atom "=" [ var x; var x ] in
        let t_eq_t = atom "=" [ t; t ] in
        let x_eq_t = atom "=" [ var x; t ] in
        pseq ~scope:"witness"
          [
            x_eq_x <<= Axiom.identity x;
            t_eq_t <<= substitution_rule x_eq_x t_eq_t;
            t_eq_t => exists x x_eq_t <<= Axiom.substitution x_eq_t x t;
            exists x x_eq_t <<= detachment t_eq_t (t_eq_t => exists x x_eq_t);
          ]
      else failwith (Printf.sprintf "invalid witness: term %s must be variable-free" (string_of_term t))

    let substitution_theorem_e a xts =
      let xs, _ = List.split xts in
      let rec aux xs ctx =
        match xs with
        | x :: xs ->
            pseq
              ~scope:(Printf.sprintf "substitution_theorem_e: var %s" x)
              [
                a => exists_seq xs a <<= aux xs;
                exists_seq xs a => exists_seq (x :: xs) a <<= Axiom.substitution (exists_seq xs a) x (var x);
                a
                => exists_seq (x :: xs) a
                <<= detachment_transitivity (a => exists_seq xs a) (exists_seq xs a => exists_seq (x :: xs) a);
              ]
              ctx
        | [] -> (ctx, a => a)
      in
      pseq ~scope:"substitution_theorem_e"
        [
          a => a <<= tautology_theorem [] (a => a);
          a => exists_seq xs a <<= aux xs;
          substitute a xts => exists_seq xs a
          <<= substitution_rule (a => exists_seq xs a) (substitute a xts => exists_seq xs a);
        ]

    let substitution_theorem_a a xts =
      let xs, _ = List.split xts in
      let rec aux xs ctx =
        match xs with
        | x :: xs ->
            pseq
              ~scope:(Printf.sprintf "substitution_theorem_a: var %s" x)
              [
                !(forall_seq xs a) => exists x !(forall_seq xs a) <<= Axiom.substitution !(forall_seq xs a) x (var x);
                forall_seq (x :: xs) a
                => forall_seq xs a
                <<= tautology_theorem
                      [ !(forall_seq xs a) => exists x !(forall_seq xs a) ]
                      (forall_seq (x :: xs) a => forall_seq xs a);
                forall_seq xs a => a <<= aux xs;
                forall_seq (x :: xs) a
                => a
                <<= detachment_transitivity (forall_seq (x :: xs) a => forall_seq xs a) (forall_seq xs a => a);
              ]
              ctx
        | [] -> (ctx, a => a)
      in
      pseq ~scope:"substitution_theorem_a"
        [
          a => a <<= tautology_theorem [] (a => a);
          forall_seq xs a => a <<= aux xs;
          forall_seq xs a => substitute a xts
          <<= substitution_rule (forall_seq xs a => a) (forall_seq xs a => substitute a xts);
        ]

    let equivalence_theorem f g =
      match (f, g) with
      | ( Neg (Disj (Neg (Disj (Neg a, a')), Neg (Disj (Neg a'', a''')))),
          Neg (Disj (Neg (Disj (Neg b, b')), Neg (Disj (Neg b'', b''')))) )
        when (a, a', b, b') = (a''', a'', b''', b'') ->
          let rec aux c c' ctx =
            if c = c' then
              pseq ~scope:"equivalence theorem: special case"
                [ c => c <<= Axiom.propositional c; c <=> c' <<= conj (c => c) (c => c) ]
                ctx
            else if (c, c') = (b, b') then (ctx, b <=> b')
            else
              match (c, c') with
              | Neg d, Neg d' ->
                  pseq [ d <=> d' <<= aux d d'; !d <=> !d' <<= tautology_theorem [ d <=> d' ] (!d <=> !d') ] ctx
              | Disj (d, e), Disj (d', e') ->
                  pseq
                    [
                      d <=> d' <<= aux d d';
                      e <=> e' <<= aux e e';
                      (d || e) <=> (d' || e') <<= tautology_theorem [ d <=> d'; e <=> e' ] ((d || e) <=> (d' || e'));
                    ]
                    ctx
              | Exists (x, d), Exists (x', d') ->
                  if not (x = x') then
                    failwith
                      (Printf.sprintf "failed equivalence theorem invariant: cannot unify existentials %s and %s"
                         (extended_string_of_formula c) (extended_string_of_formula c'))
                  else
                    pseq
                      [
                        d <=> d' <<= aux d d';
                        d => d' <<= tautology_theorem [ d <=> d' ] (d => d');
                        d' => exists x d' <<= Axiom.substitution d' x (var x);
                        d => exists x d' <<= detachment_transitivity (d => d') (d' => exists x d');
                        exists x d => exists x d' <<= Rule.e_introduction x (d => exists x d');
                        d' => d <<= tautology_theorem [ d <=> d' ] (d' => d);
                        d => exists x d <<= Axiom.substitution d x (var x);
                        d' => exists x d <<= detachment_transitivity (d' => d) (d => exists x d);
                        exists x d' => exists x d <<= Rule.e_introduction x (d' => exists x d);
                        exists x d <=> exists x d' <<= conj (exists x d => exists x d') (exists x d' => exists x d);
                      ]
                      ctx
              | _, _ ->
                  failwith
                    (Printf.sprintf "failed equivalence theorem invariant: cannot unify %s and %s"
                       (extended_string_of_formula c) (extended_string_of_formula c'))
          in
          aux a a'
      | _ ->
          failwith
            (Printf.sprintf "invalid equivalences: %s and %s" (extended_string_of_formula f)
               (extended_string_of_formula g))

    let variant_equivalence_e a x y =
      let axy = substitute a [ (x, var y) ] in
      pseq ~scope:"variant_equivalence_e"
        [
          a => exists y axy <<= Axiom.substitution axy y (var x);
          exists x a => exists y axy <<= Rule.e_introduction x (a => exists y axy);
          axy => exists x a <<= Axiom.substitution a x (var y);
          exists y axy => exists x a <<= Rule.e_introduction y (axy => exists x a);
          exists x a <=> exists y axy <<= conj (exists x a => exists y axy) (exists y axy => exists x a);
        ]

    let variant_equivalence_a a x y =
      let axy = substitute a [ (x, var y) ] in
      pseq ~scope:"variant_equivalence_a"
        [
          exists x !a <=> exists y !axy <<= variant_equivalence_e !a x y;
          forall x a <=> forall y axy
          <<= tautology_theorem [ exists x !a <=> exists y !axy ] (forall x a <=> forall y axy);
        ]

    let factor_disj_left_quantifier_e a =
      match a with
      | Disj (Exists (x, b), c) ->
          pseq ~scope:"factor_disj_left_quantifier_e"
            [
              b => (b || c) <<= tautology_theorem [] (b => (b || c));
              exists x b => exists x (b || c) <<= e_distribution x (b => (b || c));
              (b || c) => exists x (b || c) <<= Axiom.substitution (b || c) x (var x);
              c => exists x (b || c) <<= tautology_theorem [ (b || c) => exists x (b || c) ] (c => exists x (b || c));
              (exists x b || c)
              => exists x (b || c)
              <<= tautology_theorem
                    [ exists x b => exists x (b || c); c => exists x (b || c) ]
                    ((exists x b || c) => exists x (b || c));
              b => exists x b <<= Axiom.substitution b x (var x);
              (b || c) => (exists x b || c) <<= tautology_theorem [ b => exists x b ] ((b || c) => (exists x b || c));
              exists x (b || c) => (exists x b || c) <<= Rule.e_introduction x ((b || c) => (exists x b || c));
              (exists x b || c)
              <=> exists x (b || c)
              <<= conj ((exists x b || c) => exists x (b || c)) (exists x (b || c) => (exists x b || c));
            ]
      | _ ->
          failwith
            (Printf.sprintf "invalid left existential quantifier factorization: %s" (extended_string_of_formula a))

    let factor_disj_right_quantifier_e a =
      match a with
      | Disj (b, Exists (x, c)) ->
          pseq ~scope:"factor_disj_right_quantifier_e"
            [
              (b || c) => exists x (b || c) <<= Axiom.substitution (b || c) x (var x);
              b => exists x (b || c) <<= tautology_theorem [ (b || c) => exists x (b || c) ] (b => exists x (b || c));
              c => (b || c) <<= tautology_theorem [] (c => (b || c));
              exists x c => exists x (b || c) <<= e_distribution x (c => (b || c));
              (b || exists x c)
              => exists x (b || c)
              <<= tautology_theorem
                    [ b => exists x (b || c); exists x c => exists x (b || c) ]
                    ((b || exists x c) => exists x (b || c));
              c => exists x c <<= Axiom.substitution c x (var x);
              (b || c) => (b || exists x c) <<= tautology_theorem [ c => exists x c ] ((b || c) => (b || exists x c));
              exists x (b || c) => (b || exists x c) <<= Rule.e_introduction x ((b || c) => (b || exists x c));
              (b || exists x c)
              <=> exists x (b || c)
              <<= tautology_theorem
                    [ (b || exists x c) => exists x (b || c); exists x (b || c) => (b || exists x c) ]
                    ((b || exists x c) <=> exists x (b || c));
            ]
      | _ ->
          failwith
            (Printf.sprintf "invalid right existential quantifier factorization: %s" (extended_string_of_formula a))

    let factor_disj_left_quantifier_a a =
      match a with
      | Disj (Neg (Exists (x, Neg b)), c) ->
          pseq ~scope:"factor_disj_left_quantifier_a"
            [
              b => (b || c) <<= tautology_theorem [] (b => (b || c));
              forall x b => forall x (b || c) <<= a_distribution x (b => (b || c));
              c => (b || c) <<= tautology_theorem [] (c => (b || c));
              c => forall x (b || c) <<= a_introduction x (c => (b || c));
              (forall x b || c)
              => forall x (b || c)
              <<= tautology_theorem
                    [ forall x b => forall x (b || c); c => forall x (b || c) ]
                    ((forall x b || c) => forall x (b || c));
              forall x (b || c) => (b || c) <<= substitution_theorem_a (b || c) [ (x, var x) ];
              (forall x (b || c) && !c)
              => b
              <<= tautology_theorem [ forall x (b || c) => (b || c) ] ((forall x (b || c) && !c) => b);
              (forall x (b || c) && !c) => forall x b <<= a_introduction x ((forall x (b || c) && !c) => b);
              forall x (b || c)
              => (forall x b || c)
              <<= tautology_theorem [ (forall x (b || c) && !c) => forall x b ] (forall x (b || c) => (forall x b || c));
              (forall x b || c)
              <=> forall x (b || c)
              <<= tautology_theorem
                    [ (forall x b || c) => forall x (b || c); forall x (b || c) => (forall x b || c) ]
                    ((forall x b || c) <=> forall x (b || c));
            ]
      | _ ->
          let () =
            Printf.printf "invalid left universal quantifier factorization: %s\n%!" (extended_string_of_formula a)
          in
          failwith (Printf.sprintf "invalid left universal quantifier factorization: %s" (extended_string_of_formula a))

    let factor_disj_right_quantifier_a a =
      match a with
      | Disj (b, Neg (Exists (x, Neg c))) ->
          pseq ~scope:"factor_disj_right_quantifier_a"
            [
              b => (b || c) <<= tautology_theorem [] (b => (b || c));
              b => forall x (b || c) <<= a_introduction x (b => (b || c));
              c => (b || c) <<= tautology_theorem [] (c => (b || c));
              forall x c => forall x (b || c) <<= a_distribution x (c => (b || c));
              (b || forall x c)
              => forall x (b || c)
              <<= tautology_theorem
                    [ b => forall x (b || c); forall x c => forall x (b || c) ]
                    ((b || forall x c) => forall x (b || c));
              forall x (b || c) => (b || c) <<= substitution_theorem_a (b || c) [ (x, var x) ];
              (forall x (b || c) && !b)
              => c
              <<= tautology_theorem [ forall x (b || c) => (b || c) ] ((forall x (b || c) && !b) => c);
              (forall x (b || c) && !b) => forall x c <<= a_introduction x ((forall x (b || c) && !b) => c);
              forall x (b || c)
              => (b || forall x c)
              <<= tautology_theorem [ (forall x (b || c) && !b) => forall x c ] (forall x (b || c) => (b || forall x c));
              (b || forall x c)
              <=> forall x (b || c)
              <<= tautology_theorem
                    [ (b || forall x c) => forall x (b || c); forall x (b || c) => (b || forall x c) ]
                    ((b || forall x c) <=> forall x (b || c));
            ]
      | _ ->
          failwith
            (Printf.sprintf "invalid right universal quantifier factorization: %s" (extended_string_of_formula a))

    let universal_to_existential x a =
      pseq ~scope:"universal_to_existential"
        [
          forall x a => a <<= substitution_theorem_a a [ (x, var x) ];
          a => exists x a <<= Axiom.substitution a x (var x);
          forall x a => exists x a <<= detachment_transitivity (forall x a => a) (a => exists x a);
        ]
  end
end
