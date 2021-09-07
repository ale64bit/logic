open Fol
module StringSet = Set.Make (String)

module FormulaMap = Map.Make (struct
  type t = formula

  let compare = Stdlib.compare
end)

module Calculus = struct
  type proof_line = { index : int; reason : string }

  type proof = proof_line FormulaMap.t

  let empty_proof = FormulaMap.empty

  let proof_length = FormulaMap.cardinal

  type conclusion = (proof * formula, string) result

  let add ctx a reason =
    if FormulaMap.mem a ctx then Ok (ctx, a)
    else
      let l = { index = 1 + FormulaMap.cardinal ctx; reason } in
      Ok (ctx |> FormulaMap.add a l, a)

  let premise ctx a = add ctx a "premise"

  let ( let* ) r f = match r with Error _ as err -> err | Ok (p, a) -> f (p, a)

  let proves ctx a = add ctx a "goal"

  module Axiom = struct
    let propositional ctx a = add ctx (Or (Neg a, a)) "axiom: propositional"

    let substitution ctx a x t =
      add ctx
        (Defined.impl (substitute x t a) (Exists (x, a)))
        "axiom: substitution"

    let identity ctx x =
      add ctx (Atom ("=", [ Var x; Var x ])) "axiom: identity"

    let fequality ctx xys f =
      let xs, ys = List.split xys in
      let fx = Fun (f, List.map (fun x -> Var x) xs) in
      let fy = Fun (f, List.map (fun y -> Var y) ys) in
      add ctx
        (List.fold_left
           (fun acc (x, y) -> Defined.impl (Atom ("=", [ Var x; Var y ])) acc)
           (Atom ("=", [ fx; fy ]))
           (List.rev xys))
        "axiom: equality"

    let pequality ctx xys p =
      let xs, ys = List.split xys in
      let px = Atom (p, List.map (fun x -> Var x) xs) in
      let py = Atom (p, List.map (fun y -> Var y) ys) in
      add ctx
        (List.fold_left
           (fun acc (x, y) -> Defined.impl (Atom ("=", [ Var x; Var y ])) acc)
           (Defined.impl px py) (List.rev xys))
        "axiom: equality"
  end

  module Rule = struct
    let expansion ctx b a =
      let { index; _ } = FormulaMap.find a ctx in
      let reason = Printf.sprintf "rule: expansion: (%d)" index in
      add ctx (Or (b, a)) reason

    let contraction ctx a =
      match a with
      | Or (a', a'') when a' = a'' ->
          let { index; _ } = FormulaMap.find a ctx in
          let reason = Printf.sprintf "rule: contraction: (%d)" index in
          add ctx a' reason
      | _ ->
          Error (Printf.sprintf "invalid contraction: %s" (string_of_formula a))

    let associative ctx a =
      match a with
      | Or (a', Or (b', c')) ->
          let { index; _ } = FormulaMap.find a ctx in
          let reason = Printf.sprintf "rule: associative: (%d)" index in
          add ctx (Or (Or (a', b'), c')) reason
      | _ ->
          Error (Printf.sprintf "invalid association: %s" (string_of_formula a))

    let cut ctx b c =
      match (b, c) with
      | Or (a, b'), Or (Neg a', c') when a = a' ->
          let { index = indexb; _ } = FormulaMap.find b ctx in
          let { index = indexc; _ } = FormulaMap.find c ctx in
          let reason = Printf.sprintf "rule: cut: (%d) (%d)" indexb indexc in
          add ctx (Or (b', c')) reason
      | _ ->
          let () = assert false in
          Error
            (Printf.sprintf "invalid cut: (%s) and (%s)" (string_of_formula b)
               (string_of_formula c))

    let e_introduction ctx x a =
      match a with
      | Or (Neg a', b') when not (is_free x b') ->
          let { index; _ } = FormulaMap.find a ctx in
          let reason = Printf.sprintf "rule: e-introduction: (%d)" index in
          add ctx (Defined.impl (Exists (x, a')) b') reason
      | _ ->
          Error
            (Printf.sprintf "invalid e-introduction: %s and %s" x
               (string_of_formula a))
  end
end

module Meta = struct
  open Calculus

  let commute ctx = function
    | Or (a', b') as a ->
        let* ctx, s1 = Axiom.propositional ctx a' in
        let* ctx, s2 = Rule.cut ctx a s1 in
        assert (s2 = Or (b', a'));
        proves ctx s2
    | a -> Error (Printf.sprintf "invalid commute: %s" (string_of_formula a))

  let modus_ponens ctx a a_to_b =
    match a_to_b with
    | Or (Neg a', b) when a = a' ->
        let* ctx, s1 = Rule.expansion ctx b a in
        let* ctx, s2 = commute ctx s1 in
        let* ctx, s3 = Rule.cut ctx s2 a_to_b in
        let* ctx, s4 = Rule.contraction ctx s3 in
        assert (s4 = b);
        proves ctx s4
    | a ->
        Error
          (Printf.sprintf "invalid modus ponens: %s and %s"
             (string_of_formula a) (string_of_formula a_to_b))

  let neg_neg_intro ctx a =
    let* ctx, s2 = Rule.expansion ctx (Neg (Neg a)) a in
    let* ctx, s3 = Axiom.propositional ctx (Neg (Neg a)) in
    let* ctx, s4 = Rule.cut ctx s2 s3 in
    let* ctx, s5 = Axiom.propositional ctx (Neg a) in
    let* ctx, s6 = Rule.cut ctx s5 s3 in
    let* ctx, s7 = Rule.cut ctx s4 s6 in
    let* ctx, s8 = Rule.contraction ctx s7 in
    assert (s8 = Neg (Neg a));
    proves ctx s8

  let neg_neg_elim ctx = function
    | Neg (Neg a') as a ->
        let* ctx, s1 = Axiom.propositional ctx a in
        let* ctx, s2 = Axiom.propositional ctx a' in
        let* ctx, s3 = commute ctx s1 in
        let* ctx, s4 = Rule.cut ctx s2 s3 in
        let* ctx, s5 = commute ctx s4 in
        let* ctx, s6 = modus_ponens ctx a s5 in
        assert (s6 = a');
        proves ctx s6
    | a ->
        Error
          (Printf.sprintf "invalid double-negation elimination: %s"
             (string_of_formula a))

  let disj_neg_neg ctx = function
    | Or (a', b') as a ->
        let* ctx, s1 = Axiom.propositional ctx (Neg a') in
        let* ctx, s2 = commute ctx s1 in
        let* ctx, s3 = Rule.cut ctx a s2 in
        let* ctx, s4 = commute ctx s3 in
        assert (s4 = Or (Neg (Neg a'), b'));
        proves ctx s4
    | a ->
        Error
          (Printf.sprintf "invalid disjuction neg neg: %s" (string_of_formula a))

  let disj_contraction ctx = function
    | Or (a, Or (b, b')) as a' when b = b' ->
        let* ctx, s1 = Rule.associative ctx a' in
        let* ctx, s2 = commute ctx s1 in
        let* ctx, s3 = Rule.expansion ctx a s2 in
        let* ctx, s4 = Rule.associative ctx s3 in
        let* ctx, s5 = Rule.contraction ctx s4 in
        assert (s5 = Or (a, b));
        proves ctx s5
    | a ->
        Error
          (Printf.sprintf "invalid disj_contraction: %s" (string_of_formula a))

  let associative_right ctx = function
    | Or (Or (a', b'), c') as a ->
        let* ctx, s1 = commute ctx a in
        let* ctx, s2 = Rule.associative ctx s1 in
        let* ctx, s3 = commute ctx s2 in
        let* ctx, s4 = Rule.associative ctx s3 in
        let* ctx, s5 = commute ctx s4 in
        assert (s5 = Or (Or (a', b'), c'));
        proves ctx s5
    | a ->
        Error
          (Printf.sprintf "invalid right association: %s" (string_of_formula a))

  (* Infer ¬(A ∨ B) ∨ C from ¬A ∨ C and ¬B ∨ C *)
  let taut_theorem_result_c ctx a b =
    match (a, b) with
    | Or (Neg a', c), Or (Neg b', c') when c = c' ->
        let* ctx, s3 = Axiom.propositional ctx (Or (a', b')) in
        let* ctx, s4 = Rule.associative ctx s3 in
        let* ctx, s5 = commute ctx s4 in
        let* ctx, s6 = Rule.cut ctx s5 b in
        let* ctx, s7 = commute ctx s6 in
        let* ctx, s8 = Rule.associative ctx s7 in
        let* ctx, s9 = commute ctx s8 in
        let* ctx, s10 = Rule.cut ctx s9 a in
        let* ctx, s11 = commute ctx s10 in
        let* ctx, s12 = Rule.associative ctx s11 in
        let* ctx, s13 = commute ctx s12 in
        let* ctx, s14 = disj_contraction ctx s13 in
        assert (s14 = Or (Neg (Or (a', b')), c'));
        proves ctx s14
    | _ ->
        Error
          (Printf.sprintf "invalid taut_theorem_result_c: %s and %s"
             (string_of_formula a) (string_of_formula b))

  let fold_with_rule ctx f x0 xs =
    List.fold_left
      (fun acc xi ->
        match acc with Ok (ctx, si) -> f ctx si xi | Error msg -> Error msg)
      (Ok (ctx, x0))
      xs

  let split_at xi xs =
    let rec aux left = function
      | xj :: xs -> if xi = xj then (left, xs) else aux (xj :: left) xs
      | [] -> (left, [])
    in
    let l, r = aux [] xs in
    (List.rev l, r)

  (*
    If {Ai1, ... , Aim} is a subset of {A1, ... , An}, constructs a proof of ⊢(Ai1 ∨ ... ∨ Aim) → (A1 ∨ ... ∨ An).

    In the base case of m=1, it first expands Ai1 to (A1 ∨ ( A2 ∨ ... ) ) ∨ Ai1 and then commutes and expands the rest of the terms.

    In the general case, it first proves ⊢Aij → (A1 ∨ ... ∨ An) for 1 <= j <= m and then combines the results using
    case (C) of the tautology theorem, as presented in Shoenfield's "Mathematical Logic".
  *)
  let rec general_expansion_implication ctx a' a =
    assert (List.length a' > 0);
    if Util.is_subset a' a then
      match List.rev a' with
      | [ ai ] ->
          let left, right = split_at ai a in
          let* ctx, s1 = Axiom.propositional ctx ai in
          let* ctx, s2 =
            if right = [] then commute ctx s1
            else
              let* ctx, s1' = Rule.expansion ctx (disj_of_list right) s1 in
              let* ctx, s2' = Rule.associative ctx s1' in
              let* ctx, s3' = commute ctx s2' in
              let* ctx, s4' = Rule.associative ctx s3' in
              proves ctx s4'
          in
          let* ctx, s3 =
            fold_with_rule ctx
              (fun ctx acc ai ->
                let* ctx, s1' = Rule.expansion ctx ai acc in
                let* ctx, s2' = Rule.associative ctx s1' in
                proves ctx s2')
              s2 (List.rev left)
          in
          let* ctx, s4 = commute ctx s3 in
          assert (s4 = disj_of_list (Neg ai :: a));
          proves ctx s4
      | am :: a'' ->
          let proof =
            let* ctx, sm = general_expansion_implication ctx [ am ] a in
            fold_with_rule ctx
              (fun ctx b ai ->
                let* ctx, s1 = general_expansion_implication ctx [ ai ] a in
                taut_theorem_result_c ctx s1 b)
              sm a''
          in
          proof
      | [] -> failwith "impossible general expansion implication"
    else
      Error
        (Printf.sprintf "invalid general expansion implication: [%s] -> [%s]"
           (String.concat ", " (List.map string_of_formula a'))
           (String.concat ", " (List.map string_of_formula a)))

  let general_expansion ctx a' a =
    if Util.is_subset a' a then (
      let* ctx, s1 = general_expansion_implication ctx a' a in
      let* ctx, s2 = modus_ponens ctx (disj_of_list a') s1 in
      assert (s2 = disj_of_list a);
      proves ctx s2)
    else
      Error
        (Printf.sprintf "invalid general expansion: [%s] -> [%s]"
           (String.concat ", " (List.map string_of_formula a'))
           (String.concat ", " (List.map string_of_formula a)))

  let rev_impl ctx = function
    | Or (Neg a', b') as a ->
        let* ctx, s1 = commute ctx a in
        let* ctx, s2 = disj_neg_neg ctx s1 in
        assert (s2 = Defined.impl (Neg b') (Neg a'));
        proves ctx s2
    | a ->
        Error
          (Printf.sprintf "invalid reverse implication reverse: %s"
             (string_of_formula a))

  let a_introduction ctx x a =
    match a with
    | Or (Neg a', b') when not (is_free x a') ->
        let* ctx, s1 = rev_impl ctx a in
        let* ctx, s2 = Rule.e_introduction ctx x s1 in
        let* ctx, s3 = commute ctx s2 in
        assert (s3 = Defined.impl a' (Defined.forall x b'));
        proves ctx s3
    | _ ->
        Error
          (Printf.sprintf "invalid a-introduction: %s %s" x
             (string_of_formula a))

  let generalization ctx x a =
    let* ctx, s1 = Rule.expansion ctx (Neg (Neg (Defined.forall x a))) a in
    let* ctx, s2 = a_introduction ctx x s1 in
    let* ctx, s3 = rev_impl ctx s2 in
    let* ctx, s4 = Rule.contraction ctx s3 in
    let* ctx, s5 = neg_neg_elim ctx s4 in
    assert (s5 = Defined.forall x a);
    proves ctx s5

  let rec substitution ctx a a' =
    match is_instance a' a with
    | [], true ->
        assert (a = a');
        proves ctx a'
    | [ (x, t) ], true ->
        let* ctx, s1 = generalization ctx x a in
        let* ctx, s2 = Axiom.substitution ctx (Neg a) x t in
        let* ctx, s3 = rev_impl ctx s2 in
        let* ctx, s4 = modus_ponens ctx s1 s3 in
        let* ctx, s5 = neg_neg_elim ctx s4 in
        assert (s5 = a');
        proves ctx s5
    | m, true ->
        let free_a, bound_a = variables a in
        let free_a', bound_a' = variables a' in
        let all = StringSet.of_list (free_a @ bound_a @ free_a' @ bound_a') in
        let rec gen_fresh_vars i acc =
          if List.length acc = List.length m then List.rev acc
          else
            let yi = Printf.sprintf "y%d'" i in
            gen_fresh_vars (i + 1)
              (if StringSet.mem yi all then acc else yi :: acc)
        in
        let xs, ts = List.split m in
        (* The intermediate variables [ys] are needed since the terms can
           contain some of the free variables *)
        let ys = gen_fresh_vars 1 [] in
        let* ctx, s1 =
          fold_with_rule ctx
            (fun ctx ai (xi, yi) ->
              let* ctx, s1' = substitution ctx ai (substitute xi (Var yi) ai) in
              proves ctx s1')
            a (List.combine xs ys)
        in
        let* ctx, s2 =
          fold_with_rule ctx
            (fun ctx ai (yi, ti) ->
              let* ctx, s1' = substitution ctx ai (substitute yi ti ai) in
              proves ctx s1')
            s1 (List.combine ys ts)
        in
        assert (s2 = a');
        proves ctx s2
    | _ ->
        Error
          (Printf.sprintf "invalid substitution: %s is not an instance of %s"
             (string_of_formula a') (string_of_formula a))
end

let print_proof out p =
  let open Calculus in
  let sorted =
    List.sort
      (fun (_, lx) (_, ly) -> compare lx.index ly.index)
      (FormulaMap.bindings p)
  in
  let dig = String.length (string_of_int (List.length sorted)) in
  let maxw =
    List.fold_left
      (fun acc (a, _) ->
        let len = Utf8.length (string_of_formula a) in
        if acc > len then acc else len)
      0 sorted
  in
  List.iter
    (fun (a, { index; reason }) ->
      let s = string_of_formula a in
      let dw = String.length s - Utf8.length s in
      Printf.fprintf out "(%.*d) %-*s [%s]\n" dig index (maxw + 8 + dw) s reason)
    sorted

let print_proof_tex ?(fmap = fun _ -> None) out p =
  let open Calculus in
  let sorted =
    List.sort
      (fun (_, lx) (_, ly) -> compare lx.index ly.index)
      (FormulaMap.bindings p)
  in
  List.iter
    (fun (a, { index; reason }) ->
      Printf.fprintf out "\\item{(%d)} $%s$ \\hfill [%s]\n" index
        (tex_of_formula ~fmap a) reason)
    sorted
