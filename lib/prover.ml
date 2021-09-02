open Fol
open Proof
open Proof.Calculus

module type Prover = sig
  val prove : proof -> formula -> conclusion
end

module Shoenfield : Prover = struct
  let find_compl pos neg =
    List.find_opt (fun a -> List.exists (fun b -> Neg a = b) neg) pos

  let prove_elementary_by_identity ctx _ bs _ _ =
    let x_opt =
      List.find_map
        (function
          | Atom ("=", [ Var x; Var x' ]) when x = x' -> Some x | _ -> None)
        bs
    in
    match x_opt with
    | Some x ->
        let proof =
          let* ctx, s1 = Axiom.identity ctx x in
          let* ctx, s2 = Meta.general_expansion ctx [ s1 ] bs in
          proves ctx s2
        in
        Some proof
    | None -> None

  let prove_elementary_by_propositional ctx _ bs pos neg =
    match find_compl pos neg with
    | Some a' ->
        let proof =
          if Util.is_sublist [ Neg a'; a' ] bs then
            let* ctx, _ = Axiom.propositional ctx a' in
            let* ctx, s2 = Meta.general_expansion ctx [ Neg a'; a' ] bs in
            proves ctx s2
          else
            let* ctx, s1 = Axiom.propositional ctx a' in
            let* ctx, _ = Meta.commute ctx s1 in
            let* ctx, s3 = Meta.general_expansion ctx [ a'; Neg a' ] bs in
            proves ctx s3
        in
        Some proof
    | None -> None

  let prove_elementary ctx a bs pos neg =
    let fs =
      [
        prove_elementary_by_identity;
        prove_elementary_by_propositional;
        (* TODO: axiom: equality *)
        (* TODO: axiom: substitution *)
      ]
    in
    let p =
      List.fold_left
        (fun acc f ->
          match acc with Some res -> Some res | None -> f ctx a bs pos neg)
        None fs
    in
    match p with
    | Some res -> res
    | None ->
        Error
          (Printf.sprintf "failed to prove elementary disjunction: %s"
             (string_of_formula a))

  let rec prove ctx a =
    let bs = list_of_disj a in
    let pos, neg = List.partition (function Neg _ -> false | _ -> true) bs in
    let all_elementary =
      List.for_all is_elementary pos
      && List.for_all (function Neg a -> is_elementary a | _ -> false) neg
    in
    if all_elementary then prove_elementary ctx a bs pos neg
    else prove_non_elementary ctx a

  and prove_non_elementary ctx a =
    match list_of_disj a with
    | Or (b, c) :: a' ->
        let* ctx, s1 = prove ctx (disj_of_list (b :: c :: a')) in
        let* ctx, s2 = Rule.associative ctx s1 in
        assert (s2 = a);
        proves ctx s2
    | Neg (Neg b) :: a' ->
        let* ctx, s1 = prove ctx (disj_of_list (b :: a')) in
        let* ctx, s2 =
          if a' = [] then Meta.neg_neg ctx s1 else Meta.disj_neg_neg ctx s1
        in
        assert (s2 = a);
        proves ctx s2
    | Neg (Or (b, c)) :: a' ->
        if a' = [] then (
          let* ctx, s1 = prove ctx (Neg b) in
          let* ctx, s2 = prove ctx (Neg c) in
          let* ctx, s3 = Axiom.propositional ctx (Or (b, c)) in
          let* ctx, s4 = Rule.associative ctx s3 in
          let* ctx, s5 = Meta.commute ctx s4 in
          let* ctx, s6 = Meta.disj_neg_neg ctx s5 in
          let* ctx, s7 = Meta.modus_ponens ctx s2 s6 in
          let* ctx, s8 = Meta.commute ctx s7 in
          let* ctx, s9 = Meta.disj_neg_neg ctx s8 in
          let* ctx, s10 = Meta.modus_ponens ctx s1 s9 in
          assert (s10 = a);
          proves ctx s10)
        else
          let* ctx, s1 = prove ctx (disj_of_list (Neg b :: a')) in
          let* ctx, s2 = prove ctx (disj_of_list (Neg c :: a')) in
          let* ctx, s3 = Axiom.propositional ctx (Or (b, c)) in
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
          assert (s14 = a);
          proves ctx s14
    | [ b; c ] ->
        let* ctx, s1 = prove_non_elementary ctx (Or (c, b)) in
        let* ctx, s2 = Meta.commute ctx s1 in
        assert (s2 = a);
        proves ctx s2
    | b :: bs ->
        let b' = disj_of_list (bs @ [ b ]) in
        let* ctx, _ = prove_non_elementary ctx b' in
        let* ctx, s2 = Meta.general_expansion ctx (bs @ [ b ]) (b :: bs) in
        assert (s2 = a);
        proves ctx s2
    | _ ->
        Error
          (Printf.sprintf "invalid prove_non_elementary: %s"
             (string_of_formula a))
end
