open Core

module Repr = struct
  type term = Var of string | Const of string | Fun of string * term list
  type formula = Atom of string * term list | Neg of formula | Disj of formula * formula | Exists of string * formula
end

module S : FirstOrderLanguage.S with type term = Repr.term and type formula = Repr.formula = struct
  include Repr

  let var x = Var x
  let const e = Const e
  let func f ts = Fun (f, ts)
  let atom p ts = Atom (p, ts)
  let neg a = Neg a
  let disj a b = Disj (a, b)
  let conj a b = neg (disj (neg a) (neg b))
  let impl a b = disj (neg a) b
  let eq a b = conj (impl a b) (impl b a)
  let exists x a = Exists (x, a)
  let forall x a = neg (exists x (neg a))
end

module Syntax (L : FirstOrderLanguage.S with type term = Repr.term and type formula = Repr.formula) = struct
  open L
  open Repr

  module FormulaSet = Set.Make (struct
    type t = formula

    let compare = Stdlib.compare
  end)

  module FormulaMap = Map.Make (struct
    type t = formula

    let compare = Stdlib.compare
  end)

  type var = string
  type substitution = (var * term) list

  let rec exists_seq xs a = match xs with x :: xs -> exists x (exists_seq xs a) | [] -> a
  let rec forall_seq xs a = match xs with x :: xs -> forall x (forall_seq xs a) | [] -> a

  let rec string_of_term = function
    | Var x -> x
    | Const e -> e
    | Fun (f, ts) -> Printf.sprintf "%s(%s)" f (String.concat ", " (List.map string_of_term ts))

  let string_of_formula a =
    let rec aux ?(top = true) = function
      | Atom ("=", [ lhs; rhs ]) -> Printf.sprintf "(%s = %s)" (string_of_term lhs) (string_of_term rhs)
      | Atom (p, []) -> Printf.sprintf "%s" p
      | Atom (p, ts) -> Printf.sprintf "%s(%s)" p (String.concat ", " (List.map string_of_term ts))
      | Neg a -> Printf.sprintf "¬%s" (aux ~top:false a)
      | Disj (a, b) ->
          let s = Printf.sprintf "%s ∨ %s" (aux ~top:false a) (aux ~top:false b) in
          if top then s else Printf.sprintf "(%s)" s
      | Exists (x, f) -> Printf.sprintf "%s %s" (Printf.sprintf "∃%s" x) (aux ~top:false f)
    in
    aux a

  let extended_string_of_formula a =
    let rec aux ?(top = true) = function
      | Atom ("=", [ lhs; rhs ]) -> Printf.sprintf "(%s = %s)" (string_of_term lhs) (string_of_term rhs)
      | Atom (p, []) -> Printf.sprintf "%s" p
      | Atom (p, ts) -> Printf.sprintf "%s(%s)" p (String.concat ", " (List.map string_of_term ts))
      | Disj (Neg a, b) ->
          let s = Printf.sprintf "%s → %s" (aux ~top:false a) (aux ~top:false b) in
          if top then s else Printf.sprintf "(%s)" s
      | Neg (Disj (Neg (Disj (Neg a, b)), Neg (Disj (Neg b', a')))) when a = a' && b = b' ->
          let s = Printf.sprintf "%s ↔ %s" (aux ~top:false a) (aux ~top:false b) in
          if top then s else Printf.sprintf "(%s)" s
      | Neg (Disj (Neg a, Neg b)) ->
          let s = Printf.sprintf "%s ∧ %s" (aux ~top:false a) (aux ~top:false b) in
          if top then s else Printf.sprintf "(%s)" s
      | Neg (Exists (x, Neg a)) -> Printf.sprintf "%s %s" (Printf.sprintf "∀%s" x) (aux ~top:false a)
      | Neg a -> Printf.sprintf "¬%s" (aux ~top:false a)
      | Disj (a, b) ->
          let s = Printf.sprintf "%s ∨ %s" (aux ~top:false a) (aux ~top:false b) in
          if top then s else Printf.sprintf "(%s)" s
      | Exists (x, a) -> Printf.sprintf "%s %s" (Printf.sprintf "∃%s" x) (aux ~top:false a)
    in
    aux a

  let tex_of_formula ?(fmap = fun _ -> None) a =
    let rec aux ?(top = true) a =
      match fmap a with
      | Some s -> s
      | None -> (
          match a with
          | Atom ("=", [ lhs; rhs ]) -> Printf.sprintf "(%s = %s)" (string_of_term lhs) (string_of_term rhs)
          | Atom (p, ts) -> Printf.sprintf "%s(%s)" p (String.concat ", " (List.map string_of_term ts))
          | Neg a -> Printf.sprintf "\\neg %s" (aux ~top:false a)
          | Disj (a, b) ->
              let s = Printf.sprintf "%s \\lor %s" (aux ~top:false a) (aux ~top:false b) in
              if top then s else Printf.sprintf "(%s)" s
          | Exists (x, f) -> Printf.sprintf "%s %s" (Printf.sprintf "\\exists %s" x) (aux ~top:false f))
    in
    aux a

  let string_of_substitution s =
    "{" ^ String.concat ", " (List.map (fun (x, t) -> Printf.sprintf "%s -> %s" x (string_of_term t)) s) ^ "}"

  let rec disj_of_list = function
    | [] -> failwith "impossible: empty list"
    | [ a ] -> a
    | a :: xs -> disj a (disj_of_list xs)

  let list_of_disj a =
    let rec aux acc = function Disj (a', b') -> aux (a' :: acc) b' | a' -> a' :: acc in
    List.rev (aux [] a)

  let rec impl_of_list = function
    | [] -> failwith "impossible: empty list"
    | [ a ] -> a
    | a :: xs -> impl a (impl_of_list xs)

  let variable_occurrences a =
    let module VS = Set.Make (String) in
    let rec aux_term bound = function
      | Var x -> if VS.mem x bound then (VS.empty, VS.singleton x) else (VS.singleton x, VS.empty)
      | Const _ -> (VS.empty, VS.empty)
      | Fun (_, ts) ->
          List.fold_left
            (fun (free_acc, bound_acc) t ->
              let free_t, bound_t = aux_term bound t in
              (VS.union free_acc free_t, VS.union bound_acc bound_t))
            (VS.empty, VS.empty) ts
    in
    let rec aux bound = function
      | Atom (_, ts) ->
          List.fold_left
            (fun (free_acc, bound_acc) t ->
              let free_t, bound_t = aux_term bound t in
              (VS.union free_acc free_t, VS.union bound_acc bound_t))
            (VS.empty, VS.empty) ts
      | Neg a -> aux bound a
      | Disj (a, b) ->
          let free_a, bound_a = aux bound a in
          let free_b, bound_b = aux bound b in
          (VS.union free_a free_b, VS.union bound_a bound_b)
      | Exists (x, a) -> aux (VS.add x bound) a
    in
    let free, bound = aux VS.empty a in
    (VS.elements free, VS.elements bound)

  let gen_fresh_vars n bs =
    let module VS = Set.Make (String) in
    let used =
      List.fold_left
        (fun vs b ->
          let free, bound = variable_occurrences b in
          VS.union vs (VS.union (VS.of_list free) (VS.of_list bound)))
        VS.empty bs
    in
    let rec aux i k acc =
      if k = n then List.rev acc
      else
        let yi = Printf.sprintf "y%d'" i in
        if VS.mem yi used then aux (i + 1) k acc else aux (i + 1) (k + 1) (yi :: acc)
    in
    aux 1 0 []

  let substitute a xts =
    let module VS = Set.Make (String) in
    let module SUBS = Map.Make (String) in
    let s = SUBS.of_seq (List.to_seq xts) in
    let substitutible t bound =
      (* None of the free variables in [t] can become bound when substituted *)
      let free, _ = variable_occurrences (Atom ("", [ t ])) in
      List.for_all (fun y -> not (VS.mem y bound)) free
    in
    let rec aux_term bound = function
      | Var x when SUBS.mem x s && not (VS.mem x bound) ->
          let t = SUBS.find x s in
          assert (substitutible t bound);
          t
      | Var x -> Var x
      | Const e -> Const e
      | Fun (f, ts) -> Fun (f, List.map (aux_term bound) ts)
    in
    let rec aux bound = function
      | Atom (p, ts) -> Atom (p, List.map (aux_term bound) ts)
      | Neg a -> Neg (aux bound a)
      | Disj (a, b) -> Disj (aux bound a, aux bound b)
      | Exists (x, a) -> Exists (x, aux (VS.add x bound) a)
    in
    aux VS.empty a

  let substitute_opt a xts =
    let module VS = Set.Make (String) in
    let module SUBS = Map.Make (String) in
    let s = SUBS.of_seq (List.to_seq xts) in
    let substitutible t bound =
      (* None of the free variables in [t] can become bound when substituted *)
      let free, _ = variable_occurrences (Atom ("", [ t ])) in
      List.for_all (fun y -> not (VS.mem y bound)) free
    in
    let open Util.OptionUtil in
    let rec aux_term bound = function
      | Var x when SUBS.mem x s && not (VS.mem x bound) ->
          let t = SUBS.find x s in
          if not (substitutible t bound) then None else Some t
      | Var x -> Some (Var x)
      | Const e -> Some (Const e)
      | Fun (f, ts) ->
          let* ts' =
            List.fold_left
              (fun acc t ->
                let* ts' = acc in
                let* t' = aux_term bound t in
                Some (t' :: ts'))
              (Some []) ts
          in
          Some (Fun (f, List.rev ts'))
    in
    let rec aux bound = function
      | Atom (p, ts) ->
          let* ts' =
            List.fold_left
              (fun acc t ->
                let* ts' = acc in
                let* t' = aux_term bound t in
                Some (t' :: ts'))
              (Some []) ts
          in
          Some (Atom (p, List.rev ts'))
      | Neg a ->
          let* a' = aux bound a in
          Some (Neg a')
      | Disj (a, b) ->
          let* a' = aux bound a in
          let* b' = aux bound b in
          Some (Disj (a', b'))
      | Exists (x, a) ->
          let* a' = aux (VS.add x bound) a in
          Some (Exists (x, a'))
    in
    aux VS.empty a

  let variant a x y =
    let module VS = Set.Make (String) in
    let rec aux_term bound = function
      | Var x' when x' = x && VS.mem x bound -> Var y
      | Var x' -> Var x'
      | Const e -> Const e
      | Fun (f, ts) -> Fun (f, List.map (aux_term bound) ts)
    in
    let rec aux bound = function
      | Atom (p, ts) -> Atom (p, List.map (aux_term bound) ts)
      | Neg a -> Neg (aux bound a)
      | Disj (a, b) -> Disj (aux bound a, aux bound b)
      | Exists (x', a) -> Exists ((if x' = x then y else x'), aux (VS.add x' bound) a)
    in
    aux VS.empty a

  let is_elementary = function Atom _ | Exists _ -> true | _ -> false

  let is_free x a =
    let module VS = Set.Make (String) in
    let rec is_free_in_term bound = function
      | Var x' when x' = x && not (VS.mem x bound) -> true
      | Var _ -> false
      | Const _ -> false
      | Fun (_, ts) -> List.exists (is_free_in_term bound) ts
    in
    let rec aux bound = function
      | Atom (_, ts) -> List.exists (is_free_in_term bound) ts
      | Neg a -> aux bound a
      | Disj (a, b) -> aux bound a || aux bound b
      | Exists (x', a) -> aux (VS.add x' bound) a
    in
    aux VS.empty a

  let rec is_open = function
    | Atom _ -> true
    | Neg a -> is_open a
    | Disj (a, b) -> is_open a && is_open b
    | Exists _ -> false

  let is_closed a =
    let free, _ = variable_occurrences a in
    free = []

  let is_instance a' a =
    let module VS = Set.Make (String) in
    let open Util.OptionUtil in
    let is_var_instance s a' x =
      match List.assoc_opt x s with Some a when a' = a -> Some s | None -> Some ((x, a') :: s) | _ -> None
    in
    let rec is_term_instance bound s a' a =
      match (a', a) with
      | _, Var x when VS.mem x bound -> if a' = Var x then Some s else None
      | _, Var x -> is_var_instance s a' x
      | Const e', Const e when e' = e -> Some s
      | Fun (f', ts'), Fun (f, ts) when f' = f && List.length ts' = List.length ts ->
          List.fold_left
            (fun sopt (t', t) ->
              let* s = sopt in
              let* s = is_term_instance bound s t' t in
              Some s)
            (Some s) (List.combine ts' ts)
      | _ -> None
    in
    let rec is_formula_instance bound s a' a =
      match (a', a) with
      | Atom (p', ts'), Atom (p, ts) when p' = p && List.length ts' = List.length ts ->
          List.fold_left
            (fun sopt (t', t) ->
              let* s = sopt in
              let* s = is_term_instance bound s t' t in
              Some s)
            (Some s) (List.combine ts' ts)
      | Neg b', Neg b -> is_formula_instance bound s b' b
      | Disj (b', c'), Disj (b, c) ->
          let* s = is_formula_instance bound s b' b in
          let* s = is_formula_instance bound s c' c in
          Some s
      | Exists (x', b'), Exists (x, b) when x' = x -> is_formula_instance (VS.add x bound) s b' b
      | _ -> None
    in
    let* s = is_formula_instance VS.empty [] a' a in
    (* Remove identity substitutions and sort result lexicographically *)
    let nid = List.filter (fun (x, t) -> not (t = Var x)) s in
    Some (List.sort (fun (x', _) (x, _) -> Stdlib.compare x' x) nid)

  let rec height = function
    | Atom _ -> 0
    | Neg a -> 1 + height a
    | Disj (a, b) -> 1 + height a + height b
    | Exists (_, a) -> 1 + height a

  let closure a =
    let free, _ = variable_occurrences a in
    let sorted = List.sort String.compare free in
    List.fold_left (Fun.flip forall) a (List.rev sorted)

  (*
    Disambiguate variable names in the given formula by applying the
    provided function (usually, [substitute] or [variant] depending
    on whether free or bound variables, respectively, are the goal).
    Fresh variables are introduced by adding primes (') to existing 
    variable names.
 *)
  let disambiguate a xs forbidden0 sub_fn =
    let module VS = Set.Make (String) in
    let rec fresh_name x forbidden cnt =
      let psuffix = String.init cnt (fun _ -> '\'') in
      let x' = Printf.sprintf "%s%s" x psuffix in
      if VS.mem x' forbidden then fresh_name x forbidden (cnt + 1) else x'
    in
    let a', _ =
      List.fold_left
        (fun (a, forbidden) x ->
          if VS.mem x forbidden then
            let x' = fresh_name x forbidden 1 in
            (sub_fn a x x', forbidden |> VS.add x')
          else (a, forbidden))
        (a, VS.of_list forbidden0)
        xs
    in
    a'

  (*
  let disambiguate_free a forbidden =
    let free, _ = variable_occurrences a in
    let sub_fn a x x' = substitute a x (Var x') in
    disambiguate a free forbidden sub_fn
  *)

  let disambiguate_bound a forbidden =
    let _, bound = variable_occurrences a in
    disambiguate a bound forbidden variant

  let rec prenex =
    (* Operation (a) is applied by [disambiguate] *)
    (* Operation (b): replace ¬∃xB by ∀x¬B or ¬∀xB by ∃x¬B. *)
    let rec op_b = function
      | Neg (Exists (x, b)) -> forall x (Neg (op_b b))
      | Neg (Neg (Exists (x, b))) -> Exists (x, Neg (op_b b))
      | b -> b
    in
    (*
      Operations (c) and (d):
        (c) Replace QxB ∨ C by Qx(B ∨ C), if x is not free in C.
        (d) Replace B ∨ QxC by Qx(B ∨ C), if x is not free in B.
    *)
    let rec op_cd = function
      | Disj (Exists (x, b), c) -> Exists (x, op_cd (Disj (b, c)))
      | Disj (Neg (Exists (x, Neg b)), c) -> Neg (Exists (x, Neg (op_cd (Disj (b, c)))))
      | Disj (b, Exists (x, c)) -> Exists (x, op_cd (Disj (b, c)))
      | Disj (b, Neg (Exists (x, Neg c))) -> Neg (Exists (x, Neg (op_cd (Disj (b, c)))))
      | a -> a
    in
    function
    | Atom _ as a -> a
    | Exists (x, b) ->
        let b' = disambiguate_bound (prenex b) [ x ] in
        Exists (x, b')
    | Neg (Exists (x, Neg b)) ->
        let b' = disambiguate_bound (prenex b) [ x ] in
        Neg (Exists (x, Neg b'))
    | Neg b ->
        let b' = prenex b in
        op_b (Neg b')
    | Disj (b, c) ->
        let b', c' = (prenex b, prenex c) in
        let free_b, _ = variable_occurrences b' in
        let free_c, bound_c = variable_occurrences c' in
        let free = free_b @ free_c in
        let b' = disambiguate_bound b' (free @ bound_c) in
        let _, bound_b = variable_occurrences b' in
        let c' = disambiguate_bound c' (free @ bound_b) in
        op_cd (Disj (b', c'))

  let rec collect_elementary acc = function
    | Atom _ as a' -> acc |> FormulaSet.add a'
    | Exists _ as a' -> acc |> FormulaSet.add a'
    | Neg a' -> collect_elementary acc a'
    | Disj (a', b') -> collect_elementary (collect_elementary acc a') b'

  (*
    This simply tries all truth valuations over the set of elementary
    formulas of the given formula, so it's very inefficient for 
    formulas with lots of distinct elementary formulas. However, it's
    useful for smaller formulas and for testing/verification purposes.
  *)
  let is_tautology a =
    (* Collect elementary formulas *)
    let elem = collect_elementary FormulaSet.empty a in
    (* Try every valuation over the set of elementary formulas *)
    let rec aux mapping = function
      | [] ->
          let rec v = function
            | Neg a' -> not (v a')
            | Disj (a', b') -> v a' || v b'
            | a' -> FormulaMap.find a' mapping
          in
          v a
      | e :: es -> aux (mapping |> FormulaMap.add e true) es && aux (mapping |> FormulaMap.add e false) es
    in
    aux FormulaMap.empty (List.of_seq (FormulaSet.to_seq elem))

  let is_tautological_consequence bs a = is_tautology (impl_of_list (bs @ [ a ]))

  let herbrandize a =
    let module FS = Set.Make (String) in
    let rec collect_term_function_symbols = function
      | Var _ -> FS.empty
      | Const _ -> FS.empty
      | Fun (f, ts) -> List.fold_left (fun acc t -> FS.union acc (collect_term_function_symbols t)) (FS.singleton f) ts
    in
    let rec collect_formula_function_symbols = function
      | Atom (_, ts) -> List.fold_left (fun acc t -> FS.union acc (collect_term_function_symbols t)) FS.empty ts
      | Neg b -> collect_formula_function_symbols b
      | Disj (b, c) -> FS.union (collect_formula_function_symbols b) (collect_formula_function_symbols c)
      | Exists (_, b) -> collect_formula_function_symbols b
    in
    let a' = prenex (closure a) in
    let fs = collect_formula_function_symbols a' in
    let rec reduce_nonexistential_matrix xs k = function
      | Exists (x, b) ->
          let b', k' = reduce_nonexistential_matrix (x :: xs) k b in
          (Exists (x, b'), k')
      | Neg (Exists (y, Neg b)) as c ->
          let f = Printf.sprintf "f%d" k in
          if FS.mem f fs then reduce_nonexistential_matrix xs (k + 1) c
          else
            let t = match xs with [] -> Const f | _ -> Fun (f, List.map (fun x -> Var x) (List.rev xs)) in
            reduce_nonexistential_matrix xs (k + 1) (substitute b [ (y, t) ])
      | b -> (b, k)
    in
    let res, _ = reduce_nonexistential_matrix [] 0 a' in
    res
end
