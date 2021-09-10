type var = string

type pred = string

type func = string

type const = string

type term = Var of var | Const of const | Fun of func * term list

type atom = pred * term list

type formula =
  | Atom of atom
  | Neg of formula
  | Or of formula * formula
  | Exists of var * formula

module Defined = struct
  let conj a b = Neg (Or (Neg a, Neg b))

  let impl a b = Or (Neg a, b)

  let eq a b = conj (impl a b) (impl b a)

  let forall x a = Neg (Exists (x, Neg a))

  module Operators = struct
    let ( ! ) a = Neg a

    let ( || ) a b = Or (a, b)

    let ( && ) = conj

    let ( => ) = impl

    let ( <=> ) = eq
  end
end

module StringSet = Set.Make (String)

let rec disj_of_list = function
  | [] -> failwith "impossible: empty list"
  | [ a ] -> a
  | a :: xs -> Or (a, disj_of_list xs)

let list_of_disj a =
  let rec aux acc = function
    | Or (a', b') -> aux (a' :: acc) b'
    | a' -> a' :: acc
  in
  List.rev (aux [] a)

let variables a =
  let open StringSet in
  let rec aux_term bound = function
    | Var x -> if mem x bound then (empty, singleton x) else (singleton x, empty)
    | Const _ -> (empty, empty)
    | Fun (_, ts) ->
        List.fold_left
          (fun (free_acc, bound_acc) t ->
            let free_t, bound_t = aux_term bound t in
            (union free_acc free_t, union bound_acc bound_t))
          (empty, empty) ts
  in
  let rec aux bound = function
    | Atom (_, ts) ->
        List.fold_left
          (fun (free_acc, bound_acc) t ->
            let free_t, bound_t = aux_term bound t in
            (union free_acc free_t, union bound_acc bound_t))
          (empty, empty) ts
    | Neg a -> aux bound a
    | Or (a, b) ->
        let free_a, bound_a = aux bound a in
        let free_b, bound_b = aux bound b in
        (union free_a free_b, union bound_a bound_b)
    | Exists (x, a) -> aux (add x bound) a
  in
  let free, bound = aux empty a in
  (List.of_seq (to_seq free), List.of_seq (to_seq bound))

let substitute a x t =
  let free, _ = variables (Atom ("", [ t ])) in
  let substitutible bound =
    List.for_all (fun y -> not (StringSet.mem y bound)) free
  in
  let rec aux_term bound = function
    | Var x' when x' = x && not (StringSet.mem x bound) ->
        assert (substitutible bound);
        t
    | Var x' -> Var x'
    | Const e -> Const e
    | Fun (f, ts) -> Fun (f, List.map (aux_term bound) ts)
  in
  let rec aux bound = function
    | Atom (p, ts) -> Atom (p, List.map (aux_term bound) ts)
    | Neg a -> Neg (aux bound a)
    | Or (a, b) -> Or (aux bound a, aux bound b)
    | Exists (x', a) -> Exists (x', aux (StringSet.add x' bound) a)
  in
  aux StringSet.empty a

let variant a x y =
  let rec aux_term bound = function
    | Var x' when x' = x && StringSet.mem x bound -> Var y
    | Var x' -> Var x'
    | Const e -> Const e
    | Fun (f, ts) -> Fun (f, List.map (aux_term bound) ts)
  in
  let rec aux bound = function
    | Atom (p, ts) -> Atom (p, List.map (aux_term bound) ts)
    | Neg a -> Neg (aux bound a)
    | Or (a, b) -> Or (aux bound a, aux bound b)
    | Exists (x', a) ->
        Exists ((if x' = x then y else x'), aux (StringSet.add x' bound) a)
  in
  aux StringSet.empty a

let is_elementary = function Atom _ | Exists _ -> true | _ -> false

let is_free x a =
  let rec is_free_in_term bound = function
    | Var x' when x' = x && not (StringSet.mem x bound) -> true
    | Var _ -> false
    | Const _ -> false
    | Fun (_, ts) -> List.exists (is_free_in_term bound) ts
  in
  let rec aux bound = function
    | Atom (_, ts) -> List.exists (is_free_in_term bound) ts
    | Neg a -> aux bound a
    | Or (a, b) -> aux bound a || aux bound b
    | Exists (x', a) -> aux (StringSet.add x' bound) a
  in
  aux StringSet.empty a

let rec is_open = function
  | Atom _ -> true
  | Neg a -> is_open a
  | Or (a, b) -> is_open a && is_open b
  | Exists _ -> false

let is_closed a =
  let free, _ = variables a in
  free = []

let closure a =
  let free, _ = variables a in
  let sorted = List.sort String.compare free in
  List.fold_left (Fun.flip Defined.forall) a (List.rev sorted)

let is_instance a' a =
  let is_var_instance m a' x =
    match List.assoc_opt x m with
    | Some a -> (m, a' = a)
    | None -> ((x, a') :: m, true)
  in
  let rec is_term_instance m a' a =
    match (a', a) with
    | _, Var x -> is_var_instance m a' x
    | Const e', Const e -> (m, e' = e)
    | Fun (f', ts'), Fun (f, ts) when List.length ts' = List.length ts ->
        List.fold_left
          (fun (m, acc) (t', t) ->
            let m, res = is_term_instance m t' t in
            (m, acc && res))
          (m, f' = f)
          (List.combine ts' ts)
    | _ -> (m, false)
  in
  let rec is_formula_instance m a' a =
    match (a', a) with
    | Atom (p', ts'), Atom (p, ts) when List.length ts' = List.length ts ->
        List.fold_left
          (fun (m, acc) (t', t) ->
            let m, res = is_term_instance m t' t in
            (m, acc && res))
          (m, p' = p)
          (List.combine ts' ts)
    | Neg b', Neg b -> is_formula_instance m b' b
    | Or (b', c'), Or (b, c) ->
        let m, resb = is_formula_instance m b' b in
        let m, resc = is_formula_instance m c' c in
        (m, resb && resc)
    | Exists (x', b'), Exists (x, b) when x' = x -> is_formula_instance m b' b
    | _ -> (m, false)
  in
  let m, res = is_formula_instance [] a' a in
  if res then
    let nid = List.filter (fun (x, t) -> not (t = Var x)) m in
    (List.sort (fun (x', _) (x, _) -> Stdlib.compare x' x) nid, res)
  else ([], false)

(*
    Disambiguate variable names in the given formula by applying the
    provided function (usually, [substitute] or [variant] depending
    on whether free or bound variables, respectively, are the goal).
    Fresh variables are introduced by adding primes (') to existing 
    variable names.
 *)
let disambiguate a xs forbidden0 sub_fn =
  let rec fresh_name x forbidden cnt =
    let psuffix = String.init cnt (fun _ -> '\'') in
    let x' = Printf.sprintf "%s%s" x psuffix in
    if StringSet.mem x' forbidden then fresh_name x forbidden (cnt + 1) else x'
  in
  let a', _ =
    List.fold_left
      (fun (a, forbidden) x ->
        if StringSet.mem x forbidden then
          let x' = fresh_name x forbidden 1 in
          (sub_fn a x x', forbidden |> StringSet.add x')
        else (a, forbidden))
      (a, StringSet.of_list forbidden0)
      xs
  in
  a'

(*
let disambiguate_free a forbidden =
  let free, _ = variables a in
  let sub_fn a x x' = substitute a x (Var x') in
  disambiguate a free forbidden sub_fn
*)

let disambiguate_bound a forbidden =
  let _, bound = variables a in
  disambiguate a bound forbidden variant

let rec prenex =
  (* Operation (a) is applied by [disambiguate] *)
  (* Operation (b): replace ¬∃xB by ∀x¬B or ¬∀xB by ∃x¬B. *)
  let rec op_b = function
    | Neg (Exists (x, b)) -> Defined.forall x (Neg (op_b b))
    | Neg (Neg (Exists (x, b))) -> Exists (x, Neg (op_b b))
    | b -> b
  in
  (*
      Operations (c) and (d):
        (c) Replace QxB ∨ C by Qx(B ∨ C), if x is not free in C.
        (d) Replace B ∨ QxC by Qx(B ∨ C), if x is not free in B.
  *)
  let rec op_cd = function
    | Or (Exists (x, b), c) -> Exists (x, op_cd (Or (b, c)))
    | Or (Neg (Exists (x, Neg b)), c) ->
        Neg (Exists (x, Neg (op_cd (Or (b, c)))))
    | Or (b, Exists (x, c)) -> Exists (x, op_cd (Or (b, c)))
    | Or (b, Neg (Exists (x, Neg c))) ->
        Neg (Exists (x, Neg (op_cd (Or (b, c)))))
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
  | Or (b, c) ->
      let b', c' = (prenex b, prenex c) in
      let free_b, _ = variables b' in
      let free_c, bound_c = variables c' in
      let free = free_b @ free_c in
      let b' = disambiguate_bound b' (free @ bound_c) in
      let _, bound_b = variables b' in
      let c' = disambiguate_bound c' (free @ bound_b) in
      op_cd (Or (b', c'))

let rec term_of_tptp = function
  | Tptp.Var x -> Var x
  | Tptp.Const e -> Const e
  | Tptp.Fun (f, ts) -> Fun (f, List.map term_of_tptp ts)

let rec formula_of_tptp = function
  | Tptp.Atom (p, ts) -> Atom (p, List.map term_of_tptp ts)
  | Tptp.Impl (a, b) -> Or (Neg (formula_of_tptp a), formula_of_tptp b)
  | Tptp.DImpl (a, b) ->
      Neg
        (Or
           ( Neg (Or (Neg (formula_of_tptp a), formula_of_tptp b)),
             Neg (Or (Neg (formula_of_tptp b), formula_of_tptp a)) ))
  | Tptp.Neg a -> Neg (formula_of_tptp a)
  | Tptp.Or (a, b) -> Or (formula_of_tptp a, formula_of_tptp b)
  | Tptp.And (a, b) ->
      Neg (Or (Neg (formula_of_tptp a), Neg (formula_of_tptp b)))
  | Tptp.ForAll (xs, a) ->
      formula_of_tptp (Tptp.Neg (Tptp.Exists (xs, Tptp.Neg a)))
  | Tptp.Exists (xs, a) ->
      List.fold_left (fun acc x -> Exists (x, acc)) (formula_of_tptp a) xs

let rec string_of_term = function
  | Var x -> x
  | Const e -> e
  | Fun (f, ts) ->
      Printf.sprintf "%s(%s)" f
        (String.concat ", " (List.map string_of_term ts))

let rec string_of_formula ?(top = true) = function
  | Atom ("=", [ lhs; rhs ]) ->
      Printf.sprintf "(%s = %s)" (string_of_term lhs) (string_of_term rhs)
  | Atom (p, ts) ->
      Printf.sprintf "%s(%s)" p
        (String.concat ", " (List.map string_of_term ts))
  | Neg a -> Printf.sprintf "¬%s" (string_of_formula ~top:false a)
  | Or (a, b) ->
      let s =
        Printf.sprintf "%s ∨ %s"
          (string_of_formula ~top:false a)
          (string_of_formula ~top:false b)
      in
      if top then s else Printf.sprintf "(%s)" s
  | Exists (x, f) ->
      Printf.sprintf "%s %s" (Printf.sprintf "∃%s" x)
        (string_of_formula ~top:false f)

let rec tex_of_formula ?(top = true) ?(fmap = fun _ -> None) a =
  match fmap a with
  | Some s -> s
  | None -> (
      match a with
      | Atom ("=", [ lhs; rhs ]) ->
          Printf.sprintf "(%s = %s)" (string_of_term lhs) (string_of_term rhs)
      | Atom (p, ts) ->
          Printf.sprintf "%s(%s)" p
            (String.concat ", " (List.map string_of_term ts))
      | Neg a -> Printf.sprintf "\\neg %s" (tex_of_formula ~top:false ~fmap a)
      | Or (a, b) ->
          let s =
            Printf.sprintf "%s \\lor %s"
              (tex_of_formula ~top:false ~fmap a)
              (tex_of_formula ~top:false ~fmap b)
          in
          if top then s else Printf.sprintf "(%s)" s
      | Exists (x, f) ->
          Printf.sprintf "%s %s"
            (Printf.sprintf "\\exists %s" x)
            (tex_of_formula ~top:false ~fmap f))
