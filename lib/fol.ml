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

let substitute x t a =
  let rec subs_term bound = function
    | Var x' when x' = x && not (StringSet.mem x bound) -> t
    | Var x' -> Var x'
    | Const e -> Const e
    | Fun (f, ts) -> Fun (f, List.map (subs_term bound) ts)
  in
  let rec aux bound = function
    | Atom (p, ts) -> Atom (p, List.map (subs_term bound) ts)
    | Neg a -> Neg (aux bound a)
    | Or (a, b) -> Or (aux bound a, aux bound b)
    | Exists (x', a) -> aux (StringSet.add x' bound) a
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

let rec is_quantifier_free = function
  | Atom _ -> true
  | Neg a -> is_quantifier_free a
  | Or (a, b) -> is_quantifier_free a && is_quantifier_free b
  | Exists _ -> false

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

let is_closed a =
  let free, _ = variables a in
  free = []

let closure a =
  let free, _ = variables a in
  List.fold_left (Fun.flip Defined.forall) a free

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
