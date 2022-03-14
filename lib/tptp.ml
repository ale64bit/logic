type var = string
type pred = string
type func = string
type const = string
type term = Var of var | Const of const | Fun of func * term list
type atom = pred * term list

type formula =
  | Atom of atom
  | Impl of formula * formula
  | DImpl of formula * formula
  | Neg of formula
  | Or of formula * formula
  | And of formula * formula
  | ForAll of var list * formula
  | Exists of var list * formula

type role = Axiom | Hypothesis | Conjecture
type fof = { name : string; role : role; formula : formula }

let string_of_role = function
  | Axiom -> "axiom"
  | Hypothesis -> "hypothesis"
  | Conjecture -> "conjecture"

let rec string_of_term = function
  | Var x -> x
  | Const e -> e
  | Fun (f, ts) ->
      Printf.sprintf "%s(%s)" f
        (String.concat ", " (List.map string_of_term ts))

let rec string_of_formula = function
  | Atom ("=", [ lhs; rhs ]) ->
      Printf.sprintf "%s = %s" (string_of_term lhs) (string_of_term rhs)
  | Atom (p, ts) ->
      Printf.sprintf "%s(%s)" p
        (String.concat ", " (List.map string_of_term ts))
  | Impl (lhs, rhs) ->
      Printf.sprintf "(%s → %s)" (string_of_formula lhs) (string_of_formula rhs)
  | DImpl (lhs, rhs) ->
      Printf.sprintf "(%s ↔ %s)" (string_of_formula lhs) (string_of_formula rhs)
  | Or (lhs, rhs) ->
      Printf.sprintf "(%s ∨ %s)" (string_of_formula lhs) (string_of_formula rhs)
  | And (lhs, rhs) ->
      Printf.sprintf "(%s ∧ %s)" (string_of_formula lhs) (string_of_formula rhs)
  | Neg rhs -> Printf.sprintf "¬%s" (string_of_formula rhs)
  | ForAll (xs, f) ->
      Printf.sprintf "%s %s"
        (String.concat " " (List.map (Printf.sprintf "∀%s") xs))
        (string_of_formula f)
  | Exists (xs, f) ->
      Printf.sprintf "%s %s"
        (String.concat " " (List.map (Printf.sprintf "∃%s") xs))
        (string_of_formula f)

let string_of_fof { name; role; formula } =
  Printf.sprintf "fof(%s, %s, %s)." name (string_of_role role)
    (string_of_formula formula)
