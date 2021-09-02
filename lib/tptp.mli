(* Types representing first-order formulas in the TPTP format *)
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

val string_of_role : role -> string

val string_of_term : term -> string

val string_of_formula : formula -> string

val string_of_fof : fof -> string
