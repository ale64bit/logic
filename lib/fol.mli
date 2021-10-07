(* Types representing first-order formulas *)
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

(* Defined symbols to facilitate writing more complex formulas *)
module Defined : sig
  val conj : formula -> formula -> formula

  val impl : formula -> formula -> formula

  val eq : formula -> formula -> formula

  val forall : var -> formula -> formula

  (* Operator aliases for human-readability *)
  module Operators : sig
    val ( ! ) : formula -> formula

    val ( || ) : formula -> formula -> formula

    val ( && ) : formula -> formula -> formula

    val ( => ) : formula -> formula -> formula

    val ( <=> ) : formula -> formula -> formula
  end
end

type valuation = formula -> bool
(* A truth valuation *)

val disj_of_list : formula list -> formula
(* Converts a list of formulas [A1; ...; An] to a disjunction formula (A1 ∨ ... ∨ An) *)

val list_of_disj : formula -> formula list
(* Converts a disjunction formula (A1 ∨ ... ∨ An) to a list of formulas [A1; ...; An] *)

val substitute : formula -> var -> term -> formula
(* Substitutes a variable free occurrences by a term in the given formula *)

val variant : formula -> var -> var -> formula
(* Computes a variant of the given formula by substituting all bound occurrences of a variable by another. *)

val is_elementary : formula -> bool
(* Checks whether a formula is elementary, i.e. whether it is an atomic formula or an instantiation *)

val is_free : var -> formula -> bool
(* Checks whether a variable is free in the given formula *)

val is_open : formula -> bool
(* Checks whether a formula is quantifier-free *)

val variables : formula -> var list * var list
(*
    Computes the list of free and bound variable occurrences in a formula.
    Each variable appears at most once in each list.
*)

val is_closed : formula -> bool
(* Checks whether a formula is closed, i.e. contains no free variable occurrences *)

val closure : formula -> formula
(* Computes the closure of a formula by universally quantifying each free variable in alphabetical order *)

val is_instance : formula -> formula -> (var * term) list * bool
(* [is_instance a' a] tests whether formula a' is an instance of formula a *)

val prenex : formula -> formula
(* Converts a formula into an equivalent formula in prenex form. *)

val is_tautology : formula -> bool
(* [is_tautology a] tests whether formula a is a tautology *)

val formula_of_tptp : Tptp.formula -> formula
(* Converts a formula in TPTP format into the internal format *)

val string_of_term : term -> string
(* Converts a term to a human-readable string *)

val string_of_formula : ?top:bool -> formula -> string
(* Converts a formula to a human-readable string *)

val extended_string_of_formula : ?top:bool -> formula -> string
(* Converts a formula to a human-readable string with additional defined symbols *)

val tex_of_formula :
  ?top:bool -> ?fmap:(formula -> string option) -> formula -> string
(* Converts a formula to a TeX string *)
