open Core

module Repr : sig
  type term = Var of string | Const of string | Fun of string * term list
  type formula = Atom of string * term list | Neg of formula | Disj of formula * formula | Exists of string * formula
end

module S : FirstOrderLanguage.S with type term = Repr.term and type formula = Repr.formula

module Syntax : functor (L : FirstOrderLanguage.S with type term = S.term and type formula = S.formula) -> sig
  open L
  module FormulaSet : Set.S with type elt = formula
  module FormulaMap : Map.S with type key = formula

  type var = string
  type substitution = (var * term) list

  val exists_seq : var list -> formula -> formula
  (* [exists_seq xs a] builds an existential formula ∃x1 ... ∃xn A from variables [xs] and formula [a] *)

  val forall_seq : var list -> formula -> formula
  (* [forall_seq xs a] builds a universal formula ∀x1 ... ∀xn A from variables [xs] and formula [a] *)

  val string_of_term : term -> string
  (* [string_of_term t] converts a term [t] to a human-readable string *)

  val string_of_formula : formula -> string
  (* [string_of_formula a] converts a formula [a] to a human-readable string *)

  val extended_string_of_formula : formula -> string
  (* [extended_string_of_formula a] converts a formula [a] to a human-readable string with additional defined symbols *)

  val tex_of_formula : ?fmap:(formula -> string option) -> formula -> string
  (** [tex_of_formula a] converts formula [a] to a TeX string.
      The optional [fmap] can be used to render specific subformulas differently.
   *)

  val string_of_substitution : substitution -> string
  (* [string_of_substitution s] converts a substitution [s] to a human-readable string *)

  val disj_of_list : formula list -> formula
  (* Converts a list of formulas [A1; ...; An] to a disjunction (A1 ∨ ... ∨ An) *)

  val list_of_disj : formula -> formula list
  (* Converts a disjunction (A1 ∨ ... ∨ An) to a list of formulas [A1; ...; An] *)

  val impl_of_list : formula list -> formula
  (* Converts a list of formulas [A1; ...; An] to an implication (A1 → ... → An) *)

  val variable_occurrences : formula -> var list * var list
  (*
    [variable_occurrences a] computes the list of free and bound variable occurrences in formula [a].
    Each variable appears at most once in each list.
  *)

  val gen_fresh_vars : int -> formula list -> var list
  (* [gen_fresh_vars n bs] generates [n] variables not occurring free or bound in any of the formulas [bs] *)

  val substitute : formula -> substitution -> formula
  (* [substitute a s] substitutes the free occurrences of variables in [s] with the corresponding term
     in the given formula [a].
  *)

  val substitute_opt : formula -> substitution -> formula option
  (* Like [substitute a s] but returns None if the terms are not substitutible *)

  val variant : formula -> var -> var -> formula
  (* [variant a x y] computes a variant of formula [a] by substituting all bound occurrences of variable [x] with variable [y]. *)

  val is_elementary : formula -> bool
  (* [is_elementary a] checks whether formula [a] is elementary, i.e. whether it is an atomic formula or an instantiation *)

  val is_free : var -> formula -> bool
  (* [is_free x a] checks whether variable [x] is free in formula [a] *)

  val is_open : formula -> bool
  (* [is_open a] checks whether formula [a] is quantifier-free *)

  val is_closed : formula -> bool
  (* [is_closed a] checks whether formula [a] is closed, i.e. contains no free variable occurrences *)

  val is_instance : formula -> formula -> substitution option
  (* [is_instance a' a] tests whether formula [a'] is an instance of formula [a] and returns a substitution
     to transform [a] into [a'].
  *)

  val height : formula -> int
  (* [height a] computes the height of formula [a] *)

  val closure : formula -> formula
  (* [closure a] computes the closure of formula [a] by universally quantifying each free variable in alphabetical order *)

  val prenex : formula -> formula
  (* [prenex a] converts formula [a] into an equivalent formula in prenex form *)

  val is_tautology : formula -> bool
  (* [is_tautology a] tests whether formula [a] is a tautology *)

  val is_tautological_consequence : formula list -> formula -> bool
  (* [is_tautological_consequence bs a] tests whether formula [a] is a tautological consequence of formulas [bs] *)

  val herbrandize : formula -> formula
  (* [herbrandize a] computes the Herbrandization of formula [a] *)
end
