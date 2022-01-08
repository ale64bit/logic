open Fol

module Base : sig
  type proof_line

  type proof

  val empty_proof : proof

  val proof_length : proof -> int

  type conclusion = (proof * formula, string) result
  (*
      The result of a proof step, consisting of the proof context so far and
      the consequence formula of the step, or an error message indicating why
      the proof is invalid.
  *)

  val premise : proof -> formula -> conclusion
  (* Adds a formula to a proof as a premise *)

  val ( let* ) : conclusion -> (proof * formula -> conclusion) -> conclusion
  (* Monadic bind to compose proofs *)

  val proves : proof -> formula -> conclusion
  (* Readability function to conclude proofs *)

  val already_proven : proof -> formula -> bool
  (* Checks if a formula is already derived in current context *)
end

(* Predicate calculus for first-order logic as described in Shoenfield's "Mathematical Logic", Chapter 2 *)
module Calculus : sig
  open Base

  (* Logical axioms of the system *)
  module Axiom : sig
    val propositional : proof -> formula -> conclusion
    (* ¬A ∨ A *)

    val substitution : proof -> formula -> var -> term -> conclusion
    (* A[a] → ∃xA *)

    val identity : proof -> var -> conclusion
    (* x = x *)

    val fequality : proof -> (var * var) list -> func -> conclusion
    (* (x1 = y1) → ... → (xn = yn) → (f(x1, ... , xn) = f(y1, ..., yn)) *)

    val pequality : proof -> (var * var) list -> pred -> conclusion
    (* (x1 = y1) → ... → (xn = yn) → p(x1, ..., xn) → p(y1, ..., yn) *)
  end

  (* Rules of inference *)
  module Rule : sig
    val expansion : proof -> formula -> formula -> conclusion
    (* Infer B ∨ A from A *)

    val contraction : proof -> formula -> conclusion
    (* Infer A from A ∨ A *)

    val associative : proof -> formula -> conclusion
    (* Infer (A ∨ B) ∨ C from A ∨ (B ∨ C) *)

    val cut : proof -> formula -> formula -> conclusion
    (* Infer B ∨ C from A ∨ B and ¬A ∨ C *)

    val e_introduction : proof -> var -> formula -> conclusion
    (* Infer ∃xA → B from A → B if x is not free in B *)
  end

  val random_theorem :
    ?max_steps:int ->
    ?variables:var list ->
    ?predicates:(pred * int) list ->
    ?functions:(func * int) list ->
    ?constants:const list ->
    ?non_logical_axioms:(unit -> formula) list ->
    Random.State.t ->
    formula
end

(* Variant of predicate calculus for first-order logic as described in Shoenfield's "Mathematical Logic", Section 3.1 *)
module TautCalculus : sig
  open Base

  (* Logical axioms of the system *)
  module Axiom : sig
    val substitution : proof -> formula -> var -> term -> conclusion
    (* A[a] → ∃xA *)

    val identity : proof -> var -> conclusion
    (* x = x *)

    val fequality : proof -> (var * var) list -> func -> conclusion
    (* (x1 = y1) → ... → (xn = yn) → (f(x1, ... , xn) = f(y1, ..., yn)) *)

    val pequality : proof -> (var * var) list -> pred -> conclusion
    (* (x1 = y1) → ... → (xn = yn) → p(x1, ..., xn) → p(y1, ..., yn) *)
  end

  (* Rules of inference *)
  module Rule : sig
    val tautological_consequence :
      proof -> formula list -> formula -> conclusion
    (*
        Infer A from B1, ... ,Bn if A is a tautological consequence of B1, ... , Bn
        and ⊢ B1, ... , ⊢ Bn.
    *)

    val e_introduction : proof -> var -> formula -> conclusion
    (* Infer ∃xA → B from A → B if x is not free in B *)
  end
end

(* Some metatheorems handy in proving other results *)
module Meta : sig
  open Base

  val commute : proof -> formula -> conclusion
  (* A ∨ B ⊢ B ∨ A *)

  val detachment : proof -> formula -> formula -> conclusion
  (* {A, A → B} ⊢ B *)

  val conj : proof -> formula -> formula -> conclusion
  (* {A, B} ⊢ A ∧ B *)

  val dneg_intro : proof -> formula -> conclusion
  (* A ⊢ ¬¬A *)

  val dneg_elim : proof -> formula -> conclusion
  (* ¬¬A ⊢ A *)

  val disj_dneg : proof -> formula -> conclusion
  (* A ∨ B ⊢ ¬¬A ∨ B *)

  val disj_contraction : proof -> formula -> conclusion
  (* A ∨ (B ∨ B) ⊢ A ∨ B *)

  val associative_right : proof -> formula -> conclusion
  (* (A ∨ B) ∨ C ⊢ A ∨ (B ∨ C) *)

  val general_expansion : proof -> formula list -> formula list -> conclusion
  (* If ⊢ Ai1 ∨ ... ∨ Aim and {Ai1, ... , Aim} is a subset of {A1, ... , An}, then ⊢ A1 ∨ ... ∨ An *)

  val rev_impl : proof -> formula -> conclusion
  (* A → B ⊢ ¬B → ¬A *)

  val a_introduction : proof -> var -> formula -> conclusion
  (* A → B ⊢ A → ∀xB, if x is not free in A *)

  val generalization : proof -> var -> formula -> conclusion
  (* A ⊢ ∀xA *)

  val substitution : proof -> formula -> formula -> conclusion
  (* A ⊢ A' where A' is an instance of A *)

  val detachment_transitivity : proof -> formula -> formula -> conclusion
  (* {A → B, B → C} ⊢ A → C *)

  val e_distribution : proof -> var -> formula -> conclusion
  (* A → B ⊢ ∃xA → ∃xB *)

  val a_distribution : proof -> var -> formula -> conclusion
  (* A → B ⊢ ∀xA → ∀xB *)

  val witness : proof -> var -> term -> conclusion
  (* [witness x a] produces a proof of ∃x(x = a) *)
end

val print_proof : out_channel -> Base.proof -> unit
(* Prints a proof in human-readable format to an output channel *)

val print_proof_tex :
  ?fmap:(formula -> string option) -> out_channel -> Base.proof -> unit
(* Prints a proof in TeX format to an output channel *)
