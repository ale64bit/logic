open Fol

(* Predicate calculus for first-order logic as described in Shoenfield's "Mathematical Logic" *)
module Calculus : sig
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

  (* Rules of the system *)
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
end

(* Some metatheorems handy in proving other results *)
module Meta : sig
  open Calculus

  val neg_neg : proof -> formula -> conclusion
  (* A ⊢ ¬¬A *)

  val commute : proof -> formula -> conclusion
  (* A ∨ B ⊢ B ∨ A *)

  val modus_ponens : proof -> formula -> formula -> conclusion
  (* {A, A → B} ⊢ B *)

  val disj_neg_neg : proof -> formula -> conclusion
  (* A ∨ B ⊢ ¬¬A ∨ B *)

  val disj_contraction : proof -> formula -> conclusion
  (* A ∨ (B ∨ B) ⊢ A ∨ B *)

  val associative_right : proof -> formula -> conclusion
  (* (A ∨ B) ∨ C ⊢ A ∨ (B ∨ C) *)

  val general_expansion : proof -> formula list -> formula list -> conclusion
  (* If ⊢ Ai1 ∨ ... ∨ Aim and {Ai1, ... , Aim} is a subset of {A1, ... , An}, then ⊢ A1 ∨ ... ∨ An *)
end

val print_proof : out_channel -> Calculus.proof -> unit
(* Prints a proof in human-readable format to an output channel *)

val print_proof_tex : out_channel -> Calculus.proof -> unit
(* Prints a proof in TeX format to an output channel *)
