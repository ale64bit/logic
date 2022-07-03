(*
    The base axiom system as described in Shoenfield's textbook (§2.6).
*)
module Base : sig
  include Core.System.S with type formula = Lang.Shoenfield.S.formula
  open Lang.Shoenfield.S
  open Lang.Shoenfield.Syntax(Lang.Shoenfield.S)

  val ( <<= ) : formula -> (proof -> conclusion) -> formula * (proof -> conclusion)
  val pseq : ?scope:string -> (formula * (proof -> conclusion)) list -> proof -> conclusion
  (* Combinators to aid proof writing *)

  module Axiom : sig
    val propositional : formula -> proof -> conclusion
    (* ⊢ ¬A ∨ A *)

    val substitution : formula -> var -> term -> proof -> conclusion
    (* ⊢ A[x/a] → ∃xA *)

    val identity : var -> proof -> conclusion
    (* ⊢ x = x *)

    val fequality : (var * var) list -> var -> proof -> conclusion
    (* ⊢ (x1 = y1) → ... → (xn = yn) → (f(x1, ..., xn) = f(y1, ..., yn)) *)

    val pequality : (var * var) list -> var -> proof -> conclusion
    (* ⊢ (x1 = y1) → ... → (xn = yn) → p(x1, ..., xn) → p(y1, ..., yn) *)
  end

  module Rule : sig
    val expansion : formula -> formula -> proof -> conclusion
    (* A ⊢ B ∨ A *)

    val contraction : formula -> proof -> conclusion
    (* A ∨ A ⊢ A *)

    val associative : formula -> proof -> conclusion
    (* A ∨ (B ∨ C) ⊢ (A ∨ B) ∨ C *)

    val cut : formula -> formula -> proof -> conclusion
    (* {A ∨ B, ¬A ∨ C} ⊢ B ∨ C *)

    val e_introduction : var -> formula -> proof -> conclusion
    (* A → B ⊢ ∃xA → B, with x not free in B *)
  end

  module Meta : sig
    val disj_commute : formula -> proof -> conclusion
    (* A ∨ B ⊢ B ∨ A *)

    val detachment : formula -> formula -> proof -> conclusion
    (* {A, A → B} ⊢ B *)

    val conj : formula -> formula -> proof -> conclusion
    (* {A, B} ⊢ A ∧ B *)

    val dneg_introduction : formula -> proof -> conclusion
    (* A ⊢ ¬¬A *)

    val dneg_elimination : formula -> proof -> conclusion
    (* ¬¬A ⊢ A *)

    val disj_dneg : formula -> proof -> conclusion
    (* A ∨ B ⊢ ¬¬A ∨ B *)

    val disj_contraction : formula -> proof -> conclusion
    (* A ∨ (B ∨ B) ⊢ A ∨ B *)

    val associative_right : formula -> proof -> conclusion
    (* (A ∨ B) ∨ C ⊢ A ∨ (B ∨ C) *)

    val general_expansion : formula list -> formula list -> proof -> conclusion
    (* Ai1 ∨ ... ∨ Aim ⊢ A1 ∨ ... ∨ An, with {Ai1, ... , Aim} ⊂ {A1, ... , An} *)

    val tautology_theorem : formula list -> formula -> proof -> conclusion
    (* {B1, ..., Bn} ⊢ A, with A a tautological consequence of B1, ..., Bn *)

    val contrapositive : formula -> proof -> conclusion
    (* A → B ⊢ ¬B → ¬A *)

    val a_introduction : var -> formula -> proof -> conclusion
    (* A → B ⊢ A → ∀xB, with x not free in A *)

    val generalization : var -> formula -> proof -> conclusion
    (* A ⊢ ∀xA *)

    val substitution_rule : formula -> formula -> proof -> conclusion
    (* A ⊢ A', with A' an instance of A *)

    val detachment_transitivity : formula -> formula -> proof -> conclusion
    (* {A → B, B → C} ⊢ A → C *)

    val e_distribution : var -> formula -> proof -> conclusion
    (* A → B ⊢ ∃xA → ∃xB *)

    val a_distribution : var -> formula -> proof -> conclusion
    (* A → B ⊢ ∀xA → ∀xB *)

    val witness : var -> term -> proof -> conclusion
    (* [witness x a] produces a proof of ∃x(x = a) *)

    val substitution_theorem_e : formula -> substitution -> proof -> conclusion
    (* ⊢ A[x1/t1, ..., xn/tn] → ∃x1 ... ∃xn A *)

    val substitution_theorem_a : formula -> substitution -> proof -> conclusion
    (* ⊢ ∀x1 ... ∀xn A → A[x1/t1, ..., xn/tn] *)

    val equivalence_theorem : formula -> formula -> proof -> conclusion
    (*
        (B ≡ B') ⊢ (A ≡ A'), assuming that A' is obtained from A 
        by replacing some occurrences of B with B'.
    *)

    val variant_equivalence_e : formula -> var -> var -> proof -> conclusion
    (* ⊢ ∃xA ≡ ∃yA[x/y] *)

    val variant_equivalence_a : formula -> var -> var -> proof -> conclusion
    (* ⊢ ∀xA ≡ ∀yA[x/y] *)

    val universal_to_existential : var -> formula -> proof -> conclusion
    (* ⊢ ∀xA → ∃xA *)

    val factor_disj_left_quantifier_e : formula -> proof -> conclusion
    (* ⊢ (∃xA ∨ B) ≡ ∃x(A ∨ B) *)

    val factor_disj_right_quantifier_e : formula -> proof -> conclusion
    (* ⊢ (A ∨ ∃xB) ≡ ∃x(A ∨ B) *)

    val factor_disj_left_quantifier_a : formula -> proof -> conclusion
    (* ⊢ (∀xA ∨ B) ≡ ∀x(A ∨ B) *)

    val factor_disj_right_quantifier_a : formula -> proof -> conclusion
    (* ⊢ (A ∨ ∀xB) ≡ ∀x(A ∨ B) *)
  end
end
