open Fol
open Proof.Calculus

(* Interface of theorem provers *)
module type Prover = sig
  val prove : proof -> formula -> conclusion
end

(*
    Implements a simple prover for propositional tautologies based on
    Shoenfield's "Mathematical Logic" exposition of the tautology theorem.
*)
module Shoenfield : Prover
