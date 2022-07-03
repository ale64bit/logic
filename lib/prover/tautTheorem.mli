(*
    A simple prover for propositional tautologies based on the constructive exposition of the
    Tautology Theorem in Shoenfield's textbook (§3.1).
*)
module S : Core.Prover.S with module LANG = Lang.Shoenfield.S and module SYS = System.Shoenfield.Base
