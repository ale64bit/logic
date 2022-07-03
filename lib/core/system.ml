module type S = sig
  type formula
  type proof
  type conclusion = proof * formula

  val empty : proof
  val premise : formula -> proof -> conclusion
  val export : conclusion -> SZS.status * SZS.dataform
end
