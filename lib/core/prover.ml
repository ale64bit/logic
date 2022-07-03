module type S = sig
  module LANG : FirstOrderLanguage.S
  module SYS : System.S with type formula = LANG.formula

  type named_formula = string * LANG.formula

  type problem = {
    id : string;
    axioms : named_formula list;
    hypotheses : named_formula list;
    conjecture : named_formula option;
  }

  val solve : problem -> SZS.status * SZS.dataform
end
