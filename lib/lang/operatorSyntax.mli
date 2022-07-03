module Make : functor (L : Core.FirstOrderLanguage.S) -> sig
  open L

  val ( ! ) : formula -> formula
  val ( || ) : formula -> formula -> formula
  val ( && ) : formula -> formula -> formula
  val ( => ) : formula -> formula -> formula
  val ( <=> ) : formula -> formula -> formula
end
