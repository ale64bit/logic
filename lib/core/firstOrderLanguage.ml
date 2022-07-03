module type S = sig
  type term
  type formula

  (* Term constructors *)
  val var : string -> term
  val const : string -> term
  val func : string -> term list -> term

  (* Formula constructors *)
  val atom : string -> term list -> formula
  val neg : formula -> formula
  val disj : formula -> formula -> formula
  val conj : formula -> formula -> formula
  val impl : formula -> formula -> formula
  val eq : formula -> formula -> formula
  val exists : string -> formula -> formula
  val forall : string -> formula -> formula
end
