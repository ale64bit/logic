(* A functor for generating random terms and formulas in a given language *)
module Make : functor (L : Core.FirstOrderLanguage.S) -> sig
  type var = string
  type func = string
  type pred = string
  type const = string

  val random_term :
    ?max_depth:int ->
    ?variables:var list ->
    ?functions:(func * int) list ->
    ?constants:const list ->
    Random.State.t ->
    L.term

  val random_formula :
    ?max_depth:int ->
    ?variables:var list ->
    ?predicates:(pred * int) list ->
    ?functions:(func * int) list ->
    ?constants:const list ->
    Random.State.t ->
    L.formula
end
