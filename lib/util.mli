module StringSet : Set.S with type elt = string

val is_sublist : 'a list -> 'a list -> bool
(** [is_sublist xs ys] tests whether list [xs] is a sublist of list [ys]. *)

val is_subset : 'a list -> 'a list -> bool
(** [is_subset xs ys] tests whether the elements of list [xs] are a subset of the elements of list [ys]. *)
