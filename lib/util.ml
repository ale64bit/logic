module StringSet = Set.Make (String)

let rec is_sublist xs ys =
  match (xs, ys) with
  | x :: xs', y :: ys' ->
      if x = y then is_sublist xs' ys' else is_sublist xs ys'
  | _ :: _, [] -> false
  | [], _ -> true

let is_subset a' a = List.for_all ((Fun.flip List.mem) a) a'
