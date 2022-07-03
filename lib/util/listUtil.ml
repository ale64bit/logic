let split_at xi xs =
  let rec aux left = function xj :: xs -> if xi = xj then (left, xs) else aux (xj :: left) xs | [] -> (left, []) in
  let l, r = aux [] xs in
  (List.rev l, r)

let rec is_sublist xs ys =
  match (xs, ys) with
  | x :: xs', y :: ys' -> if x = y then is_sublist xs' ys' else is_sublist xs ys'
  | _ :: _, [] -> false
  | [], _ -> true

let is_subset a' a = List.for_all ((Fun.flip List.mem) a) a'
