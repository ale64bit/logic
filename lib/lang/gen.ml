module Make (L : Core.FirstOrderLanguage.S) = struct
  open L

  type var = string
  type func = string
  type pred = string
  type const = string

  let random_term ?(max_depth = 8) ?(variables = [ "x"; "y"; "z" ]) ?(functions = []) ?(constants = []) rng =
    let rand = Random.State.int rng in
    let pick_one xs = List.nth xs (rand (List.length xs)) in
    let rec gen_variable _ = var (pick_one variables)
    and gen_constant _ = const (pick_one constants)
    and gen_function depth =
      let f, arity = pick_one functions in
      func f (List.init arity (fun _ -> gen_term (depth - 1)))
    and gen_term depth =
      let available =
        if depth = 0 then [ (gen_variable, List.length variables); (gen_constant, List.length constants) ]
        else
          [
            (gen_variable, List.length variables);
            (gen_constant, List.length constants);
            (gen_function, List.length functions);
          ]
      in
      let term_generators = List.fold_left (fun acc (gen, srcs) -> if srcs = 0 then acc else gen :: acc) [] available in
      (pick_one term_generators) depth
    in
    gen_term max_depth

  let random_formula ?(max_depth = 8) ?(variables = [ "x"; "y"; "z" ]) ?(predicates = [ ("=", 2) ]) ?(functions = [])
      ?(constants = []) rng =
    assert (List.length predicates > 0);
    let rand = Random.State.int rng in
    let pick_one xs = List.nth xs (rand (List.length xs)) in
    let rec gen_atomic depth =
      let p, arity = pick_one predicates in
      atom p (List.init arity (fun _ -> random_term ~max_depth:depth ~variables ~functions ~constants rng))
    and gen_neg depth = neg (gen_formula (depth - 1))
    and gen_disj depth = disj (gen_formula (depth - 1)) (gen_formula (depth - 1))
    and gen_exists depth = exists (pick_one variables) (gen_formula (depth - 1))
    and gen_formula depth =
      let formula_generators = if depth = 0 then [ gen_atomic ] else [ gen_atomic; gen_neg; gen_disj; gen_exists ] in
      (pick_one formula_generators) depth
    in
    gen_formula max_depth
end
