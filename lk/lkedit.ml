let ( let* ) = Result.bind

(* A proof is stored as a Map of sequents to their entries *)
module SequentMap = Map.Make (struct
  type t = LK.sequent

  let compare = Stdlib.compare
end)

(* Metadata about a sequent in a proof *)
type entry = {
  ent_index : int;
  ent_command : Cmd.cmd;
  ent_derivation : LK.inference;
}

type proof = entry SequentMap.t

(* Add a sequent to the proof along with its inference *)
let add proof s inf cmd =
  if SequentMap.mem s proof then ((SequentMap.find s proof).ent_index, proof)
  else
    let index = SequentMap.cardinal proof + 1 in
    ( index,
      proof
      |> SequentMap.add s
           { ent_index = index; ent_command = cmd; ent_derivation = inf } )

let parse_cmd line =
  let lexbuf = Sedlexing.Utf8.from_string line in
  try
    let lexer = Sedlexing.with_tokenizer Lexer.token lexbuf in
    let cmd =
      MenhirLib.Convert.Simplified.traditional2revised Parser.start_cmd lexer
    in
    Ok cmd
  with
  | Lexer.Error msg -> Error (Printf.sprintf "lexer error: %s" msg)
  | Parser.Error ->
      Error
        (Printf.sprintf "At offset %d: syntax error.\n%!"
           (Sedlexing.lexeme_start lexbuf))

let resolve proof index =
  match
    List.find_opt
      (fun (_, { ent_index; _ }) -> ent_index = index)
      (List.of_seq (SequentMap.to_seq proof))
  with
  | Some (s, _) -> Ok s
  | None -> Error (Printf.sprintf "no sequent with index %d" index)

let string_of_derivation proof =
  let open LK in
  let open SequentMap in
  function
  | Axiom _ -> "[Axiom]"
  | Weakening (side, s) ->
      Printf.sprintf "[W%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Contraction (side, s) ->
      Printf.sprintf "[C%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Exchange (side, s, _) ->
      Printf.sprintf "[E%s (%d)]" (string_of_side side) (find s proof).ent_index
  | Cut (s, t) ->
      Printf.sprintf "[Cut (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | NegIntro (side, s) ->
      Printf.sprintf "[¬%s (%d)]" (string_of_side side) (find s proof).ent_index
  | ConjLeft (_, s) -> Printf.sprintf "[∧L (%d)]" (find s proof).ent_index
  | ConjRight (s, t) ->
      Printf.sprintf "[∧R (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | DisjLeft (s, t) ->
      Printf.sprintf "[∨L (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | DisjRight (_, s) -> Printf.sprintf "[∨R (%d)]" (find s proof).ent_index
  | ImplLeft (s, t) ->
      Printf.sprintf "[⊃L (%d) (%d)]" (find s proof).ent_index
        (find t proof).ent_index
  | ImplRight s -> Printf.sprintf "[⊃R (%d)]" (find s proof).ent_index
  | ForAllLeft (s, t, x) ->
      Printf.sprintf "[∀L (%d) %s -> %s]" (find s proof).ent_index
        (string_of_term t) (string_of_var x)
  | ForAllRight (s, a, x) ->
      Printf.sprintf "[∀R (%d) %s -> %s]" (find s proof).ent_index
        (string_of_var a) (string_of_var x)
  | ExistsLeft (s, a, x) ->
      Printf.sprintf "[∃L (%d) %s -> %s]" (find s proof).ent_index
        (string_of_var a) (string_of_var x)
  | ExistsRight (s, t, x) ->
      Printf.sprintf "[∃R (%d) %s -> %s]" (find s proof).ent_index
        (string_of_term t) (string_of_var x)
  | Macro (name, _, _) -> Printf.sprintf "[macro %s]" name

let print_proof proof =
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  List.iteri
    (fun i (s, { ent_derivation; _ }) ->
      Printf.printf "  (%d) %-60s%s\n" (i + 1) (LK.string_of_sequent s)
        (string_of_derivation proof ent_derivation))
    entries

let tex_of_proof proof =
  let open LK in
  let rec aux s =
    match (SequentMap.find s proof).ent_derivation with
    | Axiom f -> Printf.sprintf "\\AxiomC{$%s$}" (tex_of_sequent ([ f ], [ f ]))
    | Weakening (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[W%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Contraction (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[C%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Exchange (side, s', _) ->
        Printf.sprintf "%s\n\\RightLabel{[X%s]}\n\\UnaryInfC{$%s$}" (aux s')
          (string_of_side side) (tex_of_sequent s)
    | Cut (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[Cut]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | NegIntro (side, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\neg$%s]}\n\\UnaryInfC{$%s$}"
          (aux s') (string_of_side side) (tex_of_sequent s)
    | ConjLeft (_, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\land$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ConjRight (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\land$R]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | DisjLeft (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\lor$L]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | DisjRight (_, s') ->
        Printf.sprintf "%s\n\\RightLabel{[$\\lor$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ImplLeft (sl, sr) ->
        Printf.sprintf "%s\n%s\n\\RightLabel{[$\\supset$L]}\n\\BinaryInfC{$%s$}"
          (aux sl) (aux sr) (tex_of_sequent s)
    | ImplRight s' ->
        Printf.sprintf "%s\n\\RightLabel{[$\\supset$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ForAllLeft (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\forall$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ForAllRight (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\forall$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ExistsLeft (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\exists$L]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | ExistsRight (s', _, _) ->
        Printf.sprintf "%s\n\\RightLabel{[$\\exists$R]}\n\\UnaryInfC{$%s$}"
          (aux s') (tex_of_sequent s)
    | Macro (name, _, axioms) ->
        let nth_inf =
          [
            (1, "UnaryInfC");
            (2, "BinaryInfC");
            (3, "TrinaryInfC");
            (4, "QuaternaryInfC");
            (5, "QuinaryInfC");
          ]
        in
        let ss =
          String.concat "\n"
            (List.map
               (fun s -> Printf.sprintf "\\AxiomC{$%s$}" (tex_of_sequent s))
               axioms)
        in
        Printf.sprintf "%s\n\\doubleLine\n\\RightLabel{[%s]}\n\\%s{$%s$}" ss
          name
          (List.assoc (List.length axioms) nth_inf)
          (tex_of_sequent s)
  in
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ej.ent_index ei.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  let s, _ = List.hd entries in
  aux s

let axioms_and_endsequent proof =
  let entries =
    List.sort
      (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
      (List.of_seq (SequentMap.to_seq proof))
  in
  let axioms =
    List.filter_map
      (fun (s, { ent_derivation; _ }) ->
        match ent_derivation with Axiom _ -> Some s | _ -> None)
      entries
  in
  let endseq, _ = List.hd (List.rev entries) in
  (axioms, endseq)

let substitute_term f s t =
  let open LK in
  let rec aux_term = function
    | s' when s = s' -> t
    | Fun (f, ss) -> Fun (f, List.map aux_term ss)
    | Term (s, ss) -> Term (s, List.map aux_term ss)
    | s' -> s'
  in
  let rec aux_formula = function
    | Atom (r, ss) -> Atom (r, List.map aux_term ss)
    | Neg a -> Neg (aux_formula a)
    | Disj (a, b) -> Disj (aux_formula a, aux_formula b)
    | Conj (a, b) -> Conj (aux_formula a, aux_formula b)
    | Impl (a, b) -> Impl (aux_formula a, aux_formula b)
    | Exists (x, a) -> Exists (x, aux_formula a)
    | ForAll (x, a) -> ForAll (x, aux_formula a)
    | Formula (a, ts) -> Formula (a, List.map aux_term ts)
  in
  aux_formula f

let with_replacements repl =
  let open Cmd in
  function
  | Axiom f -> Axiom (f |> LK.with_replacements repl)
  | Weakening (side, i, f) -> Weakening (side, i, f |> LK.with_replacements repl)
  | ConjLeft (side, i, f) -> ConjLeft (side, i, f |> LK.with_replacements repl)
  | DisjRight (side, i, f) -> DisjRight (side, i, f |> LK.with_replacements repl)
  | other -> other

let rec process line proof =
  let* cmd = parse_cmd line in
  let* proof, _ = handle_cmd proof cmd in
  Ok proof

and handle_cmd proof cmd =
  match cmd with
  | Axiom a ->
      let s = ([ a ], [ a ]) in
      let* _ = LK.validate_sequent s in
      let index, proof = add proof s (LK.Axiom a) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Weakening (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = resolve proof index in
      let s =
        match side with
        | LK.Left -> (d :: ant, suc)
        | LK.Right -> (ant, suc @ [ d ])
      in
      let index, proof = add proof s (LK.Weakening (side, (ant, suc))) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Contraction (side, index) ->
      let* ant, suc = resolve proof index in
      let* s =
        match (side, ant, List.rev suc) with
        | LK.Left, d :: d' :: _, _ when d = d' -> Ok (List.tl ant, suc)
        | LK.Right, _, d :: d' :: _ when d = d' ->
            Ok (ant, List.rev (List.tl (List.rev suc)))
        | LK.Left, _ :: _ :: _, _ ->
            Error
              "contraction: the first two sequents of the antecedent must be \
               the same"
        | LK.Right, _, _ :: _ :: _ ->
            Error
              "contraction: the last two sequents of the succedent must be the \
               same"
        | LK.Left, _, _ ->
            Error "contraction: not enough formulas in the left sequent"
        | LK.Right, _, _ ->
            Error "contraction: not enough formulas in the right sequent"
      in
      let index, proof = add proof s (LK.Contraction (side, (ant, suc))) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Exchange (side, index, start) ->
      let* ant, suc = resolve proof index in
      if side = LK.Left && start + 1 >= List.length ant then
        Error "exchange: initial formula out of bounds"
      else if side = LK.Right && start + 1 >= List.length suc then
        Error "exchange: initial formula out of bounds"
      else
        let rec exch i = function
          | c :: d :: xs when i = start -> d :: c :: xs
          | x :: xs -> x :: exch (i + 1) xs
          | [] -> []
        in
        let* s =
          match (side, ant, suc) with
          | LK.Left, [ _ ], _ ->
              Error "exchange: not enough formulas in the left sequent"
          | LK.Left, [], _ ->
              Error "exchange: not enough formulas in the left sequent"
          | LK.Right, _, [ _ ] ->
              Error "exchange: not enough formulas in the right sequent"
          | LK.Right, _, [] ->
              Error "exchange: not enough formulas in the right sequent"
          | LK.Left, _, _ -> Ok (exch 0 ant, suc)
          | LK.Right, _, _ -> Ok (ant, exch 0 suc)
        in
        let index, proof =
          add proof s (LK.Exchange (side, (ant, suc), start)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (proof, s)
  | Cut (lindex, rindex) ->
      let* lant, lsuc = resolve proof lindex in
      let* rant, rsuc = resolve proof rindex in
      let* s =
        match (List.rev lsuc, rant) with
        | d :: _, d' :: _ when d = d' ->
            Ok (lant @ List.tl rant, List.rev (List.tl (List.rev lsuc)) @ rsuc)
        | _ :: _, _ :: _ ->
            Error
              "cut: last formula in left sequent must be equal to first \
               formula in right sequent"
        | _, [] -> Error "cut: not enough formulas in the right sequent"
        | [], _ -> Error "cut: not enough formulas in the left sequent"
      in
      let index, proof =
        add proof s (LK.Cut ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Negation (side, index) ->
      let* ant, suc = resolve proof index in
      let* s =
        match (side, ant, List.rev suc) with
        | LK.Left, _, d :: _ ->
            Ok (LK.Neg d :: ant, List.rev (List.tl (List.rev suc)))
        | LK.Right, d :: _, _ -> Ok (List.tl ant, suc @ [ LK.Neg d ])
        | LK.Left, _, _ ->
            Error "negation: not enough formulas in the right sequent"
        | LK.Right, _, _ ->
            Error "negation: not enough formulas in the left sequent"
      in
      let index, proof = add proof s (LK.NegIntro (side, (ant, suc))) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ConjLeft (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = resolve proof index in
      let* s =
        match (side, ant) with
        | LK.Left, c :: _ -> Ok (LK.Conj (d, c) :: List.tl ant, suc)
        | LK.Right, c :: _ -> Ok (LK.Conj (c, d) :: List.tl ant, suc)
        | _, [] -> Error "lconj: not enough formulas in the left sequent"
      in
      let index, proof = add proof s (LK.ConjLeft (side, (ant, suc))) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ConjRight (lindex, rindex) ->
      let* lant, lsuc = resolve proof lindex in
      let* rant, rsuc = resolve proof rindex in
      let* s =
        if lant = rant then
          match (List.rev lsuc, List.rev rsuc) with
          | c :: delta, d :: delta' when delta = delta' ->
              Ok (lant, List.rev (LK.Conj (c, d) :: delta))
          | _ :: _, _ :: _ -> Error "rconj: succedents must share equal prefix"
          | _, [] -> Error "rconj: not enough formulas in the right sequent"
          | [], _ -> Error "rconj: not enough formulas in the left sequent"
        else Error "rconj: antecedents must be equal"
      in
      let index, proof =
        add proof s (LK.ConjRight ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | DisjLeft (lindex, rindex) ->
      let* lant, lsuc = resolve proof lindex in
      let* rant, rsuc = resolve proof rindex in
      let* s =
        if lsuc = rsuc then
          match (lant, rant) with
          | c :: gamma, d :: gamma' when gamma = gamma' ->
              Ok (LK.Disj (c, d) :: gamma, lsuc)
          | _ :: _, _ :: _ -> Error "ldisj: succedents must share equal prefix"
          | _, [] -> Error "ldisj: not enough formulas in the right sequent"
          | [], _ -> Error "ldisj: not enough formulas in the left sequent"
        else Error "ldisj: succedents must be equal"
      in
      let index, proof =
        add proof s (LK.DisjLeft ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | DisjRight (side, index, d) ->
      let* _ = LK.validate_formula d in
      let* ant, suc = resolve proof index in
      let* s =
        match (side, List.rev suc) with
        | LK.Left, c :: _ ->
            Ok (ant, List.rev (LK.Disj (d, c) :: List.tl (List.rev suc)))
        | LK.Right, c :: _ ->
            Ok (ant, List.rev (LK.Disj (c, d) :: List.tl (List.rev suc)))
        | _, [] -> Error "rdisj: not enough formulas in the right sequent"
      in
      let index, proof = add proof s (LK.DisjRight (side, (ant, suc))) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ImplLeft (lindex, rindex) ->
      let* lant, lsuc = resolve proof lindex in
      let* rant, rsuc = resolve proof rindex in
      let* s =
        match (List.rev lsuc, rant) with
        | c :: delta, d :: pi ->
            Ok ((LK.Impl (c, d) :: lant) @ pi, List.rev delta @ rsuc)
        | _, [] -> Error "limpl: not enough formulas in the right sequent"
        | [], _ -> Error "limpl: not enough formulas in the left sequent"
      in
      let index, proof =
        add proof s (LK.ImplLeft ((lant, lsuc), (rant, rsuc))) cmd
      in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ImplRight index ->
      let* ant, suc = resolve proof index in
      let* s =
        match (ant, List.rev suc) with
        | c :: gamma, d :: delta ->
            Ok (gamma, List.rev (LK.Impl (c, d) :: delta))
        | _, [] -> Error "rimpl: not enough formulas in the right sequent"
        | [], _ -> Error "rimpl: not enough formulas in the left sequent"
      in
      let index, proof = add proof s (LK.ImplRight (ant, suc)) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ForAllLeft (index, t, x) ->
      let* ant, suc = resolve proof index in
      let* s =
        match ant with
        | f :: gamma ->
            let f' = LK.ForAll (x, substitute_term f t (LK.Var x)) in
            let* _ = LK.validate_formula f' in
            Ok (f' :: gamma, suc)
        | [] -> Error "lforall: not enough formulas in the left sequent"
      in
      let index, proof = add proof s (LK.ForAllLeft ((ant, suc), t, x)) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | ForAllRight (index, a, x) ->
      let* ant, suc = resolve proof index in
      let* s =
        match List.rev suc with
        | f :: delta ->
            let f' = LK.ForAll (x, substitute_term f (LK.Var a) (LK.Var x)) in
            Ok (ant, List.rev (f' :: delta))
        | [] -> Error "rforall: not enough formulas in the right sequent"
      in
      let* vs = LK.validate_sequent s in
      if LK.VarSet.mem a vs then
        Error
          (Printf.sprintf
             "rforall: free variable %s cannot appear in lower sequent"
             (LK.string_of_var a))
      else
        let index, proof =
          add proof s (LK.ForAllRight ((ant, suc), a, x)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (proof, s)
  | ExistsLeft (index, a, x) ->
      let* ant, suc = resolve proof index in
      let* s =
        match ant with
        | f :: gamma ->
            let f' = LK.Exists (x, substitute_term f (LK.Var a) (LK.Var x)) in
            Ok (f' :: gamma, suc)
        | [] -> Error "rforall: not enough formulas in the right sequent"
      in
      let* vs = LK.validate_sequent s in
      if LK.VarSet.mem a vs then
        Error
          (Printf.sprintf
             "lexists: free variable %s cannot appear in lower sequent"
             (LK.string_of_var a))
      else
        let index, proof =
          add proof s (LK.ForAllRight ((ant, suc), a, x)) cmd
        in
        let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
        Ok (proof, s)
  | ExistsRight (index, t, x) ->
      let* ant, suc = resolve proof index in
      let* s =
        match List.rev suc with
        | f :: delta ->
            let f' = LK.Exists (x, substitute_term f t (LK.Var x)) in
            let* _ = LK.validate_formula f' in
            Ok (ant, List.rev (f' :: delta))
        | [] -> Error "rexists: not enough formulas in the left sequent"
      in
      let index, proof = add proof s (LK.ExistsRight ((ant, suc), t, x)) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Macro (path, repl) ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_in path in
      let rec aux proof =
        try
          let line = input_line ch in
          let* cmd = parse_cmd line in
          let* proof, _ = handle_cmd proof (cmd |> with_replacements repl) in
          aux proof
        with End_of_file -> Ok proof
      in
      let proof' = SequentMap.empty in
      let* proof' = aux proof' in
      let axioms, s = axioms_and_endsequent proof' in
      let filename = List.hd (List.rev (String.split_on_char '/' path)) in
      let name =
        String.concat "."
          (List.rev (List.tl (List.rev (String.split_on_char '.' filename))))
      in
      let index, proof = add proof s (LK.Macro (name, repl, axioms)) cmd in
      let () = Printf.printf "  (%d) %s\n" index (LK.string_of_sequent s) in
      Ok (proof, s)
  | Print ->
      print_proof proof;
      Ok (proof, LK.empty_sequent)
  | TeX path ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_out path in
      Printf.fprintf ch "\\begin{prooftree}\n%s\n\\end{prooftree}\n"
        (tex_of_proof proof);
      close_out ch;
      Ok (proof, LK.empty_sequent)
  | Load path ->
      let path = String.sub path 1 (String.length path - 2) in
      let ch = open_in path in
      let rec aux proof =
        try
          let line = input_line ch in
          match process line proof with Ok proof -> aux proof | err -> err
        with End_of_file -> Ok proof
      in
      let* proof = aux proof in
      Ok (proof, LK.empty_sequent)
  | Save path ->
      let path = String.sub path 1 (String.length path - 2) in
      let entries =
        List.sort
          (fun (_, ei) (_, ej) -> Stdlib.compare ei.ent_index ej.ent_index)
          (List.of_seq (SequentMap.to_seq proof))
      in
      let s =
        String.concat "\n"
          (List.map
             (fun (_, { ent_command; _ }) ->
               Cmd.ascii_string_of_cmd ent_command)
             entries)
      in
      let ch = open_out path in
      Printf.fprintf ch "%s" s;
      close_out ch;
      Ok (proof, LK.empty_sequent)
  | Clear -> Ok (SequentMap.empty, LK.empty_sequent)

let rec loop channel proof =
  Printf.printf "> %!";
  let line = input_line channel in
  match process line proof with
  | Ok proof -> loop channel proof
  | Error err ->
      let () = Printf.printf "error: %s\n" err in
      loop channel proof

let () = loop stdin SequentMap.empty
