let id_from_file path = Filename.remove_extension (Filename.basename path)

let parse_and_solve (module P : Core.Prover.S) id linebuf =
  let module M = Parser.Make (P) in
  try
    let p = M.problem Parser__Lexer.read linebuf in
    P.solve { p with id }
  with
  | Parser__Lexer.Error msg -> Core.SZS.error (Printf.sprintf "lexer error: %s" msg)
  | M.Error -> Core.SZS.error (Printf.sprintf "parser error at offset %d" (Lexing.lexeme_start linebuf))

let parse_and_solve_channel (module P : Core.Prover.S) id ch = parse_and_solve (module P) id (Lexing.from_channel ch)

let parse_and_solve_file (module P : Core.Prover.S) path =
  let ch = open_in path in
  parse_and_solve_channel (module P) (id_from_file path) ch
