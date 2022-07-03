val id_from_file : string -> string
(* [id_from_file path] returns the file name without extension as problem ID *)

val parse_and_solve : (module Core.Prover.S) -> string -> Lexing.lexbuf -> Core.SZS.status * Core.SZS.dataform
val parse_and_solve_channel : (module Core.Prover.S) -> string -> in_channel -> Core.SZS.status * Core.SZS.dataform
val parse_and_solve_file : (module Core.Prover.S) -> string -> Core.SZS.status * Core.SZS.dataform
(* [parse_and_solve* (module P) id input] parses and tries to solve using prover [P] the input problem with [id] *)
