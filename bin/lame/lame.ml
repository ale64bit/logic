let () =
  let filename = Sys.argv.(1) in
  let id = Prover.App.id_from_file filename in
  let res = Prover.App.parse_and_solve_file (module Prover.TautTheorem.S) filename in
  Core.SZS.print Stdlib.stdout id res
