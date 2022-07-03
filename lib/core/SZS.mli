(* See http://ceur-ws.org/Vol-418/paper3.pdf *)

type proof_line = {
  index : int;
  formula : string;
  name : string option;
  premises : int list;
  inference : string;
  message : string option;
}

type proof = { system : string; lines : proof_line list }
type dataform = Proof of proof | None
type success = Theorem | CounterSatisfiable | Satisfiable | Unsatisfiable
type no_success = Timeout | GaveUp of string | Error of string | Unknown of string
type status = Success of success | NoSuccess of no_success

val error : string -> status * dataform
val print : out_channel -> string -> status * dataform -> unit
val string_of_status : status -> string
