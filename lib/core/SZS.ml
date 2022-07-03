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

type no_success =
  | Timeout
  | GaveUp of string
  | Error of string
  | Unknown of string

type status = Success of success | NoSuccess of no_success

let error msg = (NoSuccess (Error msg), None)

let print_status ch id = function
  | Success Theorem -> Printf.fprintf ch "%% SZS status Theorem for %s\n" id
  | Success CounterSatisfiable ->
      Printf.fprintf ch "%% SZS status CounterSatisfiable for %s\n" id
  | Success Satisfiable ->
      Printf.fprintf ch "%% SZS status Satisfiable for %s\n" id
  | Success Unsatisfiable ->
      Printf.fprintf ch "%% SZS status Unsatisfiable for %s\n" id
  | NoSuccess Timeout -> Printf.fprintf ch "%% SZS status Timeout for %s\n" id
  | NoSuccess (GaveUp msg) ->
      Printf.fprintf ch "%% SZS status GaveUp for %s : %s\n" id msg
  | NoSuccess (Error msg) ->
      Printf.fprintf ch "%% SZS status Error for %s : %s\n" id msg
  | NoSuccess (Unknown msg) ->
      Printf.fprintf ch "%% SZS status Unknown for %s : %s\n" id msg

let print_dataform ch id = function
  | Proof { system; lines } ->
      Printf.fprintf ch
        "%% SZS output start Proof for %s : inference system is %s\n" id system;
      List.iter
        (fun { index; formula; premises; inference; _ } ->
          Printf.fprintf ch "%d. %s  [%s%s]\n" index formula inference
            (match premises with
            | [] -> ""
            | _ -> " " ^ String.concat ", " (List.map string_of_int premises)))
        lines;
      Printf.fprintf ch "%% SZS output end Proof for %s\n" id
  | _ -> ()

let print ch id (st, df) =
  print_status ch id st;
  print_dataform ch id df

let string_of_success = function
  | Theorem -> "Theorem"
  | CounterSatisfiable -> "CounterSatisfiable"
  | Satisfiable -> "Satisfiable"
  | Unsatisfiable -> "Unsatisfiable"

let string_of_status = function
  | Success success -> Printf.sprintf "Success %s" (string_of_success success)
  | NoSuccess Timeout -> Printf.sprintf "NoSuccess Timeout"
  | NoSuccess (GaveUp msg) -> Printf.sprintf "NoSuccess GaveUp '%s'" msg
  | NoSuccess (Error msg) -> Printf.sprintf "NoSuccess Error '%s'" msg
  | NoSuccess (Unknown msg) -> Printf.sprintf "NoSuccess Unknown '%s'" msg
