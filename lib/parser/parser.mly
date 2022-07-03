(* 
    Parser for TPTP files 

    See: http://www.tptp.org/cgi-bin/SeeTPTP?Category=Documents&File=SyntaxBNF
*)

%parameter <P : Core.Prover.S>

%start <P.problem> problem

%{
  open P
  open LANG

  type entry = 
    | Axiom of named_formula
    | Hypothesis of named_formula
    | Conjecture of named_formula
%}

%%

let problem := 
  entries = fof_formula*; EOF; {
    {
      id = "";
      axioms = List.filter_map (function Axiom x -> Some x | _ -> None) entries;
      hypotheses = List.filter_map (function Hypothesis x -> Some x | _ -> None) entries;
      conjecture = List.find_map (function Conjecture x -> Some x | _ -> None) entries;
    }
  }

let fof_formula := 
  | FOF; LPAREN; name = FPC; COMMA; AXIOM; COMMA; f = formula; RPAREN; PERIOD; { Axiom (name, f) }
  | FOF; LPAREN; name = FPC; COMMA; HYPOTHESIS; COMMA; f = formula; RPAREN; PERIOD; { Hypothesis (name, f) }
  | FOF; LPAREN; name = FPC; COMMA; CONJECTURE; COMMA; f = formula; RPAREN; PERIOD; { Conjecture (name, f) }

let atom :=
  | p = FPC; LPAREN; ts = separated_list(COMMA, term); RPAREN; { atom p ts }
  | p = FPC; { atom p [] }

let formula :=
  | FORALL; LBRACKET; xs = separated_list(COMMA, VAR); RBRACKET; COLON; a = formula; {
    List.fold_left (fun a' x -> forall x a') a (List.rev xs)
  }
  | EXISTS; LBRACKET; xs = separated_list(COMMA, VAR); RBRACKET; COLON; a = formula; {
    List.fold_left (fun a' x -> exists x a') a (List.rev xs)
  }
  | NOT; a = formula; { neg a }
  | a = formula; IMPL;  b = formula; { impl a b } 
  | a = formula; DIMPL; b = formula; { eq a b } 
  | a = formula; OR;    b = formula; { disj a b } 
  | a = formula; AND;   b = formula; { conj a b } 
  | LPAREN; f = formula; RPAREN; { f }
  | ~ = atom; <>
  | lhs = term; EQ; rhs = term; { atom "=" [lhs; rhs] } 

let term :=
  | x = VAR; { var x }
  | e = FPC; { const e }
  | f = FPC; LPAREN; ts = separated_list(COMMA, term); RPAREN; { func f ts }

