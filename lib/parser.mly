(* 
    Parser for TPTP (FOF) files 

    See: http://www.tptp.org/cgi-bin/SeeTPTP?Category=Documents&File=SyntaxBNF
*)
%token FOF AXIOM HYPOTHESIS CONJECTURE
%token LPAREN RPAREN
%token LBRACKET RBRACKET

%token <string> VAR 
%token <string> FPC

%token EQ FORALL EXISTS NOT AND OR IMPL DIMPL
%token COLON COMMA PERIOD
%token EOF

%nonassoc COLON
%right DIMPL
%right IMPL
%right OR AND
%right NOT 
(*%right FORALL EXISTS*)

%start <Tptp.fof list> foflist

%%

let foflist := 
  ~ = fof*; EOF; <>

let fof := 
  FOF; LPAREN; name = FPC; COMMA; role = role; COMMA; f = formula; RPAREN; PERIOD; {
    Tptp.{ name = name; role = role; formula = f }
  }

let role :=
  | AXIOM; { Tptp.Axiom }
  | HYPOTHESIS; { Tptp.Hypothesis }
  | CONJECTURE; { Tptp.Conjecture }

let formula :=
  | FORALL; LBRACKET; ~ = separated_list(COMMA, VAR); RBRACKET; COLON; ~ = formula; <Tptp.ForAll>
  | EXISTS; LBRACKET; ~ = separated_list(COMMA, VAR); RBRACKET; COLON; ~ = formula; <Tptp.Exists>
  | NOT; ~ = formula; <Tptp.Neg>
  | lhs = formula; IMPL; rhs = formula; { Tptp.Impl (lhs, rhs) }
  | lhs = formula; DIMPL; rhs = formula; { Tptp.DImpl (lhs, rhs) }
  | lhs = formula; OR; rhs = formula; { Tptp.Or (lhs, rhs) }
  | lhs = formula; AND; rhs = formula; { Tptp.And (lhs, rhs) }
  | LPAREN; f = formula; RPAREN; { f }
  | ~ = FPC; LPAREN; ~ = separated_list(COMMA, term); RPAREN; <Tptp.Atom>
  | lhs = term; EQ; rhs = term; { Tptp.Atom ("=", [lhs; rhs]) }

let term :=
  | ~ = VAR; <Tptp.Var>
  | ~ = FPC; <Tptp.Const>
  | ~ = FPC; LPAREN; ~ = separated_list(COMMA, term); RPAREN; <Tptp.Fun>

