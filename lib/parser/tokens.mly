
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

%%
