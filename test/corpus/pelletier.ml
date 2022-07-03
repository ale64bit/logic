let propositional =
  [
    ("Pelletier1", "fof(pel1, conjecture, (p => q) <=> (~q => ~p) ).");
    ("Pelletier2", "fof(pel2, conjecture, ~~p <=> p ).");
    ("Pelletier3", "fof(pel3, conjecture, ~(p => q) => (q => p) ).");
    ("Pelletier4", "fof(pel4, conjecture, (~p => q) <=> (~q => p) ).");
    ("Pelletier5", "fof(pel5, conjecture, ((p | q) => (p | r)) => (p | (q => r)) ).");
    ("Pelletier6", "fof(pel6, conjecture, p | ~p ).");
    ("Pelletier7", "fof(pel7, conjecture, p | ~~~p ).");
    ("Pelletier8", "fof(pel8, conjecture, ((p => q) => p) => p ).");
    ("Pelletier9", "fof(pel9, conjecture, ((p | q) & (~p | q) & (p | ~q)) => ~(~p | ~q) ).");
    ( "Pelletier10",
      "fof(pel10_a1, axiom, q => r ).\n\
       fof(pel10_a2, axiom, r => (p & q) ).\n\
       fof(pel10_a3, axiom, p => (q | r) ).\n\
       fof(pel10, conjecture, p <=> q ).\n" );
    ("Pelletier11", "fof(pel11, conjecture, p <=> p ).");
    ("Pelletier12", "fof(pel12, conjecture, ((p <=> q) <=> r) <=> (p <=> (q <=> r)) ).");
    ("Pelletier13", "fof(pel13, conjecture, (p | (q & r)) <=> ((p | q) & (p | r)) ).");
    ("Pelletier14", "fof(pel14, conjecture, (p <=> q) <=> ((q | ~p) & (~q | p)) ).");
    ("Pelletier15", "fof(pel15, conjecture, (p => q) <=> (~p | q) ).");
    ("Pelletier16", "fof(pel16, conjecture, (p => q) | (q => p) ).");
    ("Pelletier17", "fof(pel17, conjecture, ((p & (q => r)) => s) <=> ((~p | q | s) & (~p | ~r | s)) ).");
  ]
