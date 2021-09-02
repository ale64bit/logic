(* Lexer for TPTP files *)
{
  open Lexing
  open Parser

  exception Error of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let var = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let fpc = ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white      { read lexbuf }
  | "%" [^ '\r' '\n']* newline
  | newline      { next_line lexbuf; read lexbuf }
  | "fof"        { FOF }
  | "axiom"      { AXIOM }
  | "hypothesis" { HYPOTHESIS }
  | "conjecture" { CONJECTURE }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "["          { LBRACKET }
  | "]"          { RBRACKET }
  | var          { VAR (Lexing.lexeme lexbuf) }
  | fpc          { FPC (Lexing.lexeme lexbuf) }
  | "="          { EQ }
  | "!"          { FORALL }
  | "?"          { EXISTS }
  | ":"          { COLON }
  | ","          { COMMA }
  | "~"          { NOT }
  | "&"          { AND }
  | "|"          { OR }
  | "=>"         { IMPL }
  | "<=>"        { DIMPL }
  | "."          { PERIOD }
  | eof          { EOF }
  | _            { raise (Error ("unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment =
  parse
  | newline    { next_line lexbuf; read lexbuf }
  | _          { comment lexbuf }
