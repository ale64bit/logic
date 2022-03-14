open Fol
open Defined.Operators

(* Some symbols/formulas which are useful in general contexts. *)
module Common = struct
  let x = Var "x"
  let y = Var "y"
  let z = Var "z"
  let px = Atom ("p", [ x ])
  let qx = Atom ("q", [ x ])
  let rx = Atom ("r", [ x ])
  let sx = Atom ("s", [ x ])
  let py = Atom ("p", [ y ])
  let pxy = Atom ("p", [ x; y ])
  let x_eq_x = Atom ("=", [ x; x ])
  let x_eq_y = Atom ("=", [ x; y ])
  let x_eq_z = Atom ("=", [ x; z ])
  let y_eq_y = Atom ("=", [ y; y ])
  let y_eq_z = Atom ("=", [ y; z ])
  let z_eq_z = Atom ("=", [ z; z ])
end

(*
    Pelletier, F.J. Seventy-five problems for testing automatic theorem provers.
    J Autom Reasoning 2, 191–216 (1986).
    https://doi.org/10.1007/BF02432151
*)
module Pelletier1986 = struct
  include Common

  (* Propositional Logic *)

  let p1 = px => qx <=> (!qx => !px)
  (* 2pts *)

  let p2 = !(!px) <=> px
  (* 2pts *)

  let p3 = !(px => qx) => (qx => px)
  (* 1pt *)

  let p4 = !px => qx <=> (!qx => px)
  (* 2pts *)

  let p5 = (px || qx) => (px || rx) => (px || qx => rx)
  (* 4pts *)

  let p6 = px || !px
  (* 2pts *)

  let p7 = px || !(!(!px))
  (* 3pts *)

  let p8 = px => qx => px => px
  (* 5pts *)

  let p9 = ((px || qx) && (!px || qx) && (px || !qx)) => !(!px || !qx)
  (* 6pts *)

  let p10 = qx => rx => (rx => (px && qx) => (px => (qx || rx) => (px <=> qx)))
  (* 4pts *)

  let p11 = px <=> px
  (* 1pt *)

  let p12 = px <=> qx <=> rx <=> (px <=> (qx <=> rx))
  (* 7pts *)

  let p13 = (px || (qx && rx)) <=> ((px || qx) && (px || rx))
  (* 5pts *)

  let p14 = px <=> qx <=> ((qx || !px) && (!qx || px))
  (* 6pts *)

  let p15 = px => qx <=> (!px || qx)
  (* 5pts *)

  let p16 = px => qx || qx => px
  (* 4pts *)

  let p17 = (px && qx => rx) => sx <=> ((!px || qx || sx) && (!px || !rx || sx))
  (* 6pts *)
end

(*
    Shoenfield, J.R. Mathematical Logic.
    Reading, Mass., Addison-Wesley Pub. Co (1967)
*)
module Shoenfield1967 = struct
  include Common

  (* Chapter 2 *)

  let ch2_5a = !(!x_eq_x) || !x_eq_x
  (* A theorem not provable without propositional axioms *)

  let ch2_5b = x_eq_x => Exists ("x", x_eq_x)
  (* A theorem not provable without substitution axioms *)

  let ch2_5c = x_eq_x
  (* A theorem not provable without identity axioms *)

  let ch2_5d = x_eq_y => (x_eq_z => (x_eq_x => y_eq_z))
  (* A theorem not provable without equality axioms *)

  let ch2_5e = x_eq_x || !x_eq_x || x_eq_x
  (* A theorem not provable without the expansion rule *)

  let ch2_5f = !(!x_eq_x)
  (* A theorem not provable without the contraction rule *)

  let ch2_5g = !(!x_eq_x || !x_eq_x)
  (* A theorem not provable without the associative rule *)

  let ch2_5h = !(!x_eq_x)
  (* A theorem not provable without the cut rule *)

  let ch2_5i = Exists ("y", !x_eq_x) => !x_eq_x
  (* A theorem not provable without the e-introduction rule *)
end

(* De Morgan laws *)
module DeMorgan = struct
  include Common

  let conj = !(px && qx) <=> (!px || !qx)
  let disj = !(px || qx) <=> (!px && !qx)
end
