module S = struct
  module LANG = Lang.Shoenfield.S
  module SYS = System.Shoenfield.Base
  open Lang.Shoenfield.Syntax (LANG)
  open SYS

  type named_formula = string * LANG.formula

  type problem = {
    id : string;
    axioms : named_formula list;
    hypotheses : named_formula list;
    conjecture : named_formula option;
  }

  let solve { axioms; hypotheses; conjecture; _ } =
    match conjecture with
    | Some (_, conj) ->
        (* Build a single implication formula from the axioms and hypotheses *)
        let fs = List.map (fun (_, a) -> a) axioms @ List.map (fun (_, a) -> a) hypotheses @ [ conj ] in
        (* Add all axioms as premises *)
        let ctx =
          List.fold_left
            (fun ctx (_, a) ->
              let ctx, _ = premise a ctx in
              ctx)
            SYS.empty axioms
        in
        (* Add all hypotheses as premises *)
        let ctx =
          List.fold_left
            (fun ctx (_, a) ->
              let ctx, _ = premise a ctx in
              ctx)
            ctx hypotheses
        in
        (* Prove the implication *)
        let ctx, _ = Meta.tautology_theorem [] (impl_of_list fs) ctx in
        (* Use detachment to eliminate the premises from the implication and obtain the conjecture *)
        let res =
          List.fold_left
            (fun (ctx, conclusion) (_, a) -> Meta.detachment a conclusion ctx)
            (ctx, impl_of_list fs)
            axioms
        in
        let res = List.fold_left (fun (ctx, conclusion) (_, a) -> Meta.detachment a conclusion ctx) res hypotheses in
        SYS.export res
    | None -> Core.SZS.error "no conjecture to prove"
end
