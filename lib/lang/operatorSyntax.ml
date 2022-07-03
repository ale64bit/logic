module Make (L : Core.FirstOrderLanguage.S) = struct
  let ( ! ) = L.neg
  let ( || ) = L.disj
  let ( && ) = L.conj
  let ( => ) = L.impl
  let ( <=> ) = L.eq
end
