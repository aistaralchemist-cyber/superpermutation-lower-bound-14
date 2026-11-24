import RunBound.Transfer
import RunBound.Geometry
import AlmanacDefs

namespace SuperpermutationLowerBound.Refinement.RunBound
open _root_.ChainReturns HaruhiLower.RunBound

/-- The shortest contiguous superpermutation on fourteen symbols has
at least 93,891,141,154 symbols. -/
theorem shortest_haruhi_improved : 93891141154 ≤ shortestSuperpermutationLength 14 := by
  apply improved14_of_windows
  intro p hp seg z hz b
  rcases List.mem_cons.mp hz with rfl | hz
  · exact Haruhi14.forbidX seg b
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact Haruhi14.forbidY seg b
    · simp at hz

/-- Unrestricted words over fourteen symbols, with contiguous coverage. -/
theorem word_haruhi_improved (w : List (Fin 14)) (hw : SuperpermutationBounds.Covers w) :
    93891141154 ≤ w.length := by
  classical
  let e : Alphabet 14 ≃ Fin 14 := Fintype.equivFinOfCardEq (by simp [Alphabet])
  let W : Word 14 := w.map e.symm
  have hW : IsSuperpermutation W := by
    intro P
    have hlength : (P.1.map e).length = 14 := by
      simpa only [List.length_map] using P.length
    have hnodup : (P.1.map e).Nodup := P.nodup.map e.injective
    obtain ⟨u, v, heq⟩ := hw (P.1.map e) hlength hnodup
    refine ⟨u.map e.symm, v.map e.symm, ?_⟩
    have hmapped := congrArg (List.map e.symm) heq
    simpa [W, List.map_append, List.map_map, Function.comp_def] using hmapped.symm
  have hmin := shortestSuperpermutationLength_le W hW
  simpa only [W, List.length_map] using le_trans shortest_haruhi_improved hmin

/-- The same unconditional result in the public challenge's definitions. -/
theorem almanac_haruhi_improved : Almanac.LowerBoundAt 14 93891141154 := by
  intro w hw
  apply word_haruhi_improved w
  intro p hlen hnd
  obtain ⟨u, v, heq⟩ := hw p hnd hlen
  exact ⟨u, v, heq.symm⟩

#print axioms shortest_haruhi_improved
#print axioms word_haruhi_improved
#print axioms almanac_haruhi_improved
end SuperpermutationLowerBound.Refinement.RunBound
