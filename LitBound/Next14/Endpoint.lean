import LitBound.Next14.PricePages
import LitBound.Next14.Transfer

set_option maxRecDepth 240000
set_option maxHeartbeats 12000000
namespace SuperpermutationLowerBound.Refinement.Coupled.Next
open _root_.ChainReturns HaruhiLower.RunBound

private def decode : FourteenCuts.Tile → Chunk
  | .efficient => E | .shortFirst => X | .shortSecond => Y | .other => .single 0

private theorem decode_of_ne (c : Chunk) (h : code c ≠ .other) : decode (code c) = c := by
  unfold code at *
  split_ifs at * <;> simp_all [decode]

private theorem lift_infix {cs : List Chunk} {ts : List FourteenCuts.Tile}
    (hi : ts <:+: cs.map code) (hgood : .other ∉ ts) : ts.map decode <:+: cs := by
  obtain ⟨left,right,he⟩ := hi
  obtain ⟨pre',post,e,e',_⟩ := List.map_eq_append_iff.mp he.symm
  obtain ⟨pre,mid,ee,_,hm⟩ := List.map_eq_append_iff.mp e'
  have h : mid.map (decode ∘ code) = mid.map id := List.map_congr_left (fun c hc =>
    decode_of_ne c (fun bad => hgood (hm ▸ (bad ▸ List.mem_map_of_mem hc))))
  refine ⟨pre,post,?_⟩
  rw [←hm,List.map_map,h,List.map_id,←ee,←e]

private theorem actual_price : Price := by
  have known : ∀ w ∈ HaruhiNextPrice.forbidden,
      (w.map decode = List.replicate 15 E ∨ w.map decode ∈ watch) ∧ FourteenCuts.Tile.other ∉ w := by decide
  intro v cap safe
  have estimate := HaruhiNextPrice.price (v.map code) (by
    intro w hw hit
    obtain ⟨hw',ht⟩ := known w hw
    have hf := lift_infix hit ht
    rcases hw' with e|e
    · exact cap (e ▸ hf)
    · exact safe _ e hf)
  simpa only [List.length_map] using estimate

open _root_.SuperpermutationLowerBound.ChainReturns in
theorem actualPacking : ActualPacking 14 (by decide) (3889/107) (4058/107) := packing_of_price actual_price

#print axioms actualPacking
theorem shortest_lower : 93891141157 ≤ shortestSuperpermutationLength 14 := shortest_of_price actual_price
/-- Unrestricted words over fourteen symbols, with contiguous coverage. -/
theorem word_lower (w : List (Fin 14)) (hw : SuperpermutationBounds.Covers w) :
    93891141157 ≤ w.length := by
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
  simpa only [W, List.length_map] using le_trans shortest_lower hmin

/-- The same unconditional result in the public challenge's definitions. -/
theorem almanac_lower : Almanac.LowerBoundAt 14 93891141157 := by
  intro w hw
  apply word_lower w
  intro p hlen hnd
  obtain ⟨u, v, heq⟩ := hw p hnd hlen
  exact ⟨u, v, heq.symm⟩


#print axioms shortest_lower
#print axioms word_lower
#print axioms almanac_lower
end SuperpermutationLowerBound.Refinement.Coupled.Next
