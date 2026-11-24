import LitBound.Geometry

/-! The shortened-cell analogue of PatternAt.full_after_cells is adapted from
Jay Pantone and contributors, pairs/InteriorFullRuns.lean, revision
ad72ab5010e945b5c8768a918281778c834dcc40, Apache-2.0. It permits all nine
interior full rows when a shortened cell occurs at a collision endpoint. -/
namespace SuperpermutationLowerBound.Refinement.PatternAt
theorem full_after_shortened_cells {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}
    {before : List Bool} {tail : List ℕ}
    (h : PatternAt segment start
      (cellWord (n - 2) before ++ (cellDigits (n - 2) true ++ tail)))
    (hstart : start < segment.length) (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (he : (segment.actualRun ⟨start, hstart⟩).entry = shortEntry n hn e)
    (r : ℕ) (hr : r < n - 4) :
    ∃ row : Fin segment.length,
      row.val = start + (cellWord (n - 2) before).length + 1 + r ∧
      (segment.actualRun row).length = n ∧
      (segment.actualRun row).entry = fullRunMapPower (by omega) r
        (fullEntry n hn ((cellNormalization n hn before).symm.trans e)) := by
  have h' : PatternAt segment start
      (cellWord (n - 2) before ++ 2 :: (List.replicate ((n - 2) - 2) 0 ++ tail)) := by
    simpa only [cellDigits, ↓reduceIte, List.cons_append] using h
  have hentry := h'.cellWord_entry hn (by decide) e he
  have htail := h.append_right
  have hformula := htail.cell_full_entry hn
    ((cellNormalization n hn before).symm.trans e) hentry r (by simpa using hr)
  have hrow : start + (cellWord (n - 2) before).length + 1 + r < segment.length := by
    have hh := htail.1
    simp only [cellDigits, ↓reduceIte, List.length_append,
      List.length_cons, List.length_replicate] at hh
    omega
  refine ⟨⟨_, hrow⟩, rfl, ?_, hformula⟩
  have hi : r + 1 < (cellDigits (n - 2) true ++ tail).length := by
    simp only [cellDigits, ↓reduceIte, List.length_append,
      List.length_cons, List.length_replicate]
    omega
  have hl := htail.actual_length (r + 1) hi
  simp only [cellDigits, ↓reduceIte, List.cons_append] at hl
  rw [List.getElem_cons_succ] at hl
  rw [List.getElem_append_left (by simp only [List.length_replicate]; omega)] at hl
  simpa only [List.getElem_replicate, Nat.add_sub_cancel, Nat.sub_zero, Nat.add_assoc, Nat.add_comm r 1] using hl

end SuperpermutationLowerBound.Refinement.PatternAt

namespace SuperpermutationLowerBound.Refinement.Coupled.Extended
open PermutationVertex _root_.ChainReturns HaruhiLower.RunBound
set_option maxRecDepth 45000
set_option maxHeartbeats 10000000
private def rot (k : ℕ) (i : Fin 14) : Fin 14 :=
  ⟨prefixRotateIndex 14 13 k i, prefixRotateIndex_lt (by decide) i.2⟩

private abbrev norm (w : List Bool) := cellNormalization 13 (by decide) w

private theorem short_row {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 11 w ++ (cellDigits 11 b ++ tail)))
    (hs : s < seg.length) (e : Fin 14 ≃ Alphabet 14)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 13 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 11 w).length ∧
      (seg.actualRun row).length = 11 ∧
      (seg.actualRun row).entry = shortEntry 13 (by decide) ((norm w).symm.trans e) := by
  have ht := h.append_right
  have hg := h.1
  simp only [cellDigits, List.cons_append, List.length_append, List.length_cons] at hg
  have hr : s+(cellWord 11 w).length < seg.length := by omega
  refine ⟨⟨_, hr⟩, rfl, ?_, ?_⟩
  · have hl := ht.actual_length 0 (by simp [cellDigits])
    simpa [cellDigits] using hl
  · exact h.cellWord_entry (n := 13) (by decide) (cells := w) (d := 2)
      (tail := List.replicate (if b then 11-2 else 11-1) 0 ++ tail) (by decide) e he


private noncomputable abbrev entry (off : ℕ) (e : Fin 14 ≃ Alphabet 14) : PermutationVertex 14 :=
  match off with
  | 0 => shortEntry 13 (by decide) e
  | j+1 => fullRunMapPower (by decide) j (fullEntry 13 (by decide) e)
private def index (off slot : ℕ) (i : Fin 14) : Fin 14 :=
  match off with
  | 0 => cellY 13 (by decide) (rot slot i)
  | j+1 => cellU 13 (by decide) ⟨prefixRotateIndex 14 12 j (rot slot i), prefixRotateIndex_lt (by decide) (rot slot i).isLt⟩

private theorem coordinates (off k : ℕ) (e : Fin 14 ≃ Alphabet 14) (i : Fin 14) :
    vertexCoordinates (runMapPower (by decide) k (entry off e)) i = e (index off k i) := by
  rw [runMapPower_coordinates (by decide)]
  cases off with
  | zero => simp only [entry,index,shortEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]
  | succ j =>
    rw [show entry (j+1) e = _ from rfl, fullRunMapPower_coordinates (by decide)]
    simp only [index,fullEntry,vertexCoordinates_coordinateVertex,Equiv.trans_apply,rot]

private theorem row_at {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 11 w ++ (cellDigits 11 b ++ tail)))
    (hs : s < seg.length) (e : Fin 14 ≃ Alphabet 14)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 13 (by decide) e)
    (off : ℕ) (hoff : off ≤ if b then 9 else 10) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 11 w).length + off ∧
      (seg.actualRun row).length = (if off = 0 then 11 else 13) ∧
      (seg.actualRun row).entry = entry off ((norm w).symm.trans e) := by
  obtain ⟨short, hshort, lshort, hentry⟩ := short_row w b tail h hs e he
  cases off with
  | zero => exact ⟨short,by omega,lshort,hentry⟩
  | succ j =>
    cases b with
    | false =>
      have hj : j < 10 := by change j+1 ≤ 10 at hoff; omega
      obtain ⟨row,hr,hl,he'⟩ := h.full_after_cells (n := 13) (by decide) hs e he j hj
      refine ⟨row,?_,hl,he'⟩
      change row.val = s+(cellWord 11 w).length+1+j at hr
      omega
    | true =>
      have hj : j < 9 := by change j+1 ≤ 9 at hoff; omega
      obtain ⟨row,hr,hl,he'⟩ := h.full_after_shortened_cells (n := 13) (by decide) hs e he j hj
      refine ⟨row,?_,hl,he'⟩
      change row.val = s+(cellWord 11 w).length+1+j at hr
      omega

theorem exclusion {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (oi oj i j : ℕ) (hi : oi ≤ if b₁ then 9 else 10) (hj : oj ≤ if b₂ then 9 else 10)
    (si : i < if oi=0 then 11 else 13) (sj : j < if oj=0 then 11 else 13)
    (order : (cellWord 11 a).length+oi < (cellWord 11 c).length+oj)
    (hit : ∀ k : Fin 14, (norm a).symm (index oi i k) = (norm c).symm (index oj j k)) :
    ¬ CellFactor 11 ws seg.deficitString := by
  intro hf
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := 13)
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := 13) (by decide)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append,List.length_cons,List.length_nil] at this; omega
  have at₁ : PatternAt seg s (cellWord 11 a ++ (cellDigits 11 b₁ ++ (cellWord 11 ta ++ [2,0]))) := by
    rw [h₁] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  have at₂ : PatternAt seg s (cellWord 11 c ++ (cellDigits 11 b₂ ++ (cellWord 11 tc ++ [2,0]))) := by
    rw [h₂] at h; simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := row_at _ _ _ at₁ hs e he oi hi
  obtain ⟨new,id₂,len₂,entry₂⟩ := row_at _ _ _ at₂ hs e he oj hj
  have hne := segment_actualRun_slots_ne seg old new (by omega) i j (by omega) (by omega)
  apply hne
  rw [entry₁,entry₂]
  apply congrArg rotationClass
  apply (show Function.Injective (@vertexCoordinates 14) from fun a b h => by
    simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex h)
  apply Equiv.ext
  intro t
  rw [coordinates,coordinates]
  exact congrArg e (hit t)

end SuperpermutationLowerBound.Refinement.Coupled.Extended
