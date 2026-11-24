import pairs.CompletedFactors
import pairs.InteriorFullRuns

namespace SuperpermutationLowerBound.Refinement.RunBound.Haruhi14
open PermutationVertex

set_option maxRecDepth 30000
set_option maxHeartbeats 7000000

private def pat (l r : ℕ) : List Bool :=
  completedChains (((List.replicate 1 [35,3]).flatten ++ [l,r]) ++
    (List.replicate 14 [35,3]).flatten)

private def x0 := completedChain 35 ++ [false,false]
private def y0 := completedPair 35 3 ++ List.replicate 33 false
private def rot (k : ℕ) (i : Fin 14) : Fin 14 :=
  ⟨prefixRotateIndex 14 13 k i, prefixRotateIndex_lt (by decide) i.2⟩

private abbrev norm (w : List Bool) := cellNormalization 13 (by decide) w

private theorem match_slots (w z : List Bool) (k l : ℕ)
    (hc : ∀ i : Fin 14, (norm w).symm (cellY 13 (by decide) (rot k i)) =
      (norm z).symm (cellU 13 (by decide) (rot l i)))
    (e : Fin 14 ≃ Alphabet 14) :
    runMapPower (by decide) k (shortEntry 13 (by decide) ((norm w).symm.trans e)) =
    runMapPower (by decide) l (fullEntry 13 (by decide) ((norm z).symm.trans e)) := by
  have eq : vertexCoordinates (runMapPower (by decide) k
      (shortEntry 13 (by decide) ((norm w).symm.trans e))) =
      vertexCoordinates (runMapPower (by decide) l
      (fullEntry 13 (by decide) ((norm z).symm.trans e))) := by
    apply Equiv.ext
    intro i
    rw [runMapPower_coordinates (by decide), runMapPower_coordinates (by decide)]
    simp only [shortEntry, fullEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
    exact congrArg e (hc i)
  simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex eq

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

private theorem full_row {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 11 w ++ (cellDigits 11 b ++ tail)))
    (hs : s < seg.length) (e : Fin 14 ≃ Alphabet 14)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 13 (by decide) e) :
    ∃ row : Fin seg.length, row.val = s + (cellWord 11 w).length+1 ∧
      (seg.actualRun row).length = 13 ∧
      (seg.actualRun row).entry = fullEntry 13 (by decide) ((norm w).symm.trans e) := by
  have ⟨short, hshort, _, hentry⟩ := short_row w b tail h hs e he
  have ht := h.append_right
  have hfin : short = ⟨s+(cellWord 11 w).length, by rw [← hshort]; exact short.isLt⟩ :=
    Fin.ext hshort
  rw [hfin] at hentry
  have hformula := ht.cell_full_entry (n := 13) (by decide) (b := b)
      ((norm w).symm.trans e) hentry
      0 (by cases b <;> decide)
  let g : ℕ := if b then 9 else 10
  have gpos : 0 < g := by cases b <;> decide
  have hs' : 1 < (cellDigits 11 b ++ tail).length := by cases b <;> simp [cellDigits]
  have hl := ht.actual_length 1 hs'
  have hr : s + (cellWord 11 w).length + 1 < seg.length := by have := ht.1; omega
  refine ⟨⟨_,hr⟩,rfl,?_,?_⟩
  · cases b <;> simpa [cellDigits] using hl
  · simpa only [fullRunMapPower, Function.iterate_zero_apply, Nat.add_zero] using hformula

private theorem exclusion {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (order : (cellWord 11 a).length ≤ (cellWord 11 c).length)
    (k l : ℕ) (hk' : k<11) (hl' : l<13)
    (hc : ∀ i : Fin 14, (norm a).symm (cellY 13 (by decide) (rot k i)) =
      (norm c).symm (cellU 13 (by decide) (rot l i))) :
    ¬ CellFactor 11 ws seg.deficitString := by
  intro hf
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := 13)
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := 13) (by decide)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append, List.length_cons, List.length_nil] at this; omega
  have at₁ : PatternAt seg s (cellWord 11 a ++ (cellDigits 11 b₁ ++ (cellWord 11 ta ++ [2,0]))) := by
    rw [h₁] at h
    simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  have at₂ : PatternAt seg s (cellWord 11 c ++ (cellDigits 11 b₂ ++ (cellWord 11 tc ++ [2,0]))) := by
    rw [h₂] at h
    simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := short_row _ _ _ at₁ hs e he
  obtain ⟨new,id₂,len₂,entry₂⟩ := full_row _ _ _ at₂ hs e he
  have hne := segment_actualRun_slots_ne seg old new (by omega) k l (by omega) (by omega)
  apply hne
  rw [entry₁, entry₂]
  exact congrArg rotationClass (match_slots _ _ _ _ hc e)

private theorem hx : ∀ i : Fin 14,
    (norm x0).symm (cellY 13 (by decide) (rot 0 i)) =
    (norm (pat 34 3)).symm (cellU 13 (by decide) (rot 2 i)) := by
  decide

theorem forbidX {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (completedChains (((List.replicate 1 [35,3]).flatten ++ [34,3]) ++
      (List.replicate 14 [35,3]).flatten) ++ [b]) seg.deficitString := by
  have hsplit : pat 34 3 = x0 ++ (pat 34 3).drop x0.length := by decide
  have horder : (cellWord 11 x0).length ≤ (cellWord 11 (pat 34 3)).length := by
    conv_rhs => rw [hsplit, cellWord_append, List.length_append]
    omega
  let ws := pat 34 3 ++ [b]
  exact exclusion seg ws x0 (pat 34 3) true b (ws.drop (x0.length + 1)) []
    (by cases b <;> decide) rfl horder 0 2 (by decide) (by decide) hx

private def fullRot (j : ℕ) (i : Fin 14) : Fin 14 :=
  ⟨prefixRotateIndex 14 12 j i, prefixRotateIndex_lt (by decide) i.2⟩

private theorem hy : ∀ i : Fin 14,
    (norm y0).symm (cellU 13 (by decide) (fullRot 9 (rot 11 i))) =
    (norm (pat 35 2)).symm (cellY 13 (by decide) (rot 0 i)) := by decide

private theorem equalY (e : Fin 14 ≃ Alphabet 14) :
    runMapPower (by decide) 11 (fullRunMapPower (by decide) 9
      (fullEntry 13 (by decide) ((norm y0).symm.trans e))) =
    runMapPower (by decide) 0 (shortEntry 13 (by decide) ((norm (pat 35 2)).symm.trans e)) := by
  apply (show Function.Injective (@vertexCoordinates 14) from fun a b h => by
    simpa only [coordinateVertex_vertexCoordinates] using congrArg coordinateVertex h)
  apply Equiv.ext
  intro i
  rw [runMapPower_coordinates (by decide), fullRunMapPower_coordinates (by decide),
      runMapPower_coordinates (by decide)]
  simp only [shortEntry, fullEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
  exact congrArg e (hy i)

theorem forbidY {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (completedChains (((List.replicate 1 [35,3]).flatten ++ [35,2]) ++
      (List.replicate 14 [35,3]).flatten) ++ [b]) seg.deficitString := by
  intro hf
  let ws := pat 35 2 ++ [b]
  obtain ⟨s,h⟩ := hf.exists_patternAt (n := 13)
  change PatternAt seg s (cellWord 11 ws ++ [2,0]) at h
  obtain ⟨e,he⟩ := h.cellWord_initial_coordinates (n := 13) (by decide)
  have hs : s < seg.length := by
    have := h.1; simp only [List.length_append, List.length_cons, List.length_nil] at this; omega
  let ta := ws.drop (y0.length+1)
  have hsplit : ws = y0 ++ false :: ta := by cases b <;> decide
  have h₁ : PatternAt seg s (cellWord 11 y0 ++ (cellDigits 11 false ++ (cellWord 11 ta ++ [2,0]))) := by
    rw [hsplit] at h
    simpa only [cellWord_append,cellWord_cons,List.append_assoc] using h
  have h₂ : PatternAt seg s (cellWord 11 (pat 35 2) ++ (cellDigits 11 b ++ [2,0])) := by
    simpa [ws,cellWord_append,cellWord_cons,cellWord,List.append_assoc] using h
  obtain ⟨old,id₁,len₁,entry₁⟩ := h₁.full_after_cells (n := 13) (by decide) hs e he 9 (by decide)
  obtain ⟨new,id₂,len₂,entry₂⟩ := short_row _ _ _ h₂ hs e he
  change old.val = s + (cellWord 11 y0).length + 1 + 9 at id₁
  have horder : (cellWord 11 y0).length + 10 < (cellWord 11 (pat 35 2)).length := by decide
  have hne := segment_actualRun_slots_ne seg old new (by omega) 11 0 (by omega) (by omega)
  apply hne
  rw [entry₁,entry₂]
  exact congrArg rotationClass (equalY e)

#print axioms forbidX
#print axioms forbidY
end SuperpermutationLowerBound.Refinement.RunBound.Haruhi14
