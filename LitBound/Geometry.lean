import RunBound.Bound
import pairs.InteriorFullRuns

namespace SuperpermutationLowerBound.Refinement.Coupled
open PermutationVertex _root_.ChainReturns HaruhiLower.RunBound

set_option maxRecDepth 140000
set_option maxHeartbeats 10000000

abbrev gap := List.replicate 13 E
def xx : List Chunk := [E,X] ++ gap ++ [X,E]
def xy : List Chunk := [X] ++ gap ++ [Y]
def yyy : List Chunk := [Y] ++ gap ++ [Y] ++ gap ++ [Y] ++ List.replicate 6 E
abbrev cells (w : List Chunk) := completedChains ((w.map Chunk.chains).flatten)

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

private theorem row_at {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    {seg : BlockAlignedLightSegment hk p hp} {s : ℕ} (w : List Bool) (b : Bool) (tail : List ℕ)
    (h : PatternAt seg s (cellWord 11 w ++ (cellDigits 11 b ++ tail)))
    (hs : s < seg.length) (e : Fin 14 ≃ Alphabet 14)
    (he : (seg.actualRun ⟨s,hs⟩).entry = shortEntry 13 (by decide) e)
    (off : ℕ) (hoff : off ≤ if b then 1 else 10) :
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
      have hzero : j=0 := by change j+1 ≤ 1 at hoff; omega
      subst j
      obtain ⟨row,hr,hl,he'⟩ := full_row w true tail h hs e he
      exact ⟨row,hr,hl,by simpa only [entry,fullRunMapPower,Function.iterate_zero_apply] using he'⟩

theorem exclusion {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (ws a c : List Bool) (b₁ b₂ : Bool)
    (ta tc : List Bool) (h₁ : ws = a ++ b₁ :: ta) (h₂ : ws = c ++ b₂ :: tc)
    (oi oj i j : ℕ) (hi : oi ≤ if b₁ then 1 else 10) (hj : oj ≤ if b₂ then 1 else 10)
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

theorem forbid_xx {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells xx ++ [b]) seg.deficitString := by
  let u := cells xx
  let a := u.take 27
  let c := u.take 612
  let ws := u ++ [b]
  exact exclusion seg ws a c false false (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 1 10 2 0
    (by decide) (by cases b <;> decide) (by decide) (by decide) (by decide) (by decide)
#print axioms forbid_xx

theorem forbid_xy {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells xy ++ [b]) seg.deficitString := by
  let u := cells xy
  let a := u.take 33
  let c := u
  let ws := u ++ [b]
  exact exclusion seg ws a c true b (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 0 1 0 4
    (by decide) (by cases b <;> decide) (by decide) (by decide) (by decide) (by decide)
#print axioms forbid_xy

theorem forbid_yyy {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells yyy ++ [b]) seg.deficitString := by
  let u := cells yyy
  let a := u.take 0
  let c := u.take 1322
  let ws := u ++ [b]
  exact exclusion seg ws a c false false (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 3 7 4 0
    (by decide) (by cases b <;> decide) (by decide) (by decide) (by change 0+3 < _+7; omega) (by decide)
#print axioms forbid_yyy
end SuperpermutationLowerBound.Refinement.Coupled
