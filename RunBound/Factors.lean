import RunBound.Arithmetic
import pairs.CompletedFactors
import pairs.PaidOne

namespace SuperpermutationLowerBound.Refinement.RunBound
open _root_.ChainReturns HaruhiLower.RunBound
abbrev AsPairs (k : ℕ) : List ℕ := (List.replicate k [35,3]).flatten
abbrev hardCells (z : List ℕ) := completedChains ((AsPairs 1 ++ z) ++ AsPairs 14)

private theorem cells_nonempty (c : Chunk) : completedChains c.chains ≠ [] := by
  cases c <;> simp [Chunk.chains, completedChains, completedChain]

private theorem flatten_window (z : Chunk) :
    ((List.replicate 1 E ++ z :: List.replicate 14 E).map Chunk.chains).flatten =
      (AsPairs 1 ++ z.chains) ++ AsPairs 14 := by simp [Chunk.chains, E, AsPairs]

/-- A middle window with two following tiles contains the first complete
cell of its successor. This makes the case of a terminal chain explicit. -/
private theorem boundary_factor {ls d : List ℕ} (H : RealizesChains 11 ls d)
    {chunks pre : List Chunk} {f l z : Chunk}
    (flat : (chunks.map Chunk.chains).flatten = ls) (split : chunks = pre ++ [f,l])
    (hit : List.replicate 1 E ++ z :: List.replicate 14 E <:+: pre) :
    ∃ b : Bool, CellFactor 11 (hardCells z.chains ++ [b]) d := by
  obtain ⟨left,right,he⟩ := hit
  let middle := List.replicate 1 E ++ z :: List.replicate 14 E
  have hmid : middle ≠ [] := by simp [middle]
  have useNext (c : Chunk) (tail : List Chunk) (ht : tail ≠ [])
      (hs : chunks = left ++ (middle ++ [c]) ++ tail) : ∃ b, CellFactor 11 (hardCells z.chains ++ [b]) d := by
    have hf := completed_chunk_factor flat (by simp : middle ++ [c] ≠ []) ht hs
    rw [List.map_append,List.flatten_append,List.map_singleton,List.flatten_singleton,
      completedChains_append,show (middle.map Chunk.chains).flatten = _ from flatten_window z] at hf
    obtain ⟨b,bs,hb⟩ := List.exists_cons_of_ne_nil (cells_nonempty c)
    rw [hb] at hf
    exact ⟨b, H _ ((show MarkFactor (hardCells z.chains ++ [b]) (hardCells z.chains ++ b::bs) from
      ⟨[],bs,by simp⟩).trans hf)⟩
  cases right with
  | nil => apply useNext f [l] (by simp); simp [split,←he,middle,List.append_assoc]
  | cons c after =>
    apply useNext c (after ++ [f,l]) (by simp)
    simp [split,←he,middle,List.append_assoc]

theorem priced_chains {ls d : List ℕ} (H : RealizesChains 11 ls d)
    (hbound : ∀ x ∈ ls, x ≤ onePeriod 4 - 1) (hsucc : OneSuccessors 4 ls) (hne : ls ≠ [])
    (h15 : ¬ CellFactor 11 (repeatedCells (completedPair 35 3) 15) d)
    (hbad : ∀ z ∈ [X,Y], ∀ b, ¬ CellFactor 11 (hardCells z.chains ++ [b]) d) :
    2*(ls.sum : ℚ) ≤ (1011/14 : ℚ) + (531/14 : ℚ) * ((ls.length : ℚ)-1) := by
  let chunks := greedyChunks 4 ls
  have cn : chunks ≠ [] := greedyChunks_ne_nil 4 hne
  let last := chunks.getLast cn
  let trunk := chunks.dropLast
  have eq : chunks = trunk ++ [last] := (List.dropLast_append_getLast cn).symm
  have valid := greedy_one_valid 4 ls hbound hsucc
  have flat : (chunks.map Chunk.chains).flatten = ls := greedyChunks_flatten 4 ls
  have finalPrice : -(16:ℚ) ≤ last.tile.loss 19 := by
    have hh := oneFinal_loss 4 (by decide) last (valid.last cn)
    norm_num [oneMean] at hh
    exact hh
  have htest : 2 * tileLength (chunks.map Chunk.tile) ≤ (1011/14 : ℚ) +
      (531/14 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
    by_cases hz : trunk = []
    · refine arithmetic [] [last] (by simp) chunks (by simpa [hz] using eq) (by simp) ?_ ?_ ?_
      · intro hi; have := hi.length_le; simp at this
      · intro z _ hi; have := hi.length_le; simp at this
      · simpa using finalPrice
    · let f := trunk.getLast hz
      let pre := trunk.dropLast
      have eq2 : trunk = pre ++ [f] := (List.dropLast_append_getLast hz).symm
      have eq3 : chunks = pre ++ [f,last] := by calc
        chunks = trunk ++ [last] := eq
        _ = _ := by rw [eq2]; simp
      have vint : ∀ c ∈ trunk, OneInterior 4 c := valid.interior
      apply arithmetic pre [f,last] (by simp) chunks eq3
      · intro c hc; exact vint c (eq2 ▸ List.mem_append_left _ hc)
      · rintro ⟨left,right,he⟩
        have factor := repeated_pair_factor_of_chunks flat 35 3 15 (by decide)
          (by simp : right ++ [f,last] ≠ [])
          (show chunks = left ++ List.replicate 15 (.pair 35 3) ++ (right ++ [f,last]) by
            rw [eq3,←he]; simp [E,List.append_assoc])
        exact h15 (H _ factor)
      · intro z hz' hit
        obtain ⟨b,hb⟩ := boundary_factor H flat eq3 hit
        exact hbad z hz' b hb
      · have intf := vint f (eq2 ▸ (by simp))
        have hprice := oneInterior_pay 4 (by decide) f intf
        norm_num [oneMean] at hprice
        simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero]
        rcases hprice with h|h <;> linarith
  simpa [chunks,greedyChunks_tiles,greedyTiles_chainLength,greedyTiles_chainCount] using htest

end SuperpermutationLowerBound.Refinement.RunBound
