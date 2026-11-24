import LitBound.Geometry
import pairs.PaidOne
import pairs.VerifiedOne
import bridge.GenericTransfer

namespace SuperpermutationLowerBound.Refinement.Coupled
open _root_.ChainReturns HaruhiLower.RunBound

def x14 : List Chunk := E :: X :: List.replicate 14 E
def y14 : List Chunk := E :: Y :: List.replicate 14 E
def watch : List (List Chunk) := [x14,y14,xx,xy,yyy]
abbrev Price := ∀ v : List Chunk, ¬ List.replicate 15 E <:+: v →
  (∀ u ∈ watch, ¬u <:+: v) → 3*v.length ≤ 41*FourteenCuts.losses (v.map code) + 45

theorem cost_le (c : Chunk) (h : OneInterior 4 c) :
    ((FourteenCuts.loss (code c) : ℕ) : ℚ) ≤ c.tile.loss 19 := by
  cases c with
  | single x =>
    change x ≤ 4 at h
    simp [code,E,X,Y,FourteenCuts.loss,Chunk.tile,Tile.loss]
    have hh : (x : ℚ) ≤ 4 := by exact_mod_cast h
    linarith
  | pair x y =>
    change x ≤ 35 ∧ y ≤ 3 at h
    unfold code
    split_ifs with h0 h1 h2
    · simp only [E,Chunk.pair.injEq] at h0
      rcases h0 with ⟨rfl,rfl⟩
      norm_num [FourteenCuts.loss,Chunk.tile,Tile.loss]
    · simp only [X,Chunk.pair.injEq] at h1
      rcases h1 with ⟨rfl,rfl⟩
      norm_num [FourteenCuts.loss,Chunk.tile,Tile.loss]
    · simp only [Y,Chunk.pair.injEq] at h2
      rcases h2 with ⟨rfl,rfl⟩
      norm_num [FourteenCuts.loss,Chunk.tile,Tile.loss]
    · simp only [E,X,Y,Chunk.pair.injEq] at *
      have hh : x + y ≤ 36 := by omega
      norm_num [FourteenCuts.loss,Chunk.tile,Tile.loss]
      have hhQ : (x : ℚ) + y ≤ 36 := by exact_mod_cast hh
      linarith

private theorem arithmetic (price : Price) (pre : List Chunk) (tail : List Chunk)
    (ht : tail.length ≤ 2) (chunks : List Chunk) (hchunks : chunks = pre ++ tail)
    (hvalid : ∀ c ∈ pre, OneInterior 4 c)
    (h15 : ¬ List.replicate 15 E <:+: pre)
    (hshort : ∀ u ∈ watch, ¬u <:+: pre)
    (hpay : -16 ≤ (tail.map (fun c => c.tile.loss 19)).sum) :
    2 * (tileLength (chunks.map Chunk.tile)) ≤ (2969/41 : ℚ) +
      (1555/41 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
  have bound := price pre h15 hshort
  have priced : ((FourteenCuts.losses (pre.map code) : ℕ) : ℚ) ≤ (pre.map (fun c => c.tile.loss 19)).sum := by
    simp only [FourteenCuts.losses,List.map_map,Nat.cast_list_sum,List.map_map]
    apply List.sum_le_sum
    exact fun c h => cost_le c (hvalid c h)
  have count := tile_count_le_twice_length (chunks.map Chunk.tile) (by
    simp only [List.forall_mem_map]
    intro c _; cases c <;> simp [Chunk.tile])
  simp only [List.length_map] at count
  have total := tile_loss_sum (19 : ℚ) (chunks.map Chunk.tile)
  simp only [List.map_map] at total
  have sumsplit : (List.map (fun c : Chunk => c.tile.loss 19) chunks).sum =
      (pre.map (fun c => c.tile.loss 19)).sum + (tail.map (fun c => c.tile.loss 19)).sum := by
    simp [hchunks]
  have len : chunks.length = pre.length + tail.length := by simp [hchunks]
  have bq : 3*(pre.length : ℚ) ≤ 41 * (FourteenCuts.losses (pre.map code) : ℚ) + 45 := by exact_mod_cast bound
  have cq : (tileChainCount (chunks.map Chunk.tile) : ℚ) ≤ 2 * (chunks.length : ℚ) := by exact_mod_cast count
  have lq : (chunks.length : ℚ) = pre.length + tail.length := by exact_mod_cast len
  have tq : (tail.length : ℚ) ≤ 2 := by exact_mod_cast ht
  change (List.map (fun c : Chunk => c.tile.loss 19) chunks).sum = _ at total
  linarith

private theorem cells_nonempty (c : Chunk) : completedChains c.chains ≠ [] := by
  cases c <;> simp [Chunk.chains, completedChains, completedChain]

/-- A middle window with two following tiles contains the first complete
cell of its successor. This makes the case of a terminal chain explicit. -/
theorem boundary_factor {ls d : List ℕ} (H : RealizesChains 11 ls d)
    {chunks pre : List Chunk} {f l : Chunk} {middle : List Chunk}
    (flat : (chunks.map Chunk.chains).flatten = ls) (split : chunks = pre ++ [f,l])
    (hit : middle <:+: pre) :
    ∃ b : Bool, CellFactor 11 (cells middle ++ [b]) d := by
  obtain ⟨left,right,he⟩ := hit
  have useNext (c : Chunk) (tail : List Chunk) (ht : tail ≠ [])
      (hs : chunks = left ++ (middle ++ [c]) ++ tail) : ∃ b, CellFactor 11 (cells middle ++ [b]) d := by
    have hf := completed_chunk_factor flat (by simp : middle ++ [c] ≠ []) ht hs
    rw [List.map_append,List.flatten_append,List.map_singleton,List.flatten_singleton,
      completedChains_append] at hf
    obtain ⟨b,bs,hb⟩ := List.exists_cons_of_ne_nil (cells_nonempty c)
    rw [hb] at hf
    exact ⟨b, H _ ((show MarkFactor (cells middle ++ [b]) (cells middle ++ b::bs) from
      ⟨[],bs,by simp⟩).trans hf)⟩
  cases right with
  | nil => apply useNext f [l] (by simp); simp [split,←he,List.append_assoc]
  | cons c after =>
    apply useNext c (after ++ [f,l]) (by simp)
    simp [split,←he,List.append_assoc]

private theorem priced_chains (price : Price) {ls d : List ℕ} (H : RealizesChains 11 ls d)
    (hbound : ∀ x ∈ ls, x ≤ onePeriod 4 - 1) (hsucc : OneSuccessors 4 ls) (hne : ls ≠ [])
    (h15 : ¬ CellFactor 11 (repeatedCells (completedPair 35 3) 15) d)
    (hbad : ∀ u ∈ watch, ∀ b, ¬ CellFactor 11 (cells u ++ [b]) d) :
    2*(ls.sum : ℚ) ≤ (2969/41 : ℚ) + (1555/41 : ℚ) * ((ls.length : ℚ)-1) := by
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
  have htest : 2 * tileLength (chunks.map Chunk.tile) ≤ (2969/41 : ℚ) +
      (1555/41 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
    by_cases hz : trunk = []
    · refine arithmetic price [] [last] (by simp) chunks (by simpa [hz] using eq) (by simp) ?_ ?_ ?_
      · intro hi; have := hi.length_le; simp at this
      · intro u hu hi; have hh := hi.length_le
        have hpos : ∀ m ∈ watch, 0 < m.length := by decide
        exact (Nat.not_lt_of_ge hh) (hpos u hu)
      · simpa using finalPrice
    · let f := trunk.getLast hz
      let pre := trunk.dropLast
      have eq2 : trunk = pre ++ [f] := (List.dropLast_append_getLast hz).symm
      have eq3 : chunks = pre ++ [f,last] := by calc
        chunks = trunk ++ [last] := eq
        _ = _ := by rw [eq2]; simp
      have vint : ∀ c ∈ trunk, OneInterior 4 c := valid.interior
      apply arithmetic price pre [f,last] (by simp) chunks eq3
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

theorem packing14_of_window (price : Price) {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp)
    (hbad : ∀ u ∈ watch, ∀ b, ¬ CellFactor 11 (cells u ++ [b]) s.deficitString) :
    ChainPacking 11 (2969/82) (1555/41) s.deficitString := by
  have avoid := actual_segment_returnAvoidance (n := 13) (by decide) s
  have local14 : ResidueOneAvoidance 11 4 s.deficitString := avoid.residueOne (by decide)
  have basic14 : BasicCellAvoidance 11 (onePeriod 4) s.deficitString := by
    have hh : period 13 = onePeriod 4 := period_onePeriod 4
    simpa only [hh] using avoid.basic
  have horder := ChainReturns.efficientOne_return 4 (by decide) (by decide)
  have horder' : (cellRho 13 (by decide) * cellG 13 (by decide) ^ 3 *
      cellRho 13 (by decide) * (cellG 13 (by decide))⁻¹)^15 = 1 := by
    exact horder
  have hrep : ¬CellFactor 11 (repeatedCells (completedPair 35 3) 15) s.deficitString := by
    apply actual_periodic_pair_avoidance 13 (by decide) p hp s 35 3 15 (by decide) (by decide) (by decide)
    rw [show cellG 13 (by decide) ^ 35 = (cellG 13 (by decide))⁻¹ from
      cellG_onePeriod_pred 4 (by decide) (by decide)]
    exact horder'
  intro gaps hg before after hd
  let ls := chainLengths 11 gaps
  have hreal : RealizesChains 11 ls s.deficitString := realizes_chainLengths (by decide) hg hd
  have hpos : ∀ x ∈ ls, 1 ≤ x := chainLengths_positive 11 gaps
  have hne : ls ≠ [] := chainLengthsFrom_nonempty 11 1 gaps
  have hsum : 2*(ls.sum : ℚ) ≤ (2969/41 : ℚ) + (1555/41 : ℚ) * ((ls.length : ℚ)-1) := by
    by_cases hlen : 2 ≤ ls.length
    · exact priced_chains price hreal
        (chain_bound_of_basic (by decide : 1 ≤ onePeriod 4) hreal hpos basic14 hlen)
        (oneSuccessors_of_avoidance hreal hpos local14) hne hrep hbad
    · have hlen1 : ls.length = 1 := by have := List.length_pos_iff.mpr hne; omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
      have hb := chain_bound_of_pure hreal basic14.pure x (by simp [hx])
      change x ≤ 36 at hb
      simp [hx]; have hxq : (x : ℚ) ≤ 36 := by exact_mod_cast hb
      linarith
  dsimp [ls] at hsum
  rw [chainLengths_sum,chainLengths_length] at hsum
  push_cast at hsum
  linarith

open _root_.SuperpermutationLowerBound.ChainReturns in
theorem shortest_of_price (price : Price) :
    93891141155 ≤ shortestSuperpermutationLength 14 := by
  have ha : Admissible 13 (2969/82) (1555/41) := by constructor <;> norm_num
  have actual : ActualPacking 14 (by decide) (2969/82) (1555/41) := fun p hp s =>
    packing14_of_window price s (by
      intro u hu b
      simp only [watch,List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl|rfl|rfl|rfl|rfl
      · exact RunBound.Haruhi14.forbidX s b
      · exact RunBound.Haruhi14.forbidY s b
      · exact forbid_xx s b
      · exact forbid_xy s b
      · exact forbid_yyy s b)
  have hh := shortest_bound_of_actualPacking (by decide : 8 ≤ 14) ha actual
  have val : bound 14 (2969/82) (1555/41) = 93891141155 := by
    have hceil : ⌈((106002575035142 : ℚ) / 218189)⌉₊ = 485829144 := by
      apply (Nat.ceil_eq_iff (by norm_num)).2; norm_num
    norm_num [bound,lam,intercept,Nat.factorial,hceil]
  rwa [val] at hh


#print axioms shortest_of_price
end SuperpermutationLowerBound.Refinement.Coupled
