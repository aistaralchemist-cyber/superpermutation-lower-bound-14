import LitBound.Next14.Pattern00
import LitBound.Next14.Pattern01
import LitBound.Next14.Pattern02
import LitBound.Next14.Pattern03
import LitBound.Next14.Pattern04
import LitBound.Next14.Pattern05
import LitBound.Next14.Pattern06
import LitBound.Next14.Pattern07
import LitBound.Next14.Pattern08
import LitBound.Next14.Pattern09
import LitBound.Next14.Pattern10
import LitBound.Next14.Pattern11
import LitBound.Next14.Pattern12
import LitBound.Next14.Pattern13
import LitBound.Next14.Pattern14
import LitBound.Next14.Pattern15
import LitBound.Next14.Pattern16
import LitBound.Next14.Pattern17
import LitBound.Next14.Pattern18
import LitBound.Next14.Pattern19
import LitBound.Next14.Pattern20
import LitBound.Next14.Pattern21
import LitBound.Next14.Pattern22
import LitBound.Next14.Pattern23
import LitBound.Next14.Pattern24
import LitBound.StrongGeometry
import LitBound.Actual
import LitBound.Strong
import pairs.PaidOne
import pairs.VerifiedOne
import bridge.GenericTransfer

set_option maxRecDepth 240000
set_option maxHeartbeats 15000000

namespace SuperpermutationLowerBound.Refinement.Coupled.Next
open _root_.ChainReturns HaruhiLower.RunBound

def watch : List (List Chunk) := [x14,y14,xx,xy,yyy,five,factor00,factor01,factor02,factor03,factor04,factor05,factor06,factor07,factor08,factor09,factor10,factor11,factor12,factor13,factor14,factor15,factor16,factor17,factor18,factor19,factor20,factor21,factor22,factor23,factor24]
abbrev Price := ∀ v : List Chunk, ¬ List.replicate 15 E <:+: v →
  (∀ u ∈ watch, ¬u <:+: v) → 8*v.length ≤ 107*FourteenCuts.losses (v.map code) + 132

private theorem arithmetic (price : Price) (pre : List Chunk) (tail : List Chunk)
    (ht : tail.length ≤ 2) (chunks : List Chunk) (hchunks : chunks = pre ++ tail)
    (hvalid : ∀ c ∈ pre, OneInterior 4 c)
    (h15 : ¬ List.replicate 15 E <:+: pre)
    (hshort : ∀ u ∈ watch, ¬u <:+: pre)
    (hpay : -16 ≤ (tail.map (fun c => c.tile.loss 19)).sum) :
    2 * (tileLength (chunks.map Chunk.tile)) ≤ (7778/107 : ℚ) +
      (4058/107 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
  have bound := price pre h15 hshort
  have priced : ((FourteenCuts.losses (pre.map code) : ℕ) : ℚ) ≤ (pre.map (fun c => c.tile.loss 19)).sum := by
    simp only [FourteenCuts.losses,List.map_map,Nat.cast_list_sum,List.map_map]
    apply List.sum_le_sum
    exact fun c h => Coupled.cost_le c (hvalid c h)
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
  have bq : 8*(pre.length : ℚ) ≤ 107 * (FourteenCuts.losses (pre.map code) : ℚ) + 132 := by exact_mod_cast bound
  have cq : (tileChainCount (chunks.map Chunk.tile) : ℚ) ≤ 2 * (chunks.length : ℚ) := by exact_mod_cast count
  have lq : (chunks.length : ℚ) = pre.length + tail.length := by exact_mod_cast len
  have tq : (tail.length : ℚ) ≤ 2 := by exact_mod_cast ht
  change (List.map (fun c : Chunk => c.tile.loss 19) chunks).sum = _ at total
  linarith

private theorem priced_chains (price : Price) {ls d : List ℕ} (H : RealizesChains 11 ls d)
    (hbound : ∀ x ∈ ls, x ≤ onePeriod 4 - 1) (hsucc : OneSuccessors 4 ls) (hne : ls ≠ [])
    (h15 : ¬ CellFactor 11 (repeatedCells (completedPair 35 3) 15) d)
    (hbad : ∀ u ∈ watch, ∀ b, ¬ CellFactor 11 (cells u ++ [b]) d) :
    2*(ls.sum : ℚ) ≤ (7778/107 : ℚ) + (4058/107 : ℚ) * ((ls.length : ℚ)-1) := by
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
  have htest : 2 * tileLength (chunks.map Chunk.tile) ≤ (7778/107 : ℚ) +
      (4058/107 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
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
        obtain ⟨b,hb⟩ := Coupled.boundary_factor H flat eq3 hit
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
    ChainPacking 11 (3889/107) (4058/107) s.deficitString := by
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
  have hsum : 2*(ls.sum : ℚ) ≤ (7778/107 : ℚ) + (4058/107 : ℚ) * ((ls.length : ℚ)-1) := by
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
theorem packing_of_price (price : Price) : ActualPacking 14 (by decide) (3889/107) (4058/107) := fun p hp s =>
    packing14_of_window price s (by
      intro u hu b
      simp only [watch,List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact RunBound.Haruhi14.forbidX s b
      · exact RunBound.Haruhi14.forbidY s b
      · exact forbid_xx s b
      · exact forbid_xy s b
      · exact forbid_yyy s b
      · exact forbid_five s b
      · exact exclude00 s b
      · exact exclude01 s b
      · exact exclude02 s b
      · exact exclude03 s b
      · exact exclude04 s b
      · exact exclude05 s b
      · exact exclude06 s b
      · exact exclude07 s b
      · exact exclude08 s b
      · exact exclude09 s b
      · exact exclude10 s b
      · exact exclude11 s b
      · exact exclude12 s b
      · exact exclude13 s b
      · exact exclude14 s b
      · exact exclude15 s b
      · exact exclude16 s b
      · exact exclude17 s b
      · exact exclude18 s b
      · exact exclude19 s b
      · exact exclude20 s b
      · exact exclude21 s b
      · exact exclude22 s b
      · exact exclude23 s b
      · exact exclude24 s b)

open _root_.SuperpermutationLowerBound.ChainReturns in
theorem shortest_of_price (price : Price) :
    93891141157 ≤ shortestSuperpermutationLength 14 := by
  have ha : Admissible 13 (3889/107) (4058/107) := by constructor <;> norm_num
  have actual := packing_of_price price
  have hh := shortest_bound_of_actualPacking (by decide : 8 ≤ 14) ha actual
  have val : bound 14 (3889/107) (4058/107) = 93891141157 := by
    have hceil : ⌈((69157292976563 : ℚ) / 142349)⌉₊ = 485829146 := by
      apply (Nat.ceil_eq_iff (by norm_num)).2; norm_num
    norm_num [bound,lam,intercept,Nat.factorial,hceil]
  rwa [val] at hh


end SuperpermutationLowerBound.Refinement.Coupled.Next
