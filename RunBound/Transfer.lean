import RunBound.Factors
import pairs.VerifiedOne
import bridge.NumericalEvaluations
import bridge.GenericTransfer

namespace SuperpermutationLowerBound.Refinement.RunBound
open _root_.ChainReturns HaruhiLower.RunBound

/-- When two sixteen-tile windows are excluded from every actual light segment,
the 14-symbol chain-to-word lower-bound transfer gives 93,891,141,154. -/
theorem packing14_of_window {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp)
    (hbad : ∀ z ∈ [X,Y], ∀ b, ¬ CellFactor 11 (hardCells z.chains ++ [b]) s.deficitString) :
    ChainPacking 11 (1011/28) (531/14) s.deficitString := by
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
  have hsum : 2*(ls.sum : ℚ) ≤ (1011/14 : ℚ) + (531/14 : ℚ) * ((ls.length : ℚ)-1) := by
    by_cases hlen : 2 ≤ ls.length
    · exact priced_chains hreal
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
theorem improved14_of_windows
    (geom : ∀ (p : OverlapPath 14) (hp : IsBlockAligned p)
      (s : BlockAlignedLightSegment (by decide : 7 ≤ 14) p hp),
      ∀ z ∈ [X,Y], ∀ b, ¬ CellFactor 11 (hardCells z.chains ++ [b]) s.deficitString) :
    93891141154 ≤ shortestSuperpermutationLength 14 := by
  have ha : Admissible 13 (1011/28) (531/14) := by constructor <;> norm_num
  have actual : ActualPacking 14 (by decide) (1011/28) (531/14) := fun p hp s =>
    packing14_of_window s (geom p hp s)
  have hh := shortest_bound_of_actualPacking (by decide : 8 ≤ 14) ha actual
  have val : bound 14 (1011/28) (531/14) = 93891141154 := by
    have hceil : ⌈((36197671895634 : ℚ) / 74507)⌉₊ = 485829143 := by
      apply (Nat.ceil_eq_iff (by norm_num)).2; norm_num
    norm_num [bound,lam,intercept,Nat.factorial,hceil]
  rwa [val] at hh

#print axioms improved14_of_windows
end SuperpermutationLowerBound.Refinement.RunBound
