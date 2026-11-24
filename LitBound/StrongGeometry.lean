import LitBound.Geometry

namespace SuperpermutationLowerBound.Refinement.Coupled

open _root_.ChainReturns HaruhiLower.RunBound
set_option maxRecDepth 220000
set_option maxHeartbeats 12000000

/-- The critical cycle for the three-defect price is interrupted when the
next two unit defects use the same two gaps again. -/
def five : List Chunk := List.replicate 12 E ++ [Y] ++ gap ++ [Y] ++ gap ++
  [X] ++ List.replicate 12 E ++ [Y] ++ gap ++ [Y] ++ List.replicate 10 E

theorem forbid_five {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells five ++ [b]) seg.deficitString := by
  let u := cells five
  let a := u.take 19
  let c := u.take 2942
  let ws := u ++ [b]
  have hpre : c = a ++ c.drop a.length := by decide
  have hord : (cellWord 11 a).length + 0 < (cellWord 11 c).length + 3 := by
    conv_rhs => rw [hpre,cellWord_append,List.length_append]
    omega
  exact exclusion seg ws a c false false (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 0 3 0 5
    (by decide) (by decide) (by decide) (by decide) hord (by decide)

#print axioms forbid_five
end SuperpermutationLowerBound.Refinement.Coupled
