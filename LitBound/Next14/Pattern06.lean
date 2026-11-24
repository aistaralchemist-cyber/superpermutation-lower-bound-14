import LitBound.StrongGeometry

namespace SuperpermutationLowerBound.Refinement.Coupled.Next
open _root_.ChainReturns HaruhiLower.RunBound
set_option maxRecDepth 420000
set_option maxHeartbeats 80000000

def factor06 : List Chunk := [Y] ++ List.replicate 13 E ++ [X] ++ List.replicate 11 E ++ [Y] ++ [E]

theorem exclude06 {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells factor06 ++ [b]) seg.deficitString := by
  let u := cells factor06
  let a := u.take 11
  let c := u.take 1052
  let ws := u ++ [b]
  have hpre : c = a ++ [false,false] ++ c.drop (a.length+2) := by decide
  have hord : (cellWord 11 a).length + 3 < (cellWord 11 c).length + 0 := by
    conv_rhs => rw [hpre,cellWord_append,cellWord_append,List.length_append,List.length_append]
    have n : (cellWord 11 [false,false]).length ≥ 20 := by decide
    omega
  exact exclusion seg ws a c false false (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 3 0 8 0
    (by decide) (by decide) (by decide) (by decide) hord (by decide)

end SuperpermutationLowerBound.Refinement.Coupled.Next
