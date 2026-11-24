import LitBound.Next14.ShortRows

namespace SuperpermutationLowerBound.Refinement.Coupled.Next
open _root_.ChainReturns HaruhiLower.RunBound
set_option maxRecDepth 420000
set_option maxHeartbeats 80000000

def factor17 : List Chunk := List.replicate 12 E ++ [X] ++ List.replicate 12 E ++ [Y] ++ List.replicate 13 E ++ [Y] ++ List.replicate 12 E ++ [Y] ++ List.replicate 12 E ++ [Y] ++ List.replicate 5 E

theorem exclude17 {hk : 7 ≤ 14} {p : OverlapPath 14} {hp : IsBlockAligned p}
    (seg : BlockAlignedLightSegment hk p hp) (b : Bool) :
    ¬ CellFactor 11 (cells factor17 ++ [b]) seg.deficitString := by
  let u := cells factor17
  let a := u.take 34
  let c := u.take 2656
  let ws := u ++ [b]
  have hpre : c = a ++ [true,false] ++ c.drop (a.length+2) := by decide
  have hord : (cellWord 11 a).length + 7 < (cellWord 11 c).length + 9 := by
    conv_rhs => rw [hpre,cellWord_append,cellWord_append,List.length_append,List.length_append]
    have n : (cellWord 11 [true,false]).length ≥ 20 := by decide
    omega
  exact Extended.exclusion seg ws a c true false (ws.drop (a.length+1)) (ws.drop (c.length+1))
    (by cases b <;> decide) (by cases b <;> decide) 7 9 7 0
    (by decide) (by decide) (by decide) (by decide) hord (by decide)

end SuperpermutationLowerBound.Refinement.Coupled.Next
