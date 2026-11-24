import TileLoss
import RunBound.Abstract

namespace FourteenCuts.RunBound
/-- Specialization of the potential inequality to the four tile types
used by the fourteen-symbol chain chart. -/
theorem run_charging (r : Nat) (hr : 2 ≤ r) (xs : List Tile)
    (cap : ¬zeroes (r+1) <:+: xs)
    (forbid : ∀ z, loss z = 1 → ¬ (Tile.efficient :: z :: zeroes r) <:+: xs) :
    xs.length ≤ r * losses xs + r := by
  apply _root_.RunBound.Abstract.run_charging Tile.efficient loss _ r hr xs cap forbid
  intro z
  cases z <;> decide
#print axioms run_charging
end FourteenCuts.RunBound
