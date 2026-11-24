import LitBound.Next14.PriceData

namespace HaruhiNextPrice
set_option maxHeartbeats 12000000
set_option maxRecDepth 40000
theorem rowGroup00 : ∀ i : Fin 32, rowAt (0 + i.val) = true := by decide
theorem rowGroup01 : ∀ i : Fin 32, rowAt (32 + i.val) = true := by decide
theorem rowGroup02 : ∀ i : Fin 32, rowAt (64 + i.val) = true := by decide
theorem rowGroup03 : ∀ i : Fin 32, rowAt (96 + i.val) = true := by decide
theorem rowGroup04 : ∀ i : Fin 32, rowAt (128 + i.val) = true := by decide
theorem rowGroup05 : ∀ i : Fin 32, rowAt (160 + i.val) = true := by decide
theorem rowGroup06 : ∀ i : Fin 32, rowAt (192 + i.val) = true := by decide
theorem rowGroup07 : ∀ i : Fin 32, rowAt (224 + i.val) = true := by decide
theorem rowGroup08 : ∀ i : Fin 32, rowAt (256 + i.val) = true := by decide
theorem rowGroup09 : ∀ i : Fin 32, rowAt (288 + i.val) = true := by decide
end HaruhiNextPrice
