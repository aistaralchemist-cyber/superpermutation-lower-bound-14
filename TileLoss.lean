import Std

/-! Pure counting consequence of the two literal 29-tile exclusions. -/
namespace FourteenCuts

inductive Tile where
  | efficient | shortFirst | shortSecond | other
  deriving DecidableEq, Repr

def loss : Tile → Nat
  | .efficient => 0
  | .shortFirst | .shortSecond => 1
  | .other => 2

abbrev zeroes (n : Nat) := List.replicate n Tile.efficient
def losses (xs : List Tile) := (xs.map loss).sum

private theorem sum_append (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

private theorem shape_of_low (xs : List Tile) (h : losses xs ≤ 1) :
    (∃ a, xs = zeroes a) ∨
    ∃ a b t, (t = .shortFirst ∨ t = .shortSecond) ∧ xs = zeroes a ++ t :: zeroes b := by
  induction xs with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons x xs ih =>
    change loss x + losses xs ≤ 1 at h
    rcases ih (by omega) with ⟨a, rfl⟩ | ⟨a,b,t,ht,rfl⟩
    · cases x with
      | efficient => exact Or.inl ⟨a+1, rfl⟩
      | shortFirst => exact Or.inr ⟨0,a,_,.inl rfl,rfl⟩
      | shortSecond => exact Or.inr ⟨0,a,_,.inr rfl,rfl⟩
      | other => simp only [loss] at h; omega
    · have lower : 1 ≤ losses (zeroes a ++ t :: zeroes b) := by
        rw [losses,List.map_append,sum_append,List.map_cons,List.sum_cons]
        rcases ht with rfl|rfl <;> simp [loss]
      have hx : loss x = 0 := by omega
      cases x with
      | efficient => exact Or.inr ⟨a+1,b,t,ht,rfl⟩
      | shortFirst | shortSecond | other => contradiction

private theorem replicate_factor (x : Tile) (a b : Nat) (hle : a ≤ b) :
    List.replicate a x <:+: List.replicate b x := by
  refine ⟨[], List.replicate (b-a) x, ?_⟩
  simp [Nat.add_sub_of_le hle]

/-- If fifteen efficient tiles cannot occur and the two low-loss
centered words cannot occur, every 29-tile window loses at least two. -/
theorem loss_at_29 (xs : List Tile) (hlen : xs.length = 29)
    (h15 : ¬ zeroes 15 <:+: xs)
    (hX : xs ≠ zeroes 14 ++ Tile.shortFirst :: zeroes 14)
    (hY : xs ≠ zeroes 14 ++ Tile.shortSecond :: zeroes 14) :
    2 ≤ losses xs := by
  apply Nat.le_of_not_gt
  intro hl
  rcases shape_of_low xs (by omega) with ⟨a,rfl⟩|⟨a,b,t,ht,rfl⟩
  · exact h15 (replicate_factor _ _ _ (by simp [zeroes] at hlen; omega))
  · have ha : a < 15 := Nat.lt_of_not_ge (fun h =>
       h15 ((replicate_factor _ 15 a h).trans (List.prefix_append _ _).isInfix))
    have hb : b < 15 := Nat.lt_of_not_ge (fun h =>
       h15 ((replicate_factor _ 15 b h).trans (by simpa [List.append_assoc] using (List.suffix_append (zeroes a ++ [t]) (zeroes b)).isInfix)))
    simp only [List.length_append,List.length_cons,List.length_replicate] at hlen
    have ea : a = 14 := by omega
    have eb : b = 14 := by omega
    subst a; subst b
    rcases ht with rfl|rfl
    · exact hX rfl
    · exact hY rfl

/-- Disjoint 29-tile windows bound the total loss, including a remainder. -/
theorem total_loss (xs : List Tile)
    (hw : ∀ w, w <:+: xs → w.length = 29 → 2 ≤ losses w) :
    2 * xs.length ≤ 29 * losses xs + 56 := by
  induction len : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    by_cases hn : n < 29
    · omega
    · let front := xs.take 29
      let rest := xs.drop 29
      have hlen : front.length = 29 := by simp [front,List.length_take,len]; omega
      have hrest : rest.length < n := by simp [rest,List.length_drop,len]; omega
      have gain := hw front (List.take_prefix ..).isInfix hlen
      have tail := ih _ hrest rest (fun w hi => hw w (hi.trans (List.drop_suffix ..).isInfix)) rfl
      have whole : front ++ rest = xs := List.take_append_drop .. 
      have hsum : losses xs = losses front + losses rest := by
        rw [←whole,losses,List.map_append,sum_append]; rfl
      have hlen' := congrArg List.length whole
      simp only [List.length_append] at hlen'
      omega

end FourteenCuts
