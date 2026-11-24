import Std

namespace RunBound.Abstract
variable {α : Type u} [DecidableEq α]
private abbrev zeroes (a : α) (n : Nat) := List.replicate n a
private def lead (a : α) : List α → Nat
  | [] => 0
  | x :: xs => if x = a then lead a xs + 1 else 0

private theorem split_lead (a : α) (xs : List α) :
    xs = zeroes a (lead a xs) ∨ ∃ z tl, z ≠ a ∧ xs = zeroes a (lead a xs) ++ z :: tl := by
  induction xs with
  | nil => exact .inl rfl
  | cons x xs ih =>
    by_cases hx : x = a
    · subst x
      rcases ih with h|⟨z,tl,hz,h⟩
      · exact .inl (by simpa [lead,List.replicate_succ] using congrArg (a :: ·) h)
      · exact .inr ⟨z,tl,hz,by simpa [lead,List.replicate_succ] using congrArg (a :: ·) h⟩
    · exact .inr ⟨x,xs,hx,by simp [lead,hx,zeroes]⟩

private theorem lead_prefix (A : α) (xs : List α) : zeroes A (lead A xs) <+: xs := by
  rcases split_lead A xs with h|⟨z,t,_,h⟩
  · exact ⟨[],by simp [← h]⟩
  · exact ⟨z::t,h.symm⟩

private def credit (a : Nat) : Nat := if a = 0 then 1 else 0

/-- A potential on consecutive zero runs. If a defect of cost one has
a length-r run on its right, the forbidden factor consumes the
one unit of boundary credit from an empty run on its left. -/
theorem run_charging (A : α) (C : α → Nat) (zero : ∀ z, C z = 0 ↔ z = A)
    (r : Nat) (hr : 2 ≤ r) (xs : List α)
    (cap : ¬zeroes A (r+1) <:+: xs)
    (forbid : ∀ z, C z = 1 → ¬ (A :: z :: zeroes A r) <:+: xs) :
    xs.length ≤ r * (xs.map C).sum + r := by
  have aux (w : List α) (hw : w <:+: xs) :
      w.length ≤ r * (w.map C).sum + (lead A w + credit (lead A w)) := by
    induction len : w.length using Nat.strongRecOn generalizing w with
    | ind n ih =>
      rcases split_lead A w with hall|⟨z,tl,hz,h⟩
      · have e := congrArg List.length hall
        simp only [List.length_replicate] at e
        omega
      · let a := lead A w
        let b := lead A tl
        have hw' : w = zeroes A a ++ z :: tl := h
        have ht : tl <:+: w := ⟨zeroes A a ++ [z],[],by simp [hw',List.append_assoc]⟩
        have hp := lead_prefix A tl
        have hb : b ≤ r := by
          apply Nat.le_of_not_gt
          intro hn
          have pf : zeroes A (r+1) <+: zeroes A b :=
            ⟨zeroes A (b-(r+1)), by simp [Nat.add_sub_of_le (by omega : r+1 ≤ b)]⟩
          exact cap ((pf.trans hp).isInfix.trans (ht.trans hw))
        have avoidRun (hl : C z = 1) (ha : 0 < a) : b < r := by
          apply Nat.lt_of_not_ge
          intro hn
          have e : b = r := by omega
          obtain ⟨u,hu⟩ := hp
          have ha' : zeroes A a = zeroes A (a-1) ++ [A] := by
            rw [←List.replicate_succ']; congr 1; omega
          apply forbid z hl
          apply List.IsInfix.trans _ hw
          refine ⟨zeroes A (a-1),u,?_⟩
          rw [hw',ha',←hu]
          simp [List.append_assoc,← e,b]
        have pay : 1 + b + credit b ≤ r * C z + credit a := by
          by_cases unit : C z = 1
          · have hc := avoidRun unit
            simp only [unit,Nat.mul_one]
            unfold credit
            split <;> split <;> omega
          · have pos : C z ≠ 0 := fun h => hz ((zero z).mp h)
            have h2 : 2 ≤ C z := by omega
            have hscale := Nat.mul_le_mul_left r h2
            simp only [Nat.mul_succ,Nat.mul_zero,Nat.zero_add] at hscale
            unfold credit
            split <;> split <;> omega
        have len : tl.length < n := by
          have he := congrArg List.length hw'
          simp only [List.length_append,List.length_replicate,List.length_cons] at he; omega
        have i := ih _ len tl (ht.trans hw) rfl
        have c : (w.map C).sum = C z + (tl.map C).sum := by
          rw [hw']; simp [List.sum_append,zeroes,(zero A).mpr rfl]
        have he := congrArg List.length hw'
        simp only [List.length_append,List.length_cons,List.length_replicate] at he
        rw [c,Nat.mul_add]
        change tl.length ≤ _ + (b + credit b) at i
        change n ≤ _ + (a + credit a)
        omega
  have hc : lead A xs ≤ r := by
    apply Nat.le_of_not_gt
    intro hn
    have pf : zeroes A (r+1) <+: zeroes A (lead A xs) :=
      ⟨zeroes A (lead A xs-(r+1)),by simp [Nat.add_sub_of_le (by omega : r+1 ≤ lead A xs)]⟩
    exact cap ((pf.trans (lead_prefix A xs)).isInfix)
  have hh := aux xs (show xs <:+: xs from ⟨[],[],by simp⟩)
  unfold credit at hh
  split at hh <;> omega
#print axioms run_charging
end RunBound.Abstract
