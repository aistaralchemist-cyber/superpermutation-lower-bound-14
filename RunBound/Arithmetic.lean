import pairs.GreedyLocal
import RunBound.Charging

namespace HaruhiLower.RunBound
open ChainReturns
abbrev E := Chunk.pair 35 3
abbrev X := Chunk.pair 34 3
abbrev Y := Chunk.pair 35 2

def code (c : Chunk) : FourteenCuts.Tile :=
  if c = E then .efficient else if c = X then .shortFirst
  else if c = Y then .shortSecond else .other

private def decode : FourteenCuts.Tile → Chunk
  | .efficient => E | .shortFirst => X | .shortSecond => Y | .other => .single 0

private theorem decode_of_ne (c : Chunk) (h : code c ≠ .other) : decode (code c) = c := by
  unfold code at *
  split_ifs at * <;> simp_all [decode]

private theorem cost_le (c : Chunk) (h : OneInterior 4 c) :
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

private theorem lift_infix {cs : List Chunk} {ts : List FourteenCuts.Tile}
    (hi : ts <:+: cs.map code) (hgood : .other ∉ ts) : ts.map decode <:+: cs := by
  obtain ⟨left,right,he⟩ := hi
  obtain ⟨pre',post,e,e',_⟩ := List.map_eq_append_iff.mp he.symm
  obtain ⟨pre,mid,ee,_,hm⟩ := List.map_eq_append_iff.mp e'
  have h : mid.map (decode ∘ code) = mid.map id := List.map_congr_left (fun c hc =>
    decode_of_ne c (fun bad => hgood (hm ▸ (bad ▸ List.mem_map_of_mem hc))))
  refine ⟨pre,post,?_⟩
  rw [←hm,List.map_map,h,List.map_id,←ee,←e]

theorem arithmetic (pre : List Chunk) (tail : List Chunk)
    (ht : tail.length ≤ 2) (chunks : List Chunk) (hchunks : chunks = pre ++ tail)
    (hvalid : ∀ c ∈ pre, OneInterior 4 c)
    (h15 : ¬ List.replicate 15 E <:+: pre)
    (hshort : ∀ z ∈ [X,Y], ¬ (List.replicate 1 E ++ z :: List.replicate 14 E) <:+: pre)
    (hpay : -16 ≤ (tail.map (fun c => c.tile.loss 19)).sum) :
    2 * (tileLength (chunks.map Chunk.tile)) ≤ (1011/14 : ℚ) +
      (531/14 : ℚ) * ((tileChainCount (chunks.map Chunk.tile) : ℚ) - 1) := by
  have cap : ¬ FourteenCuts.zeroes 15 <:+: pre.map code := fun hz =>
    h15 (by simpa [decode] using lift_infix hz (by simp [FourteenCuts.zeroes]))
  have guard : ∀ z, FourteenCuts.loss z = 1 →
      ¬ (FourteenCuts.Tile.efficient :: z :: FourteenCuts.zeroes 14) <:+: pre.map code := by
    intro z hz hf
    cases z with
    | efficient | other => contradiction
    | shortFirst => exact hshort X (by simp) (by simpa [decode] using lift_infix hf (by simp [FourteenCuts.zeroes]))
    | shortSecond => exact hshort Y (by simp) (by simpa [decode] using lift_infix hf (by simp [FourteenCuts.zeroes]))
  have bound := FourteenCuts.RunBound.run_charging 14 (by decide) (pre.map code) cap guard
  simp only [List.length_map] at bound
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
  have bq : (pre.length : ℚ) ≤ 14 * (FourteenCuts.losses (pre.map code) : ℚ) + 14 := by exact_mod_cast bound
  have cq : (tileChainCount (chunks.map Chunk.tile) : ℚ) ≤ 2 * (chunks.length : ℚ) := by exact_mod_cast count
  have lq : (chunks.length : ℚ) = pre.length + tail.length := by exact_mod_cast len
  have tq : (tail.length : ℚ) ≤ 2 := by exact_mod_cast ht
  change (List.map (fun c : Chunk => c.tile.loss 19) chunks).sum = _ at total
  linarith

end HaruhiLower.RunBound
