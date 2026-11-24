import TileLoss
import Mathlib.Data.List.Induction

set_option maxRecDepth 60000

/-! A weighted suffix automaton. Each row describes a proper prefix of a
forbidden word. A transition either certifies a forbidden suffix, or advances
to a suffix and satisfies a potential inequality. All entries are rechecked
by Lean's kernel. -/
namespace LiteratureStrong
open FourteenCuts
abbrev A := Tile.efficient
abbrev X := Tile.shortFirst
abbrev Y := Tile.shortSecond
abbrev rA (n : Nat) := List.replicate n A

def middle := [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y]

def forbidden : List (List Tile) :=
  [rA 15, [A,X] ++ rA 14, [A,Y] ++ rA 14,
   [A,X] ++ rA 13 ++ [X,A], [X] ++ rA 13 ++ [Y],
   [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ rA 6, rA 12 ++ middle ++ rA 10]

private abbrev State := Fin 157
private def labels : Array (List Tile) := #[
  [],
  [A],
  [X],
  [Y],
  rA 2,
  [A] ++ [X],
  [A] ++ [Y],
  [X] ++ [A],
  [Y] ++ [A],
  rA 3,
  [A] ++ [X] ++ [A],
  [A] ++ [Y] ++ [A],
  [X] ++ rA 2,
  [Y] ++ rA 2,
  rA 4,
  [A] ++ [X] ++ rA 2,
  [A] ++ [Y] ++ rA 2,
  [X] ++ rA 3,
  [Y] ++ rA 3,
  rA 5,
  [A] ++ [X] ++ rA 3,
  [A] ++ [Y] ++ rA 3,
  [X] ++ rA 4,
  [Y] ++ rA 4,
  rA 6,
  [A] ++ [X] ++ rA 4,
  [A] ++ [Y] ++ rA 4,
  [X] ++ rA 5,
  [Y] ++ rA 5,
  rA 7,
  [A] ++ [X] ++ rA 5,
  [A] ++ [Y] ++ rA 5,
  [X] ++ rA 6,
  [Y] ++ rA 6,
  rA 8,
  [A] ++ [X] ++ rA 6,
  [A] ++ [Y] ++ rA 6,
  [X] ++ rA 7,
  [Y] ++ rA 7,
  rA 9,
  [A] ++ [X] ++ rA 7,
  [A] ++ [Y] ++ rA 7,
  [X] ++ rA 8,
  [Y] ++ rA 8,
  rA 10,
  [A] ++ [X] ++ rA 8,
  [A] ++ [Y] ++ rA 8,
  [X] ++ rA 9,
  [Y] ++ rA 9,
  rA 11,
  [A] ++ [X] ++ rA 9,
  [A] ++ [Y] ++ rA 9,
  [X] ++ rA 10,
  [Y] ++ rA 10,
  rA 12,
  [A] ++ [X] ++ rA 10,
  [A] ++ [Y] ++ rA 10,
  [X] ++ rA 11,
  [Y] ++ rA 11,
  rA 13,
  rA 12 ++ [Y],
  [A] ++ [X] ++ rA 11,
  [A] ++ [Y] ++ rA 11,
  [X] ++ rA 12,
  [Y] ++ rA 12,
  rA 14,
  rA 12 ++ [Y] ++ [A],
  [A] ++ [X] ++ rA 12,
  [A] ++ [Y] ++ rA 12,
  [X] ++ rA 13,
  [Y] ++ rA 13,
  rA 12 ++ [Y] ++ rA 2,
  [A] ++ [X] ++ rA 13,
  [A] ++ [Y] ++ rA 13,
  [Y] ++ rA 13 ++ [Y],
  rA 12 ++ [Y] ++ rA 3,
  [A] ++ [X] ++ rA 13 ++ [X],
  [Y] ++ rA 13 ++ [Y] ++ [A],
  rA 12 ++ [Y] ++ rA 4,
  [Y] ++ rA 13 ++ [Y] ++ rA 2,
  rA 12 ++ [Y] ++ rA 5,
  [Y] ++ rA 13 ++ [Y] ++ rA 3,
  rA 12 ++ [Y] ++ rA 6,
  [Y] ++ rA 13 ++ [Y] ++ rA 4,
  rA 12 ++ [Y] ++ rA 7,
  [Y] ++ rA 13 ++ [Y] ++ rA 5,
  rA 12 ++ [Y] ++ rA 8,
  [Y] ++ rA 13 ++ [Y] ++ rA 6,
  rA 12 ++ [Y] ++ rA 9,
  [Y] ++ rA 13 ++ [Y] ++ rA 7,
  rA 12 ++ [Y] ++ rA 10,
  [Y] ++ rA 13 ++ [Y] ++ rA 8,
  rA 12 ++ [Y] ++ rA 11,
  [Y] ++ rA 13 ++ [Y] ++ rA 9,
  rA 12 ++ [Y] ++ rA 12,
  [Y] ++ rA 13 ++ [Y] ++ rA 10,
  rA 12 ++ [Y] ++ rA 13,
  [Y] ++ rA 13 ++ [Y] ++ rA 11,
  rA 12 ++ [Y] ++ rA 13 ++ [Y],
  [Y] ++ rA 13 ++ [Y] ++ rA 12,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ [A],
  [Y] ++ rA 13 ++ [Y] ++ rA 13,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 2,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 3,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ [A],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 4,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ rA 2,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 5,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ rA 3,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 6,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ rA 4,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 7,
  [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [Y] ++ rA 5,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 8,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 9,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 10,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 11,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 12,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ [A],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 2,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 3,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 4,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 5,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 6,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 7,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 8,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 9,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 10,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 11,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ [A],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 2,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 3,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 4,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 5,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 6,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 7,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 8,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 9,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 10,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 11,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 12,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ [A],
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 2,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 3,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 4,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 5,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 6,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 7,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 8,
  rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 13 ++ [X] ++ rA 12 ++ [Y] ++ rA 13 ++ [Y] ++ rA 9]

private def table : Array (Array Nat) := #[
  #[1, 2, 3, 0],
  #[4, 5, 6, 0],
  #[7, 2, 3, 0],
  #[8, 2, 3, 0],
  #[9, 5, 6, 0],
  #[10, 2, 3, 0],
  #[11, 2, 3, 0],
  #[12, 5, 6, 0],
  #[13, 5, 6, 0],
  #[14, 5, 6, 0],
  #[15, 5, 6, 0],
  #[16, 5, 6, 0],
  #[17, 5, 6, 0],
  #[18, 5, 6, 0],
  #[19, 5, 6, 0],
  #[20, 5, 6, 0],
  #[21, 5, 6, 0],
  #[22, 5, 6, 0],
  #[23, 5, 6, 0],
  #[24, 5, 6, 0],
  #[25, 5, 6, 0],
  #[26, 5, 6, 0],
  #[27, 5, 6, 0],
  #[28, 5, 6, 0],
  #[29, 5, 6, 0],
  #[30, 5, 6, 0],
  #[31, 5, 6, 0],
  #[32, 5, 6, 0],
  #[33, 5, 6, 0],
  #[34, 5, 6, 0],
  #[35, 5, 6, 0],
  #[36, 5, 6, 0],
  #[37, 5, 6, 0],
  #[38, 5, 6, 0],
  #[39, 5, 6, 0],
  #[40, 5, 6, 0],
  #[41, 5, 6, 0],
  #[42, 5, 6, 0],
  #[43, 5, 6, 0],
  #[44, 5, 6, 0],
  #[45, 5, 6, 0],
  #[46, 5, 6, 0],
  #[47, 5, 6, 0],
  #[48, 5, 6, 0],
  #[49, 5, 6, 0],
  #[50, 5, 6, 0],
  #[51, 5, 6, 0],
  #[52, 5, 6, 0],
  #[53, 5, 6, 0],
  #[54, 5, 6, 0],
  #[55, 5, 6, 0],
  #[56, 5, 6, 0],
  #[57, 5, 6, 0],
  #[58, 5, 6, 0],
  #[59, 5, 60, 0],
  #[61, 5, 6, 0],
  #[62, 5, 6, 0],
  #[63, 5, 6, 0],
  #[64, 5, 6, 0],
  #[65, 5, 60, 0],
  #[66, 2, 3, 0],
  #[67, 5, 6, 0],
  #[68, 5, 6, 0],
  #[69, 5, 60, 0],
  #[70, 5, 60, 0],
  #[157, 5, 60, 0],
  #[71, 5, 6, 0],
  #[72, 5, 60, 0],
  #[73, 5, 60, 0],
  #[65, 5, 157, 0],
  #[65, 5, 74, 0],
  #[75, 5, 6, 0],
  #[157, 76, 157, 0],
  #[157, 5, 74, 0],
  #[77, 2, 3, 0],
  #[78, 5, 6, 0],
  #[157, 2, 3, 0],
  #[79, 5, 6, 0],
  #[80, 5, 6, 0],
  #[81, 5, 6, 0],
  #[82, 5, 6, 0],
  #[83, 5, 6, 0],
  #[84, 5, 6, 0],
  #[85, 5, 6, 0],
  #[86, 5, 6, 0],
  #[87, 5, 6, 0],
  #[88, 5, 6, 0],
  #[89, 5, 6, 0],
  #[90, 5, 6, 0],
  #[91, 5, 6, 0],
  #[92, 5, 6, 0],
  #[93, 5, 6, 0],
  #[94, 5, 6, 0],
  #[95, 5, 6, 0],
  #[96, 5, 60, 0],
  #[97, 5, 6, 0],
  #[157, 5, 98, 0],
  #[99, 5, 6, 0],
  #[100, 2, 3, 0],
  #[101, 5, 60, 0],
  #[102, 5, 6, 0],
  #[157, 5, 103, 0],
  #[104, 5, 6, 0],
  #[105, 2, 3, 0],
  #[106, 5, 6, 0],
  #[107, 5, 6, 0],
  #[108, 5, 6, 0],
  #[109, 5, 6, 0],
  #[110, 5, 6, 0],
  #[111, 5, 6, 0],
  #[112, 5, 6, 0],
  #[113, 5, 6, 0],
  #[114, 5, 6, 0],
  #[157, 5, 6, 0],
  #[115, 5, 6, 0],
  #[116, 5, 6, 0],
  #[117, 5, 6, 0],
  #[118, 5, 6, 0],
  #[119, 5, 60, 0],
  #[157, 120, 103, 0],
  #[121, 2, 3, 0],
  #[122, 5, 6, 0],
  #[123, 5, 6, 0],
  #[124, 5, 6, 0],
  #[125, 5, 6, 0],
  #[126, 5, 6, 0],
  #[127, 5, 6, 0],
  #[128, 5, 6, 0],
  #[129, 5, 6, 0],
  #[130, 5, 6, 0],
  #[131, 5, 6, 0],
  #[132, 5, 6, 0],
  #[72, 5, 133, 0],
  #[134, 2, 3, 0],
  #[135, 5, 6, 0],
  #[136, 5, 6, 0],
  #[137, 5, 6, 0],
  #[138, 5, 6, 0],
  #[139, 5, 6, 0],
  #[140, 5, 6, 0],
  #[141, 5, 6, 0],
  #[142, 5, 6, 0],
  #[143, 5, 6, 0],
  #[144, 5, 6, 0],
  #[145, 5, 6, 0],
  #[146, 5, 60, 0],
  #[157, 5, 147, 0],
  #[148, 2, 3, 0],
  #[149, 5, 6, 0],
  #[150, 5, 6, 0],
  #[151, 5, 6, 0],
  #[152, 5, 6, 0],
  #[153, 5, 6, 0],
  #[154, 5, 6, 0],
  #[155, 5, 6, 0],
  #[156, 5, 6, 0],
  #[157, 5, 6, 0]]

private def potentials : Array Nat := #[
  50, 55, 0, 0, 60, 60, 53, 5, 5, 65, 65, 58,
  10, 10, 70, 70, 63, 15, 15, 75, 75, 68, 20, 20,
  80, 80, 73, 25, 25, 85, 85, 78, 30, 30, 90, 90,
  83, 35, 35, 95, 95, 88, 40, 40, 100, 100, 93, 45,
  45, 105, 105, 98, 50, 50, 110, 110, 103, 55, 55, 115,
  57, 115, 108, 60, 60, 120, 62, 120, 113, 65, 65, 67,
  126, 118, 55, 72, 63, 60, 77, 65, 82, 70, 87, 75,
  92, 80, 97, 85, 102, 90, 107, 95, 112, 100, 117, 105,
  122, 110, 59, 115, 64, 120, 69, 61, 74, 66, 79, 71,
  84, 76, 89, 81, 94, 86, 99, 104, 109, 114, 119, 124,
  61, 66, 71, 76, 81, 86, 91, 96, 101, 106, 111, 116,
  121, 58, 63, 68, 73, 78, 83, 88, 93, 98, 103, 108,
  113, 118, 123, 60, 65, 70, 75, 80, 85, 90, 95, 100,
  105]

private def label (s : State) := labels[s.val]!
private def pot (s : State) := potentials[s.val]!
private def col : Tile → Nat
  | .efficient => 0 | .shortFirst => 1 | .shortSecond => 2 | .other => 3
private def next (s : State) (z : Tile) := table[s.val]![col z]!

private def ok (s : State) (z : Tile) : Bool :=
  if h : next s z < 157 then
    let t : State := ⟨next s z,h⟩
    (label t).isSuffixOf (label s ++ [z]) && decide (5 + pot s ≤ 68 * loss z + pot t)
  else forbidden.any (fun w => w.isSuffixOf (label s ++ [z]))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 15000000 in
private theorem table_ok (s : State) (z : Tile) : ok s z = true := by
  have all : ∀ i : State, ok i A && ok i X && ok i Y && ok i .other = true := by decide
  have h := all s
  cases z <;> simp_all [Bool.and_eq_true]

private theorem step {xs : List Tile} (safe : ∀ w ∈ forbidden, ¬ w <:+: xs) :
    ∃ s : State, label s <:+ xs ∧ 5 * xs.length + pot 0 ≤ 68 * losses xs + pot s := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨0, by decide, by simp [losses]⟩
  | append_singleton pre z ih =>
    have hp : ∀ w ∈ forbidden, ¬ w <:+: pre := fun w hw hi =>
      safe w hw (hi.trans (List.prefix_append pre [z]).isInfix)
    obtain ⟨s, hs, price⟩ := ih hp
    have endpoint : label s ++ [z] <:+ pre ++ [z] := by
      obtain ⟨a,ha⟩ := hs
      exact ⟨a,by simp [←ha,List.append_assoc]⟩
    have ok' := table_ok s z
    by_cases ht : next s z < 157
    · let t : State := ⟨next s z,ht⟩
      have both : (label t).isSuffixOf (label s ++ [z]) = true ∧
          5 + pot s ≤ 68 * loss z + pot t := by simpa [ok,ht,t] using ok'
      refine ⟨t,(List.isSuffixOf_iff_suffix.mp both.1).trans endpoint,?_⟩
      have hl : losses (pre ++ [z]) = losses pre + loss z := by simp [losses,List.sum_append]
      simp only [List.length_append,List.length_singleton,hl] at *
      omega
    · have hit : forbidden.any (fun w => w.isSuffixOf (label s ++ [z])) = true := by
        simpa [ok,ht] using ok'
      obtain ⟨w,hw,hw'⟩ := List.any_eq_true.mp hit
      exact False.elim (safe w hw ((List.isSuffixOf_iff_suffix.mp hw').trans endpoint).isInfix)

/-- With the seven forbidden local factors, each 68 units of loss pay
for at most 5 symbols per unit of length, with boundary allowance 76. -/
theorem price (xs : List Tile) (safe : ∀ w ∈ forbidden, ¬ w <:+: xs) :
    5 * xs.length ≤ 68 * losses xs + 76 := by
  obtain ⟨s,_,h⟩ := step safe
  have cap : ∀ i : State, pot i ≤ 126 := by decide
  have init : pot 0 = 50 := by decide
  rw [init] at h
  have := cap s
  omega

#print axioms price
end LiteratureStrong
