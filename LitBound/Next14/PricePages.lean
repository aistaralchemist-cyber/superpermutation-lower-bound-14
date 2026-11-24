import LitBound.Next14.PriceRows0
import LitBound.Next14.PriceRows1
import LitBound.Next14.PriceRows2
import LitBound.Next14.PriceRows3
import LitBound.Next14.PriceRows4

namespace HaruhiNextPrice
open FourteenCuts
set_option maxHeartbeats 18000000
set_option maxRecDepth 60000

private theorem verified (s : Nat) (hs : s < 1596) : rowAt s = true := by
  by_cases h0 : s < 800
  · by_cases h1 : s < 416
    · by_cases h2 : s < 224
      · by_cases h3 : s < 128
        · by_cases h4 : s < 64
          · by_cases h5 : s < 32
            · have hfirst : 0 ≤ s := by omega
              have hb := rowGroup00 ⟨s-0,by omega⟩
              have heq : 0+(s-0)=s := by omega
              change rowAt (0 + (s - 0)) = true at hb
              rwa [heq] at hb
            · have hfirst : 32 ≤ s := by omega
              have hb := rowGroup01 ⟨s-32,by omega⟩
              have heq : 32+(s-32)=s := by omega
              change rowAt (32 + (s - 32)) = true at hb
              rwa [heq] at hb
          · by_cases h5 : s < 96
            · have hfirst : 64 ≤ s := by omega
              have hb := rowGroup02 ⟨s-64,by omega⟩
              have heq : 64+(s-64)=s := by omega
              change rowAt (64 + (s - 64)) = true at hb
              rwa [heq] at hb
            · have hfirst : 96 ≤ s := by omega
              have hb := rowGroup03 ⟨s-96,by omega⟩
              have heq : 96+(s-96)=s := by omega
              change rowAt (96 + (s - 96)) = true at hb
              rwa [heq] at hb
        · by_cases h4 : s < 192
          · by_cases h5 : s < 160
            · have hfirst : 128 ≤ s := by omega
              have hb := rowGroup04 ⟨s-128,by omega⟩
              have heq : 128+(s-128)=s := by omega
              change rowAt (128 + (s - 128)) = true at hb
              rwa [heq] at hb
            · have hfirst : 160 ≤ s := by omega
              have hb := rowGroup05 ⟨s-160,by omega⟩
              have heq : 160+(s-160)=s := by omega
              change rowAt (160 + (s - 160)) = true at hb
              rwa [heq] at hb
          · have hfirst : 192 ≤ s := by omega
            have hb := rowGroup06 ⟨s-192,by omega⟩
            have heq : 192+(s-192)=s := by omega
            change rowAt (192 + (s - 192)) = true at hb
            rwa [heq] at hb
      · by_cases h3 : s < 320
        · by_cases h4 : s < 288
          · by_cases h5 : s < 256
            · have hfirst : 224 ≤ s := by omega
              have hb := rowGroup07 ⟨s-224,by omega⟩
              have heq : 224+(s-224)=s := by omega
              change rowAt (224 + (s - 224)) = true at hb
              rwa [heq] at hb
            · have hfirst : 256 ≤ s := by omega
              have hb := rowGroup08 ⟨s-256,by omega⟩
              have heq : 256+(s-256)=s := by omega
              change rowAt (256 + (s - 256)) = true at hb
              rwa [heq] at hb
          · have hfirst : 288 ≤ s := by omega
            have hb := rowGroup09 ⟨s-288,by omega⟩
            have heq : 288+(s-288)=s := by omega
            change rowAt (288 + (s - 288)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 384
          · by_cases h5 : s < 352
            · have hfirst : 320 ≤ s := by omega
              have hb := rowGroup10 ⟨s-320,by omega⟩
              have heq : 320+(s-320)=s := by omega
              change rowAt (320 + (s - 320)) = true at hb
              rwa [heq] at hb
            · have hfirst : 352 ≤ s := by omega
              have hb := rowGroup11 ⟨s-352,by omega⟩
              have heq : 352+(s-352)=s := by omega
              change rowAt (352 + (s - 352)) = true at hb
              rwa [heq] at hb
          · have hfirst : 384 ≤ s := by omega
            have hb := rowGroup12 ⟨s-384,by omega⟩
            have heq : 384+(s-384)=s := by omega
            change rowAt (384 + (s - 384)) = true at hb
            rwa [heq] at hb
    · by_cases h2 : s < 608
      · by_cases h3 : s < 512
        · by_cases h4 : s < 480
          · by_cases h5 : s < 448
            · have hfirst : 416 ≤ s := by omega
              have hb := rowGroup13 ⟨s-416,by omega⟩
              have heq : 416+(s-416)=s := by omega
              change rowAt (416 + (s - 416)) = true at hb
              rwa [heq] at hb
            · have hfirst : 448 ≤ s := by omega
              have hb := rowGroup14 ⟨s-448,by omega⟩
              have heq : 448+(s-448)=s := by omega
              change rowAt (448 + (s - 448)) = true at hb
              rwa [heq] at hb
          · have hfirst : 480 ≤ s := by omega
            have hb := rowGroup15 ⟨s-480,by omega⟩
            have heq : 480+(s-480)=s := by omega
            change rowAt (480 + (s - 480)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 576
          · by_cases h5 : s < 544
            · have hfirst : 512 ≤ s := by omega
              have hb := rowGroup16 ⟨s-512,by omega⟩
              have heq : 512+(s-512)=s := by omega
              change rowAt (512 + (s - 512)) = true at hb
              rwa [heq] at hb
            · have hfirst : 544 ≤ s := by omega
              have hb := rowGroup17 ⟨s-544,by omega⟩
              have heq : 544+(s-544)=s := by omega
              change rowAt (544 + (s - 544)) = true at hb
              rwa [heq] at hb
          · have hfirst : 576 ≤ s := by omega
            have hb := rowGroup18 ⟨s-576,by omega⟩
            have heq : 576+(s-576)=s := by omega
            change rowAt (576 + (s - 576)) = true at hb
            rwa [heq] at hb
      · by_cases h3 : s < 704
        · by_cases h4 : s < 672
          · by_cases h5 : s < 640
            · have hfirst : 608 ≤ s := by omega
              have hb := rowGroup19 ⟨s-608,by omega⟩
              have heq : 608+(s-608)=s := by omega
              change rowAt (608 + (s - 608)) = true at hb
              rwa [heq] at hb
            · have hfirst : 640 ≤ s := by omega
              have hb := rowGroup20 ⟨s-640,by omega⟩
              have heq : 640+(s-640)=s := by omega
              change rowAt (640 + (s - 640)) = true at hb
              rwa [heq] at hb
          · have hfirst : 672 ≤ s := by omega
            have hb := rowGroup21 ⟨s-672,by omega⟩
            have heq : 672+(s-672)=s := by omega
            change rowAt (672 + (s - 672)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 768
          · by_cases h5 : s < 736
            · have hfirst : 704 ≤ s := by omega
              have hb := rowGroup22 ⟨s-704,by omega⟩
              have heq : 704+(s-704)=s := by omega
              change rowAt (704 + (s - 704)) = true at hb
              rwa [heq] at hb
            · have hfirst : 736 ≤ s := by omega
              have hb := rowGroup23 ⟨s-736,by omega⟩
              have heq : 736+(s-736)=s := by omega
              change rowAt (736 + (s - 736)) = true at hb
              rwa [heq] at hb
          · have hfirst : 768 ≤ s := by omega
            have hb := rowGroup24 ⟨s-768,by omega⟩
            have heq : 768+(s-768)=s := by omega
            change rowAt (768 + (s - 768)) = true at hb
            rwa [heq] at hb
  · by_cases h1 : s < 1216
    · by_cases h2 : s < 1024
      · by_cases h3 : s < 928
        · by_cases h4 : s < 864
          · by_cases h5 : s < 832
            · have hfirst : 800 ≤ s := by omega
              have hb := rowGroup25 ⟨s-800,by omega⟩
              have heq : 800+(s-800)=s := by omega
              change rowAt (800 + (s - 800)) = true at hb
              rwa [heq] at hb
            · have hfirst : 832 ≤ s := by omega
              have hb := rowGroup26 ⟨s-832,by omega⟩
              have heq : 832+(s-832)=s := by omega
              change rowAt (832 + (s - 832)) = true at hb
              rwa [heq] at hb
          · by_cases h5 : s < 896
            · have hfirst : 864 ≤ s := by omega
              have hb := rowGroup27 ⟨s-864,by omega⟩
              have heq : 864+(s-864)=s := by omega
              change rowAt (864 + (s - 864)) = true at hb
              rwa [heq] at hb
            · have hfirst : 896 ≤ s := by omega
              have hb := rowGroup28 ⟨s-896,by omega⟩
              have heq : 896+(s-896)=s := by omega
              change rowAt (896 + (s - 896)) = true at hb
              rwa [heq] at hb
        · by_cases h4 : s < 992
          · by_cases h5 : s < 960
            · have hfirst : 928 ≤ s := by omega
              have hb := rowGroup29 ⟨s-928,by omega⟩
              have heq : 928+(s-928)=s := by omega
              change rowAt (928 + (s - 928)) = true at hb
              rwa [heq] at hb
            · have hfirst : 960 ≤ s := by omega
              have hb := rowGroup30 ⟨s-960,by omega⟩
              have heq : 960+(s-960)=s := by omega
              change rowAt (960 + (s - 960)) = true at hb
              rwa [heq] at hb
          · have hfirst : 992 ≤ s := by omega
            have hb := rowGroup31 ⟨s-992,by omega⟩
            have heq : 992+(s-992)=s := by omega
            change rowAt (992 + (s - 992)) = true at hb
            rwa [heq] at hb
      · by_cases h3 : s < 1120
        · by_cases h4 : s < 1088
          · by_cases h5 : s < 1056
            · have hfirst : 1024 ≤ s := by omega
              have hb := rowGroup32 ⟨s-1024,by omega⟩
              have heq : 1024+(s-1024)=s := by omega
              change rowAt (1024 + (s - 1024)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1056 ≤ s := by omega
              have hb := rowGroup33 ⟨s-1056,by omega⟩
              have heq : 1056+(s-1056)=s := by omega
              change rowAt (1056 + (s - 1056)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1088 ≤ s := by omega
            have hb := rowGroup34 ⟨s-1088,by omega⟩
            have heq : 1088+(s-1088)=s := by omega
            change rowAt (1088 + (s - 1088)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 1184
          · by_cases h5 : s < 1152
            · have hfirst : 1120 ≤ s := by omega
              have hb := rowGroup35 ⟨s-1120,by omega⟩
              have heq : 1120+(s-1120)=s := by omega
              change rowAt (1120 + (s - 1120)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1152 ≤ s := by omega
              have hb := rowGroup36 ⟨s-1152,by omega⟩
              have heq : 1152+(s-1152)=s := by omega
              change rowAt (1152 + (s - 1152)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1184 ≤ s := by omega
            have hb := rowGroup37 ⟨s-1184,by omega⟩
            have heq : 1184+(s-1184)=s := by omega
            change rowAt (1184 + (s - 1184)) = true at hb
            rwa [heq] at hb
    · by_cases h2 : s < 1408
      · by_cases h3 : s < 1312
        · by_cases h4 : s < 1280
          · by_cases h5 : s < 1248
            · have hfirst : 1216 ≤ s := by omega
              have hb := rowGroup38 ⟨s-1216,by omega⟩
              have heq : 1216+(s-1216)=s := by omega
              change rowAt (1216 + (s - 1216)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1248 ≤ s := by omega
              have hb := rowGroup39 ⟨s-1248,by omega⟩
              have heq : 1248+(s-1248)=s := by omega
              change rowAt (1248 + (s - 1248)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1280 ≤ s := by omega
            have hb := rowGroup40 ⟨s-1280,by omega⟩
            have heq : 1280+(s-1280)=s := by omega
            change rowAt (1280 + (s - 1280)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 1376
          · by_cases h5 : s < 1344
            · have hfirst : 1312 ≤ s := by omega
              have hb := rowGroup41 ⟨s-1312,by omega⟩
              have heq : 1312+(s-1312)=s := by omega
              change rowAt (1312 + (s - 1312)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1344 ≤ s := by omega
              have hb := rowGroup42 ⟨s-1344,by omega⟩
              have heq : 1344+(s-1344)=s := by omega
              change rowAt (1344 + (s - 1344)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1376 ≤ s := by omega
            have hb := rowGroup43 ⟨s-1376,by omega⟩
            have heq : 1376+(s-1376)=s := by omega
            change rowAt (1376 + (s - 1376)) = true at hb
            rwa [heq] at hb
      · by_cases h3 : s < 1504
        · by_cases h4 : s < 1472
          · by_cases h5 : s < 1440
            · have hfirst : 1408 ≤ s := by omega
              have hb := rowGroup44 ⟨s-1408,by omega⟩
              have heq : 1408+(s-1408)=s := by omega
              change rowAt (1408 + (s - 1408)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1440 ≤ s := by omega
              have hb := rowGroup45 ⟨s-1440,by omega⟩
              have heq : 1440+(s-1440)=s := by omega
              change rowAt (1440 + (s - 1440)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1472 ≤ s := by omega
            have hb := rowGroup46 ⟨s-1472,by omega⟩
            have heq : 1472+(s-1472)=s := by omega
            change rowAt (1472 + (s - 1472)) = true at hb
            rwa [heq] at hb
        · by_cases h4 : s < 1568
          · by_cases h5 : s < 1536
            · have hfirst : 1504 ≤ s := by omega
              have hb := rowGroup47 ⟨s-1504,by omega⟩
              have heq : 1504+(s-1504)=s := by omega
              change rowAt (1504 + (s - 1504)) = true at hb
              rwa [heq] at hb
            · have hfirst : 1536 ≤ s := by omega
              have hb := rowGroup48 ⟨s-1536,by omega⟩
              have heq : 1536+(s-1536)=s := by omega
              change rowAt (1536 + (s - 1536)) = true at hb
              rwa [heq] at hb
          · have hfirst : 1568 ≤ s := by omega
            have hb := rowGroup49 ⟨s-1568,by omega⟩
            have heq : 1568+(s-1568)=s := by omega
            change rowAt (1568 + (s - 1568)) = true at hb
            rwa [heq] at hb
private theorem table_ok (s : State) (z : Tile) : ok s z = true := by
  have h := verified s.val s.isLt
  simp only [rowAt,dif_pos s.isLt] at h
  cases z <;> simp_all [Bool.and_eq_true]
private theorem step {xs : List Tile} (safe : ∀ w ∈ forbidden, ¬ w <:+: xs) :
    ∃ s : State, label s <:+ xs ∧ 8 * xs.length + pot 0 ≤ 107 * losses xs + pot s := by
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
    by_cases ht : next s z < 1596
    · let t : State := ⟨next s z,ht⟩
      have both : (label t).isSuffixOf (label s ++ [z]) = true ∧
          8 + pot s ≤ 107 * loss z + pot t := by simpa [ok,ht,t] using ok'
      refine ⟨t,(List.isSuffixOf_iff_suffix.mp both.1).trans endpoint,?_⟩
      have hl : losses (pre ++ [z]) = losses pre + loss z := by simp [losses,List.sum_append]
      simp only [List.length_append,List.length_singleton,hl] at *
      omega
    · have hit : forbidden.any (fun w => w.isSuffixOf (label s ++ [z])) = true := by
        simpa [ok,ht] using ok'
      obtain ⟨w,hw,hw'⟩ := List.any_eq_true.mp hit
      exact False.elim (safe w hw ((List.isSuffixOf_iff_suffix.mp hw').trans endpoint).isInfix)

/-- A transition potential proves the 8:107 ratio with additive allowance 132. -/
theorem price (xs : List Tile) (safe : ∀ w ∈ forbidden, ¬ w <:+: xs) :
    8 * xs.length ≤ 107 * losses xs + 132 := by
  obtain ⟨s,_,h⟩ := step safe
  have cap : ∀ i : State, pot i ≤ 132 := by decide
  have init : pot 0 = 0 := by decide
  rw [init] at h
  have := cap s
  omega

#print axioms price
end HaruhiNextPrice
