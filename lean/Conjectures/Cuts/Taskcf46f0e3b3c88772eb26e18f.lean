import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace FiniteLogWindows

private def Hit (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ n < 2*p ∧ 2*p ≤ n+9000

private theorem cover {n p : ℕ} (prime : p.Prime) (large : 2 < p)
    (lo : n < 2*p) (hi : 2*p ≤ n+9000) : Hit n :=
  ⟨p, prime, prime.odd_of_ne_two (by omega), lo, hi⟩

/-- Each interval of 8192 starting values has a common witness 2p. -/
theorem hit (n : ℕ) (hn : n ≤ 1000000) : Hit n := by
  by_cases h61 : n < 499712
  · by_cases h30 : n < 245760
    · by_cases h15 : n < 122880
      · by_cases h7 : n < 57344
        · by_cases h3 : n < 24576
          · by_cases h1 : n < 8192
            · exact cover (p := 4099) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h2 : n < 16384
              · exact cover (p := 8209) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 12289) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h5 : n < 40960
            · by_cases h4 : n < 32768
              · exact cover (p := 16411) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 20483) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h6 : n < 49152
              · exact cover (p := 24593) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 28687) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h11 : n < 90112
          · by_cases h9 : n < 73728
            · by_cases h8 : n < 65536
              · exact cover (p := 32771) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 36871) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h10 : n < 81920
              · exact cover (p := 40961) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 45061) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h13 : n < 106496
            · by_cases h12 : n < 98304
              · exact cover (p := 49157) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 53267) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h14 : n < 114688
              · exact cover (p := 57347) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 61441) (by norm_num1) (by decide) (by omega) (by omega)
      · by_cases h22 : n < 180224
        · by_cases h18 : n < 147456
          · by_cases h16 : n < 131072
            · exact cover (p := 65537) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h17 : n < 139264
              · exact cover (p := 69653) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 73751) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h20 : n < 163840
            · by_cases h19 : n < 155648
              · exact cover (p := 77839) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 81929) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h21 : n < 172032
              · exact cover (p := 86017) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 90121) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h26 : n < 212992
          · by_cases h24 : n < 196608
            · by_cases h23 : n < 188416
              · exact cover (p := 94219) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 98317) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h25 : n < 204800
              · exact cover (p := 102407) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 106501) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h28 : n < 229376
            · by_cases h27 : n < 221184
              · exact cover (p := 110597) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 114689) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h29 : n < 237568
              · exact cover (p := 118787) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 122887) (by norm_num1) (by decide) (by omega) (by omega)
    · by_cases h45 : n < 368640
      · by_cases h37 : n < 303104
        · by_cases h33 : n < 270336
          · by_cases h31 : n < 253952
            · exact cover (p := 126989) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h32 : n < 262144
              · exact cover (p := 131101) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 135173) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h35 : n < 286720
            · by_cases h34 : n < 278528
              · exact cover (p := 139267) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 143387) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h36 : n < 294912
              · exact cover (p := 147457) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 151553) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h41 : n < 335872
          · by_cases h39 : n < 319488
            · by_cases h38 : n < 311296
              · exact cover (p := 155653) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 159763) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h40 : n < 327680
              · exact cover (p := 163841) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 167953) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h43 : n < 352256
            · by_cases h42 : n < 344064
              · exact cover (p := 172049) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 176129) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h44 : n < 360448
              · exact cover (p := 180233) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 184321) (by norm_num1) (by decide) (by omega) (by omega)
      · by_cases h53 : n < 434176
        · by_cases h49 : n < 401408
          · by_cases h47 : n < 385024
            · by_cases h46 : n < 376832
              · exact cover (p := 188417) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 192529) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h48 : n < 393216
              · exact cover (p := 196613) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 200713) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h51 : n < 417792
            · by_cases h50 : n < 409600
              · exact cover (p := 204803) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 208907) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h52 : n < 425984
              · exact cover (p := 212999) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 217111) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h57 : n < 466944
          · by_cases h55 : n < 450560
            · by_cases h54 : n < 442368
              · exact cover (p := 221197) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 225287) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h56 : n < 458752
              · exact cover (p := 229393) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 233477) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h59 : n < 483328
            · by_cases h58 : n < 475136
              · exact cover (p := 237571) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 241667) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h60 : n < 491520
              · exact cover (p := 245771) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 249857) (by norm_num1) (by decide) (by omega) (by omega)
  · by_cases h92 : n < 753664
    · by_cases h76 : n < 622592
      · by_cases h68 : n < 557056
        · by_cases h64 : n < 524288
          · by_cases h62 : n < 507904
            · exact cover (p := 253969) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h63 : n < 516096
              · exact cover (p := 258061) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 262147) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h66 : n < 540672
            · by_cases h65 : n < 532480
              · exact cover (p := 266261) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 270337) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h67 : n < 548864
              · exact cover (p := 274441) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 278543) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h72 : n < 589824
          · by_cases h70 : n < 573440
            · by_cases h69 : n < 565248
              · exact cover (p := 282661) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 286721) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h71 : n < 581632
              · exact cover (p := 290821) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 294919) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h74 : n < 606208
            · by_cases h73 : n < 598016
              · exact cover (p := 299011) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 303119) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h75 : n < 614400
              · exact cover (p := 307201) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 311299) (by norm_num1) (by decide) (by omega) (by omega)
      · by_cases h84 : n < 688128
        · by_cases h80 : n < 655360
          · by_cases h78 : n < 638976
            · by_cases h77 : n < 630784
              · exact cover (p := 315407) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 319489) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h79 : n < 647168
              · exact cover (p := 323591) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 327689) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h82 : n < 671744
            · by_cases h81 : n < 663552
              · exact cover (p := 331777) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 335879) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h83 : n < 679936
              · exact cover (p := 339991) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 344083) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h88 : n < 720896
          · by_cases h86 : n < 704512
            · by_cases h85 : n < 696320
              · exact cover (p := 348163) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 352267) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h87 : n < 712704
              · exact cover (p := 356387) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 360457) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h90 : n < 737280
            · by_cases h89 : n < 729088
              · exact cover (p := 364571) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 368647) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h91 : n < 745472
              · exact cover (p := 372739) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 376837) (by norm_num1) (by decide) (by omega) (by omega)
    · by_cases h107 : n < 876544
      · by_cases h99 : n < 811008
        · by_cases h95 : n < 778240
          · by_cases h93 : n < 761856
            · exact cover (p := 380929) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h94 : n < 770048
              · exact cover (p := 385027) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 389141) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h97 : n < 794624
            · by_cases h96 : n < 786432
              · exact cover (p := 393241) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 397337) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h98 : n < 802816
              · exact cover (p := 401411) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 405521) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h103 : n < 843776
          · by_cases h101 : n < 827392
            · by_cases h100 : n < 819200
              · exact cover (p := 409609) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 413711) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h102 : n < 835584
              · exact cover (p := 417793) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 421891) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h105 : n < 860160
            · by_cases h104 : n < 851968
              · exact cover (p := 425987) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 430081) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h106 : n < 868352
              · exact cover (p := 434179) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 438281) (by norm_num1) (by decide) (by omega) (by omega)
      · by_cases h115 : n < 942080
        · by_cases h111 : n < 909312
          · by_cases h109 : n < 892928
            · by_cases h108 : n < 884736
              · exact cover (p := 442397) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 446473) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h110 : n < 901120
              · exact cover (p := 450563) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 454673) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h113 : n < 925696
            · by_cases h112 : n < 917504
              · exact cover (p := 458789) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 462851) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h114 : n < 933888
              · exact cover (p := 466951) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 471041) (by norm_num1) (by decide) (by omega) (by omega)
        · by_cases h119 : n < 974848
          · by_cases h117 : n < 958464
            · by_cases h116 : n < 950272
              · exact cover (p := 475141) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 479239) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h118 : n < 966656
              · exact cover (p := 483337) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 487427) (by norm_num1) (by decide) (by omega) (by omega)
          · by_cases h121 : n < 991232
            · by_cases h120 : n < 983040
              · exact cover (p := 491527) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 495617) (by norm_num1) (by decide) (by omega) (by omega)
            · by_cases h122 : n < 999424
              · exact cover (p := 499717) (by norm_num1) (by decide) (by omega) (by omega)
              · exact cover (p := 503819) (by norm_num1) (by decide) (by omega) (by omega)

end FiniteLogWindows

theorem Conjectures.Cuts.Taskcf46f0e3b3c88772eb26e18f : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (16384 : ℕ) ≤ x2 → x2 ≤ (1000000 : ℕ) → (1 : ℕ) + ⌊x1 * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤ {x5 ∈ Finset.Ioc x2 ⌊↑x2 + (123 : ℝ) * Real.log ↑x2 ^ (2 : ℕ)⌋₊ | (0 : ℕ) < {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Odd x6 ∧ Nat.Prime (x5 - x6) ∧ Odd (x5 - x6)}.card}.card) := by
  refine ⟨1/400, by norm_num, ?_⟩
  intro n hn hN
  have hlow : Real.log ((2:ℝ)^14) ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hn)
  have hhigh : Real.log (n:ℝ) ≤ Real.log ((2:ℝ)^20) := Real.log_le_log (by positivity) (by exact_mod_cast (show n ≤ 2^20 by omega))
  rw [Real.log_pow] at hlow hhigh
  norm_num1 at hlow hhigh
  have h9 : 9 ≤ Real.log n := by linarith [Real.log_two_gt_d9]
  have h20 : Real.log n < 20 := by linarith [Real.log_two_lt_d9]
  have hsq : Real.log n ^ 2 < 400 := by nlinarith [mul_pos (sub_pos.mpr h20) (show 0 < 20+Real.log n by linarith)]
  rw [Nat.floor_eq_zero.mpr (show (1/400:ℝ)*Real.log n^2 < 1 by linarith)]
  obtain ⟨p,hp,ho,hlo,hhi⟩ := FiniteLogWindows.hit n hN
  simp only [Nat.add_zero, Nat.one_le_iff_ne_zero, ne_eq, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨2*p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, ?_⟩, ?_⟩⟩
  · apply (Nat.le_floor_iff (by positivity)).mpr
    have hr : ((2*p:ℕ):ℝ) ≤ (n:ℝ) + 9000 := by exact_mod_cast hhi
    nlinarith [mul_nonneg (show 0 ≤ Real.log n-9 by linarith) (show 0 ≤ Real.log n+9 by linarith)]
  · refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,ho,?_⟩⟩
    simpa only [show 2*p-p = p by omega] using And.intro hp ho

