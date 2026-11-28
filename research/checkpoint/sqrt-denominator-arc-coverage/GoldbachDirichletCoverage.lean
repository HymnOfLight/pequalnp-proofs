import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
namespace Goldbach.SqrtArcCoverage
-- The following lemma is taken verbatim from the project's
-- Conjectures.Goldbach.DeepThreeQuartersFromFareyError_aux.dirichlet_nat.
theorem dirichlet_nat (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ (q : ℝ) ≤ Real.sqrt n ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Real.sqrt n) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hnR
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := lt_of_lt_of_le zero_lt_one hsqrt1
  have hBpos : (0 : ℕ) < ⌊Real.sqrt (n : ℝ)⌋₊ := Nat.floor_pos.mpr hsqrt1
  obtain ⟨s, hs, hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hBpos
  have hdpos : (0 : ℝ) < (s.den : ℝ) := Nat.cast_pos.mpr s.pos
  have hBposR : (0 : ℝ) < (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) := Nat.cast_pos.mpr hBpos
  rw [Rat.cast_def, mul_comm (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * (s.den : ℝ) - (s.num : ℝ)| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl, hu⟩ := abs_lt.mp hclose
  have ht0' : 0 ≤ t * (s.den : ℝ) := mul_nonneg ht0 hdpos.le
  have ht1' : t * (s.den : ℝ) ≤ (s.den : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right ht1 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < (s.num : ℝ) by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by
    exact_mod_cast (show (s.num : ℝ) < (s.den : ℝ) + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
      _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by
    exact_mod_cast (show (s.num.natAbs : ℤ) ≤ (s.den : ℤ) by omega)
  have hdenle : (s.den : ℝ) ≤ Real.sqrt (n : ℝ) := by
    calc (s.den : ℝ) ≤ (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) := by exact_mod_cast hd
      _ ≤ Real.sqrt (n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrtlt : Real.sqrt (n : ℝ) < (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) + 1 :=
    Nat.lt_floor_add_one _
  rw [← hcast'] at hs
  refine ⟨s.num.natAbs, s.den, s.pos, hle, s.reduced, hdenle, ?_⟩
  calc |t - (s.num.natAbs : ℝ) / (s.den : ℝ)|
      ≤ 1 / ((s.den : ℝ) * ((((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) + 1)) := hs
    _ ≤ 1 / ((s.den : ℝ) * Real.sqrt (n : ℝ)) := by
        apply one_div_le_one_div_of_le (mul_pos hdpos hsqrtpos)
        exact mul_le_mul_of_nonneg_left hsqrtlt.le hdpos.le

/-- A sqrt-denominator arc system covers the interval once its numerator is at least sqrt(n). -/
theorem all_points (n H : ℕ) (hn : 1 ≤ n) (hH : Real.sqrt (n : ℝ) ≤ H)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n) := by
  obtain ⟨a, q, hq, ha, hac, hqs, happrox⟩ := dirichlet_nat t ht.1 ht.2 n hn
  refine ⟨q, a, hq, Nat.le_floor (by rw [← Real.sqrt_eq_rpow]; exact hqs), ha, hac, happrox.trans ?_⟩
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs := Real.sqrt_pos.2 hn'
  apply (div_le_div_iff₀ (mul_pos hq' hs) (mul_pos hq' hn')).2
  have hnH : (n : ℝ) ≤ H * Real.sqrt n := by
    nlinarith [Real.sq_sqrt hn'.le, mul_le_mul_of_nonneg_right hH hs.le]
  nlinarith [mul_le_mul_of_nonneg_left hnH hq'.le]
theorem covers_frozen_width (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / q| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ * (Nat.log 2 (n+2))^2 : ℕ) : ℝ) / ((q : ℝ) * n) := by
  apply all_points n _ hn _ t ht
  rw [← Real.sqrt_eq_rpow]
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hf : 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ := Nat.le_floor (by simpa using hs)
  have hl : 1 ≤ (Nat.log 2 (n+2))^2 := Nat.one_le_pow _ _ (Nat.log_pos (by decide) (by omega))
  have hb : ⌊Real.sqrt (n : ℝ)⌋₊ + 1 ≤ 256 * ⌊Real.sqrt (n : ℝ)⌋₊ * (Nat.log 2 (n+2))^2 := by
    calc
      _ ≤ 256 * ⌊Real.sqrt (n : ℝ)⌋₊ := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ hl
  have hc : (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) + 1 ≤ _ := (by exact_mod_cast hb : (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) + 1 ≤ ((256 * ⌊Real.sqrt (n : ℝ)⌋₊ * (Nat.log 2 (n+2))^2 : ℕ) : ℝ))
  exact (Nat.lt_floor_add_one _).le.trans hc
#print axioms covers_frozen_width
end Goldbach.SqrtArcCoverage
