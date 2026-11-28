import Mathlib

private noncomputable def phase (k : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * t)

private theorem phase_orth (k j : ℕ) :
    (∫ t in (0 : ℝ)..1, phase k t * star (phase j t)) = if k = j then 1 else 0 := by
  let a : ℂ := ((k : ℂ) - j) * (2 * (Real.pi : ℂ) * Complex.I)
  have h (t : ℝ) : phase k t * star (phase j t) = Complex.exp (a * t) := by
    unfold phase
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
    simp [a, map_mul, htwo]
    <;> ring
  simp_rw [h]
  by_cases hk : k = j
  · subst k
    simp [a]
  · have ha : a ≠ 0 := by
      dsimp [a]
      exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hk))
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : Complex.exp a = 1 := by
      simpa [a] using Complex.exp_int_mul_two_pi_mul_I ((k : ℤ) - j)
    rw [integral_exp_mul_complex ha]
    simp [hk, he]

theorem Conjectures.Cuts.Taske7eb86ed8e7dc2b75c3ea402 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : Finset ℕ) (x3 x4 : ℕ) (x5 : Finset ℕ),   have x6 : Finset (Finset ℕ) := Finset.powersetCard x4 x2;   have x7 : Finset ℕ → ℕ := fun (x7 : Finset ℕ) => ∑ x8 ∈ x7, x3 ^ x8;   ↑{x8 ∈ x6 | x7 x8 ∈ x5}.card = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∑ x9 ∈ x6, ∏ x10 ∈ x9, x1 (x3 ^ x10) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re) := by
  classical
  dsimp only
  intro A b j R
  let B := A.powersetCard j
  let v (s : Finset ℕ) := ∑ i ∈ s, b ^ i
  have prod_phase (s : Finset ℕ) (t : ℝ) :
      (∏ i ∈ s, phase (b ^ i) t) = phase (v s) t := by
    unfold phase v
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have expand (t : ℝ) : (∑ s ∈ B, ∏ i ∈ s, phase (b ^ i) t) * star (∑ n ∈ R, phase n t) =
      ∑ s ∈ B, ∑ n ∈ R, phase (v s) t * star (phase n t) := by
    simp_rw [prod_phase]
    rw [star_sum, Finset.sum_mul_sum]
  have hint (s : Finset ℕ) (n : ℕ) :
      IntervalIntegrable (fun t => phase (v s) t * star (phase n t)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop
  have outer (s : Finset ℕ) :
      IntervalIntegrable (fun t => ∑ n ∈ R, phase (v s) t * star (phase n t))
        MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop
  change ((B.filter (fun s => v s ∈ R)).card : ℝ) =
    (∫ t in (0 : ℝ)..1, (∑ s ∈ B, ∏ i ∈ s, phase (b ^ i) t) * star (∑ n ∈ R, phase n t)).re
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun s _ => outer s)]
  simp_rw [intervalIntegral.integral_finsetSum (fun n _ => hint _ n), phase_orth]
  simp
