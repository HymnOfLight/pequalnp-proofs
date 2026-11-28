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

theorem Conjectures.Cuts.Task2648c5451231c368b3124e92 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : Finset ℕ) (x3 : ℕ → ℂ) (x4 : ℕ), ∫ (x5 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x6 ∈ x2, ((1 : ℂ) + x3 x6 * x1 (1 : ℕ) x5)) * Star.star (x1 x4 x5) = ∑ x5 ∈ Finset.powersetCard x4 x2, ∏ x6 ∈ x5, x3 x6) := by
  classical
  dsimp only
  intro A c j
  change (∫ t in (0 : ℝ)..1, (∏ i ∈ A, (1 + c i * phase 1 t)) * star (phase j t)) = _
  have pow_phase (k : ℕ) (t : ℝ) : phase 1 t ^ k = phase k t := by
    unfold phase
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have expand (t : ℝ) : (∏ i ∈ A, (1 + c i * phase 1 t)) * star (phase j t) =
      ∑ s ∈ A.powerset, (∏ i ∈ s, c i) * (phase s.card t * star (phase j t)) := by
    rw [Finset.prod_one_add, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.prod_mul_distrib, Finset.prod_const, pow_phase, mul_assoc]
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun s _ => by
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, phase_orth]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  congr 1
  ext s
  simp [Finset.mem_powersetCard]
