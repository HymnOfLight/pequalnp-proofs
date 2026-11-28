import Mathlib
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge

theorem Conjectures.Cuts.Taskd64e8218071fd61cf4ae2c5f : (∀ (x1 : ℕ), (∫ (x2 : ℝ) in (0 : ℝ)..(1 : ℝ), {x3 : ℝ | ∃ (x4 : ℕ) (x5 : ℕ), (1 : ℕ) ≤ x4 ∧ x4 ≤ Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ) ∧ x5 ≤ x4 ∧ x5.Coprime x4 ∧ |x3 - ↑x5 / ↑x4| ≤ ↑(Nat.log (2 : ℕ) (x1 + (2 : ℕ))) ^ (2 : ℕ) / (↑x4 * ↑x1)}.indicator (fun (x3 : ℝ) => (∑ x4 ∈ Finset.range (x1 + (1 : ℕ)), (if Nat.Prime x4 then ↑(Real.log ↑x4) else (0 : ℂ)) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I)) ^ (2 : ℕ) * Complex.exp (↑((2 : ℝ) * Real.pi * -↑x1 * x3) * Complex.I)) x2).re + (∫ (x2 : ℝ) in (0 : ℝ)..(1 : ℝ), {x3 : ℝ | ∃ (x4 : ℕ) (x5 : ℕ), (1 : ℕ) ≤ x4 ∧ x4 ≤ Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ) ∧ x5 ≤ x4 ∧ x5.Coprime x4 ∧ |x3 - ↑x5 / ↑x4| ≤ ↑(Nat.log (2 : ℕ) (x1 + (2 : ℕ))) ^ (2 : ℕ) / (↑x4 * ↑x1)}ᶜ.indicator (fun (x3 : ℝ) => (∑ x4 ∈ Finset.range (x1 + (1 : ℕ)), (if Nat.Prime x4 then ↑(Real.log ↑x4) else (0 : ℂ)) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I)) ^ (2 : ℕ) * Complex.exp (↑((2 : ℝ) * Real.pi * -↑x1 * x3) * Complex.I)) x2).re = ∑ x2 ∈ Finset.range (x1 + (1 : ℕ)), (if Nat.Prime x2 then Real.log ↑x2 else (0 : ℝ)) * if Nat.Prime (x1 - x2) then Real.log (↑x1 - ↑x2) else (0 : ℝ)) := by
  classical
  intro n
  have h := congrArg Complex.re (Conjectures.Goldbach.FourSevenths.Coefficient n)
  dsimp only at h
  have weight (k : ℕ) :
      ((if k.Prime then Real.log k else 0 : ℝ) : ℂ) =
        (if k.Prime then (Real.log k : ℂ) else 0) := by
    split <;> simp_all
  simp only [Complex.add_re, Complex.ofReal_re, weight, Nat.cast_pow, mul_assoc] at h ⊢
  refine h.trans (Finset.sum_congr rfl fun k hk => ?_)
  rw [Nat.cast_sub (by have := Finset.mem_range.mp hk; omega : k ≤ n)]
