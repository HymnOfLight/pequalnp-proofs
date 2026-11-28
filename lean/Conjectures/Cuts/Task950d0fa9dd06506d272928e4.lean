import Mathlib.Tactic

theorem Conjectures.Cuts.Task950d0fa9dd06506d272928e4 : (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ) (x4 : ℝ), (0 : ℝ) < x3 ∧ (0 : ℝ) < x4 ∧ ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → x7 ≤ x6 → x7 ^ (2 : ℕ) ≤ x6 → x6 < (2 : ℕ) * x7 → ↑x6 ^ (7 / 120 : ℝ) * Real.log ↑x6 ^ x3 ≤ ↑x7 → ↑{x13 ∈ Finset.Icc (x6 - x7) x6 | (4 : ℕ) ≤ x13 ∧ Even x13 ∧ ∀ x14 ∈ Finset.range (x13 + (1 : ℕ)), ¬(Nat.Prime x14 ∧ Nat.Prime (x13 - x14))}.card ≤ x4 * ↑x7 / Real.log ↑x6 ^ x1) := by
  intro A hA
  refine ⟨1, 1, by norm_num, by norm_num, 4, ?_⟩
  intro X H hX hHX hsq hshort _
  have hH : 2 ≤ H := by omega
  have hprod := Nat.mul_le_mul_right H hH
  simp only [sq] at hsq
  omega
