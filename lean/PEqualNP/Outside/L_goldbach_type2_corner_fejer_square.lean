import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

open scoped ComplexConjugate

theorem PEqualNP.Outside.L_goldbach_type2_corner_fejer_square :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (h : ℕ) (θ : ℝ), ((‖∑ j ∈ Finset.range h, E (2*(j:ℝ)*θ)‖^2 : ℝ) : ℂ) = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h, E (2*((i:ℝ)-(j:ℝ))*θ) := by
  dsimp only
  intro h θ
  rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring
