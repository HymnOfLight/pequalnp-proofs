import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_farey_spacing_lower :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ, 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq hqQ hr hrQ ha hb hne m
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let z : ℤ := (a:ℤ)*r - b*q - m*q*r
  have hn : z ≠ 0 := by
    intro hz
    change (a:ℤ)*r - b*q - m*q*r = 0 at hz
    have hqr : q ∣ r := by
      apply ha.symm.dvd_of_dvd_mul_left
      apply Int.natCast_dvd_natCast.mp
      push_cast
      exact ⟨b + m*r, by linarith⟩
    have hrq : r ∣ q := by
      apply hb.symm.dvd_of_dvd_mul_left
      apply Int.natCast_dvd_natCast.mp
      push_cast
      exact ⟨a - m*q, by linarith⟩
    have he : q = r := Nat.dvd_antisymm hqr hrq
    subst r
    have eq : (b:ℤ) - a = q * (-m) := by
      apply mul_right_cancel₀ (show (q:ℤ) ≠ 0 by omega)
      linarith
    exact hne.elim (fun H => H rfl) (fun H => H (Nat.modEq_iff_dvd.mpr ⟨-m, eq⟩))
  have hZ : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hn; omega
  have hZR : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast hZ
  have den : (q:ℝ) * r ≤ (Q:ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hqQ) (by exact_mod_cast hrQ) (by positivity) (by positivity)
  have eq : (a:ℝ)/q - b/r - m = (z:ℝ) / ((q:ℝ)*r) := by
    dsimp [z]
    push_cast
    field_simp
    <;> ring
  rw [eq, abs_div, abs_of_pos (mul_pos hqR hrR)]
  exact (one_div_le_one_div_of_le (mul_pos hqR hrR) den).trans
    (div_le_div_of_nonneg_right hZR (by positivity))
