import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Log

theorem PEqualNP.Outside.L_goldbach_vaughan_cutoff_identity :
    let cut (h : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun k => if k ≤ h then f k else 0, (ite_eq_left (Nat.zero_le h)).trans f.map_zero⟩; let L := ArithmeticFunction.vonMangoldt; let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius; let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta; ∀ U V : ℕ, let a := cut U m; let b := cut V L; L = b + a * ArithmeticFunction.log - a * b * z + (m-a) * ((L-b) * z) := by
  intro cut L m z U V a b
  have hl : L * z = ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
  have hm : m * z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  rw [← hl]
  calc
    L = b + (L - b) * (m * z) := by rw [hm]; ring
    _ = _ := by ring
