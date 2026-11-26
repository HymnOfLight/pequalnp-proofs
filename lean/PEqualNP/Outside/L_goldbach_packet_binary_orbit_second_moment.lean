import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

open Finset
open scoped ComplexConjugate

namespace GoldbachPacketOrthogonality

private theorem sum_range_cast {q : ℕ} [NeZero q] {R : Type*} [AddCommMonoid R]
    (F : ZMod q → R) : ∑ a ∈ range q, F a = ∑ a : ZMod q, F a := by
  apply Finset.sum_bij' (s := range q) (t := (univ : Finset (ZMod q))) (f := fun a : ℕ => F (a : ZMod q)) (g := F) (fun a _ => (a : ZMod q)) (fun a _ => a.val)
  · simp
  · exact fun a _ => mem_range.mpr a.val_lt
  · exact fun a ha => ZMod.val_natCast_of_lt (mem_range.mp ha)
  · exact fun a _ => ZMod.natCast_zmod_val a
  · intro _ _; rfl

private theorem char_exp {q : ℕ} [NeZero q] (k a : ℕ) :
    Complex.exp (((2 * Real.pi * ((k:ℝ)*a/q) : ℝ) : ℂ) * Complex.I) =
      ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) := by
  rw [show (k : ZMod q) * a = ((k*a:ℕ) : ZMod q) by simp, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  congr 1
  push_cast
  ring

private theorem char_conj {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ZMod.stdAddChar_apply,
      AddChar.map_neg_eq_inv]

private theorem orthogonality {q : ℕ} [NeZero q] (x y : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (x*a) * conj (ZMod.stdAddChar (y*a))) =
      if x=y then (q:ℂ) else 0 := by
  simp_rw [char_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  by_cases h : x = y
  · simp [h, ZMod.card]
  · simp only [h, ↓reduceIte]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q (sub_ne_zero.mpr h))

/-- Collision count for an arbitrary finite multiset of frequency indices. -/
theorem packet_second_moment {q : ℕ} [NeZero q] {ι : Type*} (s : Finset ι) (k : ι → ℕ) :
    (∑ a ∈ range q, ‖∑ i ∈ s, ZMod.stdAddChar ((k i : ZMod q) * (a : ZMod q))‖^2) =
    (q : ℝ) * (((s ×ˢ s).filter (fun ij => k ij.1 % q = k ij.2 % q)).card : ℝ) := by
  classical
  rw [sum_range_cast (fun a : ZMod q => ‖∑ i ∈ s, ZMod.stdAddChar ((k i : ZMod q)*a)‖^2)]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, if k i % q = k j % q then (q:ℂ) else 0 := by
      apply sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [orthogonality, ZMod.natCast_eq_natCast_iff']
    _ = ∑ ij ∈ s ×ˢ s, (q:ℂ) * (if k ij.1 % q = k ij.2 % q then 1 else 0) := by
      rw [Finset.sum_product]
      simp [mul_ite]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_boole]

end GoldbachPacketOrthogonality

theorem PEqualNP.Outside.L_goldbach_packet_binary_orbit_second_moment :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ q m : ℕ, 0<q → (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, E ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2) = (q:ℝ)*(((Finset.range m ×ˢ Finset.range m).filter (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ) := by
  dsimp only
  intro q m hq
  let : NeZero q := ⟨hq.ne'⟩
  simp_rw [GoldbachPacketOrthogonality.char_exp]
  exact GoldbachPacketOrthogonality.packet_second_moment (Finset.range m) (fun j => 2^(j+1))
