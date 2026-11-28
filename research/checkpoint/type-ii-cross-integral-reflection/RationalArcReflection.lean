import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Finset MeasureTheory
open scoped ComplexConjugate
namespace RationalArcReflection

def arcs (Q : ℕ) (radius : ℕ → ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a:ℝ)/q| ≤ radius q}

private theorem reflect_mem {Q r t} (ht : t ∈ arcs Q r) : 1-t ∈ arcs Q r := by
  obtain ⟨q,a,hq,hQ,ha,hc,hr⟩ := ht
  refine ⟨q,q-a,hq,hQ,Nat.sub_le _ _,(Nat.coprime_self_sub_left ha).2 hc,?_⟩
  rw [Nat.cast_sub ha]
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [show 1-t-((q:ℝ)-a)/q = -(t-(a:ℝ)/q) by field_simp; ring, abs_neg]
  exact hr

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
noncomputable def exponentialSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (u k:ℂ)*phase ((k:ℝ)*t)

private theorem phase_reflect (k : ℤ) (t : ℝ) :
    phase ((k:ℝ)*(1-t)) = conj (phase ((k:ℝ)*t)) := by
  unfold phase
  rw [← Complex.exp_conj]
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
  rw [show (2*(Real.pi:ℂ)*((k:ℂ)*(1-(t:ℂ))))*Complex.I =
    (k:ℂ)*(2*Real.pi*Complex.I) + 2*Real.pi*((k:ℂ)*t)*(-Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem sum_reflect (n : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    exponentialSum n u (1-t) = conj (exponentialSum n u t) := by
  unfold exponentialSum
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  simpa using congrArg (fun z : ℂ => (u k:ℂ)*z) (phase_reflect (k:ℤ) t)

theorem imaginary_part_zero (Q n : ℕ) (r : ℕ → ℝ) (u v : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x)) t).im = 0 := by
  let F := (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x))
  have hf (t : ℝ) : F (1-t) = conj (F t) := by
    have hm : 1-t ∈ arcs Q r ↔ t ∈ arcs Q r :=
      ⟨fun h => by simpa using reflect_mem h, reflect_mem⟩
    by_cases ht : t ∈ arcs Q r
    · simp [F, ht, hm]
    · have hn := phase_reflect (-(n:ℤ)) t
      push_cast at hn
      simpa [F, ht, hm, sum_reflect] using congrArg
        (fun z : ℂ => conj (exponentialSum n u t) * conj (exponentialSum n v t) * z) hn
  let J := ∫ t in (0:ℝ)..1, F t
  have hJ : J = conj J := by
    calc
      J = ∫ t in (0:ℝ)..1, F (1-t) := by
        simp [J, intervalIntegral.integral_comp_sub_left]
      _ = ∫ t in (0:ℝ)..1, conj (F t) := by simp_rw [hf]
      _ = conj J := by simp [J, intervalIntegral, integral_conj]
  change J.im = 0
  have hh := congrArg Complex.im hJ
  simpa using (show J.im = 0 by simp at hh; linarith)
end RationalArcReflection
#print axioms RationalArcReflection.imaginary_part_zero
