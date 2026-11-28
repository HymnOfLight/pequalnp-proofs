import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic
open Finset
namespace FiniteFourierPrefix
noncomputable def wave (y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)

private lemma wave_add (x y : ℝ) : wave (x+y) = wave x * wave y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma wave_norm (x : ℝ) : ‖wave x‖ = 1 := by rw [wave, Complex.norm_exp]; simp

private lemma wave_step (e : ℝ) (i : ℕ) :
    ‖wave ((i+1:ℕ)*e) - wave ((i:ℝ)*e)‖ ≤ 2*Real.pi*|e| := by
  push_cast
  rw [add_mul, one_mul, wave_add, ← mul_sub_one, norm_mul, wave_norm, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*e)
  simpa [wave, mul_comm Complex.I, Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le] using h

noncomputable def transform (w : ℕ → ℝ) (n : ℕ) (x : ℝ) :=
  ∑ m ∈ range n, (w m : ℂ) * wave ((m:ℝ)*x)

theorem perturbed (w : ℕ → ℝ) (n : ℕ) (x e B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i ≤ n, ‖transform w i x‖ ≤ B) :
    ‖transform w n (x+e)‖ ≤ (1 + 2*Real.pi*(n:ℝ)*|e|)*B := by
  let f (i:ℕ) := (w i:ℂ)*wave ((i:ℝ)*x)
  let g (i:ℕ) := wave ((i:ℝ)*e)
  have heq : transform w n (x+e) = ∑ i ∈ range n, f i • g i := by
    simp [transform,f,g, mul_add,wave_add,mul_assoc,smul_eq_mul]
  rw [heq, sum_range_by_parts']
  apply (norm_sub_le _ _).trans
  have hfirst : ‖(∑ i ∈ range n, f i) • g (n-1)‖ ≤ B := by
    simpa [smul_eq_mul,norm_mul,g,wave_norm,transform,f] using h n le_rfl
  have hsum : ‖∑ i ∈ range (n-1), (∑ j ∈ range (i+1), f j) • (g (i+1)-g i)‖ ≤
      (n:ℝ)*(B*(2*Real.pi*|e|)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ range (n-1), B*(2*Real.pi*|e|) := by
        apply sum_le_sum
        intro i hi
        rw [smul_eq_mul, norm_mul]
        apply mul_le_mul (h (i+1) (by have := mem_range.mp hi; omega)) (wave_step e i) (norm_nonneg _) hB
      _ = ((n-1:ℕ):ℝ)*(B*(2*Real.pi*|e|)) := by simp
      _ ≤ _ := by gcongr; exact_mod_cast Nat.sub_le n 1
  linarith only [hfirst,hsum]
end FiniteFourierPrefix
#print axioms FiniteFourierPrefix.perturbed
