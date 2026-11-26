import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

private theorem bilinearBand (n U B : ℕ) (c : ℕ → ℝ) (v : ℕ → ℝ) (F : ℕ → ℂ) :
    (∑ m ∈ Finset.range (n+1),
      ((∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m/a),
        c a * v (m/a) : ℝ):ℂ) * F m) =
      ∑ a ∈ Finset.Icc (U+1) B, (c a : ℂ) *
        ∑ r ∈ Finset.Icc (U+1) (n/a), (v r : ℂ) * F (a*r) := by
  classical
  let A := Finset.Icc (U+1) B
  let R := Finset.range (n+1)
  let ok := fun m a : ℕ => a ∣ m ∧ U < m/a
  have hset (m : ℕ) : m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m/a) =
      A.filter (ok m) := by
    ext a
    simp only [Finset.mem_filter, Nat.mem_divisors, A, Finset.mem_Icc, ok]
    by_cases hm : m = 0
    · simp [hm]
    · omega
  calc
    _ = ∑ m ∈ R, ∑ a ∈ A, if ok m a then (c a:ℂ) * (v (m/a):ℂ) * F m else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hset]
      simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : ok m a <;> simp [h]
    _ = ∑ a ∈ A, ∑ m ∈ R.filter (fun m => ok m a), (c a:ℂ) * (v (m/a):ℂ) * F m := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := (Finset.mem_Icc.mp ha).1
      have hpos : 0 < a := by omega
      rw [Finset.mul_sum]
      apply Finset.sum_bij' (fun m _ => m/a) (fun r _ => a*r)
      · intro m hm
        obtain ⟨hmn, hdiv, hl⟩ := Finset.mem_filter.mp hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hmn)
        exact Finset.mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hmn'⟩
      · intro r hr
        obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hr
        have hrn := (Nat.le_div_iff_mul_le hpos).mp hu
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr ?_, dvd_mul_right _ _, ?_⟩
        · rw [Nat.mul_comm] ; omega
        · simpa [Nat.mul_div_cancel_left _ hpos] using Nat.lt_of_succ_le hl
      · intro m hm
        exact Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2.1
      · intro r _
        exact Nat.mul_div_cancel_left _ hpos
      · intro m hm
        rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2.1, mul_assoc]

theorem PEqualNP.Outside.L_goldbach_frontier_type2_b1_b1_bilinear_expansion :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ArithmeticFunction.vonMangoldt (m / a); ∀ (n : ℕ) (t : ℝ), S n (τ₁ n) t = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ∑ r ∈ Finset.Icc (U n + 1) (n / a), ArithmeticFunction.vonMangoldt r * E (((a*r:ℕ):ℝ)*t) := by
  intro E S U B μ τ n t
  exact bilinearBand n (U n) (B n) (fun a => ∑ d ∈ a.divisors.filter (fun d => U n < d), μ d)
    ArithmeticFunction.vonMangoldt (fun m => E ((m:ℝ)*t))
