import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Finset ArithmeticFunction Real Filter
namespace Goldbach.HigherPrimePowerBudget
noncomputable section

def primeWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
def squareWeight (n : ℕ) : ℝ :=
  if n.sqrt.Prime ∧ n.sqrt ^ 2 = n then Real.log n.sqrt else 0
def tailWeight (n : ℕ) : ℝ := vonMangoldt n - primeWeight n - squareWeight n

lemma tail_prime {p : ℕ} (hp : p.Prime) : tailWeight p = 0 := by
  have h : ¬ (p.sqrt.Prime ∧ p.sqrt ^ 2 = p) := fun h =>
    Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (by rw [h.2]; exact hp : (p.sqrt ^ 2).Prime)
  simp [tailWeight, primeWeight, squareWeight, hp, h, vonMangoldt_apply_prime hp]

lemma tail_square {p : ℕ} (hp : p.Prime) : tailWeight (p^2) = 0 := by
  have h : ¬ (p ^ 2).Prime := Nat.Prime.not_prime_pow (by decide)
  simp [tailWeight, primeWeight, squareWeight, h, hp, vonMangoldt_apply_pow,
    vonMangoldt_apply_prime hp]

lemma tail_nonneg (n : ℕ) : 0 ≤ tailWeight n := by
  by_cases h : n.Prime
  · rw [tail_prime h]
  by_cases hs : n.sqrt.Prime ∧ n.sqrt ^ 2 = n
  · exact (hs.2 ▸ (tail_square hs.1).ge)
  simp [tailWeight, primeWeight, squareWeight, h, hs, vonMangoldt_nonneg]

lemma tail_le (n : ℕ) : tailWeight n ≤ vonMangoldt n := by
  have hp : 0 ≤ primeWeight n := by
    unfold primeWeight
    split <;> first | exact Real.log_nonneg (by exact_mod_cast ‹n.Prime›.one_le) | rfl
  have hs : 0 ≤ squareWeight n := by
    unfold squareWeight
    split <;> first | exact Real.log_nonneg (by exact_mod_cast (‹_ ∧ _›.1 : n.sqrt.Prime).one_le) | rfl
  unfold tailWeight
  linarith

/-- The bound is uniform over every subset of the interval, including every residue class. -/
theorem subset_bound (X : ℕ) (hX : 1 ≤ X) (S : Finset ℕ) (hS : S ⊆ Icc 1 X) :
    |∑ n ∈ S, tailWeight n| ≤ (Real.log X / Real.log 2) * (Real.log 4 * (X : ℝ)^(1/3 : ℝ)) := by
  classical
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : 0 ≤ (X : ℝ) := by positivity
  let B := Real.log 4 * (X : ℝ) ^ (1/3 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [abs_of_nonneg (sum_nonneg fun n _ => tail_nonneg n)]
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊(X : ℝ)⌋₊, tailWeight n := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => tail_nonneg n)
      intro n hn
      have hn := mem_Icc.mp (hS hn)
      simpa using mem_Ioc.mpr (show 0 < n ∧ n ≤ X from hn)
    _ = ∑ n ∈ Ioc 0 ⌊(X : ℝ)⌋₊ with IsPrimePow n, tailWeight n := by
      symm
      apply sum_subset (filter_subset _ _)
      intro n hn hn'
      have hnp : ¬ IsPrimePow n := fun hp => hn' (mem_filter.mpr ⟨hn, hp⟩)
      exact le_antisymm ((tail_le n).trans (vonMangoldt_eq_zero_iff.mpr hnp).le) (tail_nonneg n)
    _ ≤ ∑ k ∈ Icc 1 ⌊Real.log X / Real.log 2⌋₊, B := by
      rw [Chebyshev.sum_PrimePow_eq_sum_sum _ hx0]
      apply sum_le_sum
      intro k hk
      have hk1 := (mem_Icc.mp hk).1
      by_cases h3 : 3 ≤ k
      · calc
          _ ≤ Chebyshev.theta ((X : ℝ) ^ (1 / (k : ℝ))) := by
            unfold Chebyshev.theta
            apply sum_le_sum
            intro p hp
            have hprime := (mem_filter.mp hp).2
            simpa [vonMangoldt_apply_pow (by omega : k ≠ 0), vonMangoldt_apply_prime hprime] using tail_le (p^k)
          _ ≤ _ := (Chebyshev.theta_le_log4_mul_x (by positivity)).trans (by
            dsimp [B]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hx (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) (by exact_mod_cast h3 : (3:ℝ) ≤ k)))
      · have hz : ∀ p : ℕ, p.Prime → tailWeight (p^k) = 0 := by
          intro p hp
          rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
          · simpa using tail_prime hp
          · exact tail_square hp
        rw [sum_eq_zero (fun p hp => hz p (mem_filter.mp hp).2)]
        exact hB
    _ ≤ _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg (Real.log_nonneg hx) (by positivity))) hB

/-- Total budget at level X^(3/5); each modulus may choose its own residue class. -/
theorem higher_power_budget :
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ∃ U : ℕ → ℝ,
      (∀ q ∈ Icc 1 ⌊(X : ℝ) ^ (3/5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        let S := (Icc 1 X).filter (fun k => k % q = a % q)
        |(∑ k ∈ S, vonMangoldt k) - (∑ k ∈ S, primeWeight k) - (∑ k ∈ S, squareWeight k)| ≤ U q) ∧
      (∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (3/5 : ℝ)⌋₊, U q) ≤ C * (X : ℝ) ^ (29/30 : ℝ) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/30)).bound (by norm_num : (0:ℝ) < 1))
  refine ⟨Real.log 4 / Real.log 2, max 1 ⌈R⌉₊, by positivity, ?_⟩
  intro X hX
  have hXn : 1 ≤ X := (le_max_left _ _).trans hX
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hXn
  have hxpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hx
  have hXR : R ≤ (X : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast ((le_max_right _ _).trans hX : ⌈R⌉₊ ≤ X))
  have hl := hR (X : ℝ) hXR
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx), abs_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul] at hl
  let B := Real.log X / Real.log 2 * (Real.log 4 * (X : ℝ) ^ (1/3 : ℝ))
  refine ⟨fun _ => B, ?_, ?_⟩
  · intro q hq a ha
    dsimp only
    simp only [← sum_sub_distrib]
    exact subset_bound X hXn _ (filter_subset _ _)
  · simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hB : 0 ≤ B := mul_nonneg (div_nonneg (Real.log_nonneg hx) (by positivity)) (by positivity)
    calc
      _ ≤ (X : ℝ)^(3/5 : ℝ) * B := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hB
      _ = Real.log 4 / Real.log 2 * ((X:ℝ)^(3/5 : ℝ) * (X:ℝ)^(1/3 : ℝ) * Real.log X) := by dsimp [B]; ring
      _ ≤ Real.log 4 / Real.log 2 * ((X:ℝ)^(3/5 : ℝ) * (X:ℝ)^(1/3 : ℝ) * (X:ℝ)^(1/30 : ℝ)) := by gcongr
      _ = _ := by rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num

#print axioms higher_power_budget
end
end Goldbach.HigherPrimePowerBudget
