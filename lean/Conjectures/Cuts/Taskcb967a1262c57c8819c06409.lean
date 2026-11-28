import Mathlib

open Finset
namespace PrimePowerComparison

noncomputable abbrev L (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n
noncomputable def P (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
noncomputable def D (n : ℕ) : ℝ := L n - P n

private theorem prime_le (j : ℕ) : P j ≤ L j := by
  by_cases hp : j.Prime
  · simp [P, L, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [P,hp,L]

private theorem prime_pos (j : ℕ) : 0 ≤ P j := by
  by_cases hp : j.Prime
  · simpa [P,hp] using Real.log_nonneg (by exact_mod_cast hp.one_le : (1:ℝ) ≤ j)
  · simp [P,hp]

private theorem remainder_pos (j : ℕ) : 0 ≤ D j := sub_nonneg.mpr (prime_le j)

private theorem shift_mass {N X t a : ℕ} (hN : 1 ≤ N) (hX : X ≤ N) (ha : a ≤ t) :
    ∑ j ∈ range (X-t), D (j+a) ≤ 2 * Real.sqrt N * Real.log N := by
  let F := (range (X-t)).image (fun j => j+a)
  have hsub : F ⊆ Icc 0 N := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
    have := mem_range.mp hj
    exact mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
  calc
    _ = ∑ z ∈ F, D z := (sum_image (fun j _ k _ h => by omega)).symm
    _ ≤ ∑ z ∈ Icc 0 N, D z := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => remainder_pos _
    _ = Chebyshev.psi N - Chebyshev.theta N := by
      rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter, ← sum_sub_distrib]
      rfl
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)

private theorem mang_le {N j : ℕ} (hn : 1 ≤ N) (hj : j ≤ N) : L j ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos j with rfl | hj'
  · simpa [L] using Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hn)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hj') (by exact_mod_cast hj))

private theorem shift_error {N X : ℕ} (hN : 1 ≤ N) (hX : X ≤ N) (t : ℕ) :
    (∑ j ∈ range (X-t), L j * L (j+t)) - (∑ j ∈ range (X-t), P j * P (j+t)) ≤
      4 * Real.sqrt N * (Real.log N)^2 := by
  let J := range (X-t)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hj (j : ℕ) (hj : j ∈ J) : L j * L (j+t) - P j * P (j+t) ≤
      (D j + D (j+t)) * Real.log N := by
    have hh := mem_range.mp hj
    have h₁ := mul_le_mul_of_nonneg_left (mang_le hN (show j+t ≤ N by omega)) (remainder_pos j)
    have h₂ := mul_le_mul_of_nonneg_right ((prime_le j).trans (mang_le hN (by omega))) (remainder_pos (j+t))
    dsimp [D] at h₁ h₂ ⊢
    nlinarith only [h₁,h₂]
  have a := shift_mass (t := t) (a := 0) hN hX (Nat.zero_le _)
  simp only [Nat.add_zero] at a
  have b := shift_mass (t := t) (a := t) hN hX le_rfl
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ J, (D j + D (j+t)) * Real.log N := sum_le_sum hj
    _ = ((∑ j ∈ J, D j) + ∑ j ∈ J, D (j+t)) * Real.log N := by rw [← sum_mul, sum_add_distrib]
    _ ≤ _ := by
      dsimp only [J]
      nlinarith only [mul_le_mul_of_nonneg_right (add_le_add a b) hlog]

noncomputable def C (w : ℕ → ℝ) (X q : ℕ) :=
  ∑ k ∈ Icc 1 ((X-1)/q), ∑ j ∈ range (X-q*k), w j * w (j+q*k)

private theorem monotoneC (X q : ℕ) : C P X q ≤ C L X q := by
  apply sum_le_sum
  intro k _
  apply sum_le_sum
  intro j _
  exact mul_le_mul (prime_le j) (prime_le _) (prime_pos _) ArithmeticFunction.vonMangoldt_nonneg

theorem compare {N X p : ℕ} (hN : 2 ≤ N) (hp : p.Prime) (hupper : N ≤ 4*(p^2)^2) (hX : X ≤ N) :
    C L X (p^2) - C L X p / p ≤ C P X (p^2) - C P X p / p + 8*N*(Real.log N)^2 := by
  let K := (X-1)/(p^2)
  have hdivN : K * p^2 ≤ N := (Nat.div_mul_le_self _ _).trans (by omega)
  have hp0 := hp.pos
  have hqr : (0:ℝ) < (p:ℝ)^2 := by positivity
  have hNs : (Real.sqrt (N:ℝ))^2 = N := Real.sq_sqrt (by positivity)
  have hS : Real.sqrt N ≤ 2*(p:ℝ)^2 := by
    have hhi : (N:ℝ) ≤ 4*((p:ℝ)^2)^2 := by exact_mod_cast hupper
    nlinarith [Real.sqrt_nonneg (N:ℝ),sq_nonneg (p:ℝ)]
  have hK : (K:ℝ) ≤ 2*Real.sqrt N := by
    apply le_of_mul_le_mul_right (a := (p:ℝ)^2) _ hqr
    have hd : (K:ℝ)*(p:ℝ)^2 ≤ N := by exact_mod_cast hdivN
    nlinarith only [hd,hNs,mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg (N:ℝ))]
  have hsum : C L X (p^2) - C P X (p^2) ≤ (K:ℝ)*(4*Real.sqrt N*(Real.log N)^2) := by
    unfold C
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ _k ∈ Icc 1 K, 4*Real.sqrt N*(Real.log N)^2 :=
        sum_le_sum fun k _ => shift_error (by omega) hX _
      _ = _ := by simp [Nat.card_Icc]
  have hm := div_le_div_of_nonneg_right (monotoneC X p) (Nat.cast_nonneg (α := ℝ) p)
  have hscale := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4*Real.sqrt N*(Real.log N)^2 by positivity)
  nlinarith only [hm,hsum,hscale,congrArg (fun s : ℝ => s*(Real.log N)^2) hNs]

end PrimePowerComparison

theorem Conjectures.Cuts.Taskcb967a1262c57c8819c06409 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 x4 : ℕ), (2 : ℕ) ≤ x3 → Nat.Prime x4 → (x4 ^ (2 : ℕ)) ^ (2 : ℕ) ≤ x3 → x3 ≤ (4 : ℕ) * (x4 ^ (2 : ℕ)) ^ (2 : ℕ) → ∀ x9 ≤ x3, x2 (⇑ArithmeticFunction.vonMangoldt) x9 (x4 ^ (2 : ℕ)) - x2 (⇑ArithmeticFunction.vonMangoldt) x9 x4 / ↑x4 ≤ x2 x1 x9 (x4 ^ (2 : ℕ)) - x2 x1 x9 x4 / ↑x4 + (8 : ℝ) * ↑x3 * Real.log ↑x3 ^ (2 : ℕ)) := by
  intro P C N p hN hp _ hupper X hX
  exact PrimePowerComparison.compare hN hp hupper hX
