import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic

open Finset Filter
open scoped Topology BigOperators

namespace PrimeDensityWeight
private def primes (q a n : ℕ) :=
  (Ioc 0 n).filter (fun p => p.Prime ∧ p ≡ a [MOD q])

private theorem change_index (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ p ∈ S, Nat.Prime p) (q a N : ℕ) (hq : 0 < q)
    (ha : a < q) (ha0 : 0 < a) :
    ∑ p ∈ (primes q a (q*N)).filter (· ∈ S), Real.log p =
      ∑ i ∈ range N, if q*i+a ∈ S then Real.log (q*i+a : ℕ) else 0 := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun i _ => q*i+a)
  · intro i hi
    obtain ⟨hi, hs⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    have hb : q*(i+1) ≤ q*N := Nat.mul_le_mul_left _ hi'
    have hm : (q*i+a) % q = a := by simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by nlinarith⟩,
      hS _ hs, by simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hm⟩,hs⟩
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hij)
  · intro p hp
    obtain ⟨ht,hs⟩ := mem_filter.mp hp
    obtain ⟨hr, _, hm⟩ := mem_filter.mp ht
    have hm' : p % q = a := by simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hm
    have he : q*(p/q)+a=p := by simpa [← hm', Nat.add_comm] using Nat.mod_add_div p q
    have hlt : p / q < N := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      have hle := (mem_Ioc.mp hr).2
      rcases lt_or_eq_of_le hle with h | h
      · simpa [Nat.mul_comm] using h
      · simp [h] at hm'
        omega
    exact ⟨p/q, mem_filter.mpr ⟨mem_range.mpr hlt, by rw [he]; exact hs⟩, he⟩
  · intro i hi
    rfl

theorem transfer (S : Set ℕ) [DecidablePred (· ∈ S)] (hS : ∀ p ∈ S, Nat.Prime p)
    (q a : ℕ) (d : ℝ) (hq : 2 ≤ q) (ha : a < q) (hc : a.Coprime q)
    (hd : ∀ η : ℝ, 0 < η → ∃ n₀, ∀ n ≥ n₀, (d-η)*((primes q a n).card : ℝ) ≤
        ((primes q a n).filter (· ∈ S)).card) (ε : ℝ) (he : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (d-ε)*(q*N : ℕ) ≤ (q.totient:ℝ)*
      ∑ i ∈ range N, if q*i+a ∈ S then Real.log (q*i+a : ℕ) else 0 := by
  have hq' : 0 < q := by omega
  let : NeZero q := ⟨by omega⟩
  have ha0 : 0 < a := by
    by_contra! hz
    have : a=0 := by omega
    simp [this] at hc
    omega
  have ht : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq'
  let P := primes q a
  let B := fun n => (P n).filter (· ∈ S)
  have h₁ : Tendsto (fun n:ℕ => (P n).card * Real.log n / (n:ℝ)) atTop
      (𝓝 ((q.totient:ℝ)⁻¹)) := by
    simpa [P, primes, Function.comp_def] using
      (Nat.tendsto_card_prime_modEq_mul_log_div_atTop hc).comp tendsto_natCast_atTop_atTop
  have h₂ : Tendsto (fun n:ℕ => ((B n).card * Real.log n - ∑ p ∈ B n, Real.log p) / (n:ℝ)) atTop (𝓝 0) := by
    simpa [B,P,primes,filter_filter, and_assoc,Function.comp_def] using
      (Chebyshev.isLittleO_card_prime_with_mul_log_sum_prime_log_with
        (fun p => p ≡ a [MOD q] ∧ p ∈ S)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h₃ := ((h₁.const_mul (d-ε/2)).sub h₂).const_mul (q.totient:ℝ)
  have hv : (q.totient:ℝ)*((d-ε/2)*(q.totient:ℝ)⁻¹-0)=d-ε/2 := by field_simp [ht.ne'] <;> ring
  rw [hv] at h₃
  obtain ⟨n₁,H₁⟩ := eventually_atTop.mp (h₃.eventually_const_lt (show d-ε < d-ε/2 by linarith))
  obtain ⟨n₂,H₂⟩ := hd (ε/2) (by linarith)
  refine ⟨max 1 (max n₁ n₂), ?_⟩
  intro N hN
  let n := q*N
  have hNn : N ≤ n := by dsimp [n]; nlinarith
  have hn₁ : n₁ ≤ n := by omega
  have hn₂ : n₂ ≤ n := by omega
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hw := H₁ n hn₁
  change d-ε < (q.totient:ℝ)*((d-ε/2)*((P n).card*Real.log n/n)-
    (((B n).card*Real.log n-∑ p ∈ B n, Real.log p)/n)) at hw
  have hdc : (d-ε/2)*((P n).card:ℝ)*Real.log n ≤ (B n).card*Real.log n :=
    mul_le_mul_of_nonneg_right (H₂ n hn₂) hl
  rw [← change_index S hS q a N hq' ha ha0]
  change (d-ε)*(n:ℝ) ≤ (q.totient:ℝ)*∑ p ∈ B n, Real.log p
  field_simp [hn.ne'] at hw
  nlinarith only [hw, mul_le_mul_of_nonneg_left hdc ht.le]
end PrimeDensityWeight

theorem Conjectures.Cuts.Taskcb0c37cacf616f35b953ecc3 : (∀ (x1 : Set ℕ) [x2 : DecidablePred fun (x2 : ℕ) => x2 ∈ x1],   (∀ x3 ∈ x1, Nat.Prime x3) →     ∀ (x4 x5 : ℕ) (x6 : ℝ),       (2 : ℕ) ≤ x4 →         x5 < x4 →           x5.Coprime x4 →             (0 : ℝ) ≤ x6 →               x6 ≤ (1 : ℝ) →                 have x12 : ℕ → Finset ℕ := fun (x12 : ℕ) => {x13 ∈ Finset.Icc (1 : ℕ) x12 | Nat.Prime x13 ∧ x13 % x4 = x5};                 (∀ (x13 : ℝ), (0 : ℝ) < x13 → ∃ (x15 : ℕ), ∀ x16 ≥ x15, (x6 - x13) * ↑(x12 x16).card ≤ ↑{x18 ∈ x12 x16 | x18 ∈ x1}.card) → ∀ (x14 : ℝ), (0 : ℝ) < x14 → ∃ (x16 : ℕ), ∀ x17 ≥ x16, (x6 - x14) * ↑(x4 * x17) ≤ ↑x4.totient * ∑ x19 ∈ Finset.range x17, if x4 * x19 + x5 ∈ x1 then Real.log ↑(x4 * x19 + x5) else (0 : ℝ)) := by
  intro S inst hS q a d hq ha hc _ _
  dsimp only
  intro hd ε he
  refine PrimeDensityWeight.transfer S hS q a d hq ha hc ?_ ε he
  intro η hη
  obtain ⟨n,H⟩ := hd η hη
  refine ⟨n, fun x hx => ?_⟩
  have hi : Icc 1 x = Ioc 0 x := Finset.Icc_succ_left_eq_Ioc (0 : ℕ) x
  simpa [PrimeDensityWeight.primes, Nat.ModEq, Nat.mod_eq_of_lt ha, hi] using H x hx
