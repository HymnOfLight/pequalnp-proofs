import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Data.Nat.Sqrt

open Finset Filter
open scoped Topology BigOperators

/-- The Chebyshev-window argument follows the project’s L_goldbach_central_first_moment. -/
private noncomputable def weight (p : ℕ) : ℝ := if p.Prime then Real.log (p : ℝ) else 0

/-- Primes in the window. Its endpoints make both the size and the parity argument exact. -/
private def windowPrimes (k : ℕ) : Finset ℕ := (Ioc (2 * k) (3 * k)).filter Nat.Prime

private theorem window_mass (k : ℕ) :
    ∑ p ∈ windowPrimes k, weight p = Chebyshev.theta (3 * k : ℕ) - Chebyshev.theta (2 * k : ℕ) := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) = ∑ p ∈ Ioc 0 n, weight p := by
    simp [Chebyshev.theta, weight, sum_filter]
  have split := Finset.sum_union (f := weight)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := 2 * k) (c := 2 * k) (d := 3 * k) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)] at split
  have drop : ∑ p ∈ windowPrimes k, weight p = ∑ p ∈ Ioc (2 * k) (3 * k), weight p := by
    rw [windowPrimes, sum_filter]
    refine sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.Prime <;> simp [weight, hp]
  rw [drop, expand, expand, split]
  abel

/-- Two fixed relative-error bounds for the Chebyshev function, from Mathlib's PNT.
See https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/WeakPNT.html#Chebyshev.tendsto_theta_div_atTop. -/
private theorem theta_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

private theorem eventually_large_mass : ∃ K : ℕ, ∀ k ≥ K,
    (k : ℝ)/2 < ∑ p ∈ windowPrimes k, weight p := by
  obtain ⟨K, hK⟩ := theta_bounds
  refine ⟨max K 1, fun k hk ↦ ?_⟩
  have hthree := (hK (3*k) (by omega)).1
  have htwo := (hK (2*k) (by omega)).2
  rw [window_mass]
  push_cast at hthree htwo ⊢
  linarith


private theorem box_bound :
  let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ X : ℕ, 64 ≤ X → (P X).card * ((Finset.Icc X (3*X/2)).filter Nat.Prime).card ≤ ∑ n ∈ E X, H X n := by
  classical
  intro E P H X hX
  let Q := (Finset.Icc X (3*X/2)).filter Nat.Prime
  let R (p n : ℕ) : Prop := p ≤ n ∧ Nat.Prime (n-p)
  have hs : 8 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hs4 : 4 * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) (show 4 ≤ Nat.sqrt X by omega)).trans (Nat.sqrt_le X)
  have bound (p : ℕ) (hp : p ∈ P X) : Q.card ≤ ((E X).filter (R p)).card := by
    change p ∈ (Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime at hp
    obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := Finset.mem_Icc.mp hpI
    apply Finset.card_le_card_of_injOn (fun q : ℕ => p + q)
    · intro q hq
      obtain ⟨hqI, hqP⟩ := Finset.mem_filter.mp (show q ∈ Q from hq)
      obtain ⟨hql, hqu⟩ := Finset.mem_Icc.mp hqI
      change p + q ∈ (E X).filter (R p)
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          (hpP.odd_of_ne_two (by omega)).add_odd (hqP.odd_of_ne_two (by omega))⟩
      · exact ⟨by omega, by simpa using hqP⟩
    · intro a ha b hb hab
      exact Nat.add_left_cancel hab
  change (P X).card * Q.card ≤ _
  calc
    _ = ∑ _p ∈ P X, Q.card := by simp
    _ ≤ ∑ p ∈ P X, ((E X).filter (R p)).card := Finset.sum_le_sum bound
    _ = ∑ p ∈ P X, ∑ n ∈ E X, if R p n then 1 else 0 := by
      simp [Finset.sum_boole]
    _ = ∑ n ∈ E X, ∑ p ∈ P X, if R p n then 1 else 0 := Finset.sum_comm
    _ = _ := by simp [H, R, Finset.sum_boole]

private theorem window_card_lower : ∃ N : ℕ, ∀ n ≥ N, ∀ X ≥ n,
    (n : ℝ) ≤ 12 * (((Icc n (3*n/2)).filter Nat.Prime).card : ℝ) * Real.log (X : ℝ) := by
  classical
  obtain ⟨K, hK⟩ := eventually_large_mass
  refine ⟨max 4 (2*K), ?_⟩
  intro n hn X hX
  let k := n/2
  have hk : K ≤ k := by dsimp [k]; omega
  have hn4 : 4 ≤ n := by omega
  have hkn : n ≤ 3*k := by dsimp [k]; omega
  have hin : windowPrimes k ⊆ (Icc n (3*n/2)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hi, hpr⟩ := mem_filter.mp (show p ∈ (Ioc (2*k) (3*k)).filter Nat.Prime from hp)
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hi
    dsimp [k] at hl hu
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hpr⟩
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hb : ∑ p ∈ windowPrimes k, weight p ≤
      (((Icc n (3*n/2)).filter Nat.Prime).card : ℝ) * (2 * Real.log (X : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ windowPrimes k, 2 * Real.log (X : ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hi, hpr⟩ := mem_filter.mp (hin hp)
        obtain ⟨_, hu⟩ := mem_Icc.mp hi
        have h2X : p ≤ 2 * X := by omega
        have hsq : 2 * X ≤ X ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul_right X (show 2 ≤ X by omega)
        have hlogp := Real.log_le_log (show (0:ℝ)<p by exact_mod_cast hpr.pos)
            (show (p:ℝ) ≤ (X:ℝ)^2 by exact_mod_cast (h2X.trans hsq))
        simpa [weight, hpr, Real.log_pow] using hlogp
      _ = ((windowPrimes k).card : ℝ) * (2 * Real.log (X : ℝ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hin) (by positivity)
  have hsum := hK k hk
  have hkn' : (n : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hkn
  linarith

theorem Conjectures.Goldbach.DynFirstMass :
  let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, c*(X:ℝ)*M X ≤ ∑ n ∈ E X, (H X n:ℝ) := by
  classical
  intro E P H M
  obtain ⟨N, hN⟩ := window_card_lower
  let T := max N 64
  refine ⟨1/288, by norm_num, T * T, ?_⟩
  intro X hX
  have hT : T ≤ Nat.sqrt X := Nat.le_sqrt.mpr hX
  have hs2 : 2 ≤ Nat.sqrt X := by dsimp [T] at hT; omega
  have hsX : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  have hX64 : 64 ≤ X := by dsimp [T] at hT; omega
  have hNX : N ≤ X := by dsimp [T] at hT; omega
  have hNs : N ≤ X.sqrt := by dsimp [T] at hT; omega
  let Q := (Icc X (3*X/2)).filter Nat.Prime
  have hq : (X:ℝ) ≤ 12 * (Q.card:ℝ) * Real.log X := hN X hNX X le_rfl
  have hp₀ := hN X.sqrt hNs X hsX
  have hsub : (Icc X.sqrt (3*X.sqrt/2)).filter Nat.Prime ⊆ P X := by
    intro p hp
    obtain ⟨hi, hpr⟩ := mem_filter.mp hp
    obtain ⟨hl,hu⟩ := mem_Icc.mp hi
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, by omega⟩, hpr⟩
  have hlog : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hs : (X.sqrt:ℝ) ≤ 12 * ((P X).card:ℝ) * Real.log X := by
    calc
      _ ≤ _ := hp₀
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_le_card hsub) (by norm_num)) hlog.le
  have hsqrt : Real.sqrt (X:ℝ) ≤ 2 * (X.sqrt:ℝ) := by
    have hlt : (X:ℝ) < ((X.sqrt : ℝ) + 1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' X
    have h := (Real.sqrt_lt' (by positivity : 0 < (X.sqrt:ℝ)+1)).mpr hlt
    have htwo : (2:ℝ) ≤ X.sqrt := by exact_mod_cast hs2
    linarith
  have hprod := mul_le_mul hq (show Real.sqrt (X:ℝ) ≤ 24 * ((P X).card:ℝ) * Real.log X by linarith)
    (Real.sqrt_nonneg _) (show 0 ≤ 12 * (Q.card:ℝ) * Real.log X by positivity)
  have hboxN : (P X).card * Q.card ≤ ∑ n ∈ E X, H X n := box_bound X hX64
  have hbox : (((P X).card : ℝ) * (Q.card : ℝ)) ≤ ∑ n ∈ E X, (H X n : ℝ) := by exact_mod_cast hboxN
  change (1/288 : ℝ) * X * (Real.sqrt X / (Real.log X)^2) ≤ _
  apply le_trans _ hbox
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hlog)).mpr
  nlinarith only [hprod]
