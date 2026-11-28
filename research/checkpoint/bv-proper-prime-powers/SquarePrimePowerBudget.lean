import Conjectures.Goldbach.QuarticSquareSlice
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Finset Real Filter
namespace Goldbach.SquarePrimePowerBudget
noncomputable section

private theorem complementary_class {x r q : ℕ} (hq : 0 < q) (h : x^2 ≡ r^2 [MOD q]) :
    x ≡ r [MOD q / Nat.gcd q (x+r)] := by
  apply Nat.ModEq.cancel_left_div_gcd hq
  convert h.add_right (r*x) using 1 <;> ring

/-- Roots with the same divisor gcd(q,x+r) have equal doubled residues modulo q.
The argument also covers powers of two. -/
theorem doubled_residue {x y r q : ℕ} (hq : 0 < q) (hr : r.Coprime q)
    (hx : x^2 ≡ r^2 [MOD q]) (hy : y^2 ≡ r^2 [MOD q])
    (hxy : Nat.gcd q (x+r) = Nat.gcd q (y+r)) : 2*x ≡ 2*y [MOD q] := by
  let d := Nat.gcd q (x+r)
  let b := q / d
  have hd : d ∣ q := Nat.gcd_dvd_left .. 
  have hprod : d*b = q := Nat.mul_div_cancel' hd
  have hdx : d ∣ x+r := Nat.gcd_dvd_right .. 
  have hdy : d ∣ y+r := by simpa [d,hxy] using Nat.gcd_dvd_right q (y+r)
  have hmodD : x ≡ y [MOD d] :=
    Nat.ModEq.add_right_cancel' r ((Nat.modEq_zero_iff_dvd.mpr hdx).trans (Nat.modEq_zero_iff_dvd.mpr hdy).symm)
  have hbx : x ≡ r [MOD b] := complementary_class hq hx
  have hby : y ≡ r [MOD b] := by simpa [b,d,hxy] using complementary_class hq hy
  have hmodL := Nat.mod_lcm hmodD (hbx.trans hby.symm)
  let g := Nat.gcd d b
  have hgq : g ∣ q := (Nat.gcd_dvd_left d b).trans hd
  have hg2r : g ∣ 2*r := by
    rw [two_mul]
    exact ((hbx.add_right r).dvd_iff (Nat.gcd_dvd_right d b)).mp ((Nat.gcd_dvd_left d b).trans hdx)
  have hg2 : g ∣ 2 := ((hr.coprime_dvd_right hgq).symm.dvd_mul_right).mp hg2r
  obtain ⟨c,hc⟩ := hg2
  have heq : g * Nat.lcm d b = q := (Nat.gcd_mul_lcm d b).trans hprod
  have ht : g*x ≡ g*y [MOD q] := heq ▸ hmodL.mul_left' g
  convert ht.mul_left c using 1 <;> rw [hc] <;> ring

/-- Count all square roots in an arbitrary reduced residue class up to M. -/
theorem roots_card {q a M : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    ((range (M+1)).filter (fun x => x^2 ≡ a [MOD q])).card ≤ q.divisors.card * (2*M/q + 1) := by
  classical
  let S := (range (M+1)).filter (fun x => x^2 ≡ a [MOD q])
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨r,hr⟩ := hS
    have hMem {x : ℕ} (hx : x ∈ S) : x ≤ M ∧ x^2 ≡ a [MOD q] := by
      simpa [S, Nat.lt_succ_iff] using hx
    have hcop : r.Coprime q := by
      have hc : (r^2).Coprime q := (hMem hr).2.gcd_eq.trans ha
      exact hc.coprime_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0))
    let enc (x : ℕ) := (Nat.gcd q (x+r), 2*x/q)
    calc
      _ ≤ (q.divisors ×ˢ range (2*M/q+1)).card := by
        apply card_le_card_of_injOn enc
        · intro x hx
          exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left .., hq.ne'⟩,
            mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.mul_le_mul_left 2 (hMem hx).1)))⟩
        · intro x hx y hy he
          have hg := congrArg Prod.fst he
          have hd := congrArg Prod.snd he
          have hm := doubled_residue hq hcop ((hMem hx).2.trans (hMem hr).2.symm)
            ((hMem hy).2.trans (hMem hr).2.symm) hg
          change 2*x % q = 2*y % q at hm
          change 2*x/q = 2*y/q at hd
          have hy' := Nat.mod_add_div (2*y) q
          rw [← hm, ← hd, Nat.mod_add_div] at hy'
          omega
      _ = _ := by simp
  · simp [not_nonempty_iff_eq_empty.mp hS]

private def progression (X q a : ℕ) := (Icc 1 X).filter (fun k => k % q = a % q)
private def weight (k : ℕ) : ℝ :=
  if k.sqrt.Prime ∧ k.sqrt ^ 2 = k then Real.log k.sqrt else 0

theorem square_mass {X q a : ℕ} (hX : 1 ≤ X) (hq : 0 < q) (ha : a.Coprime q) :
    |∑ k ∈ progression X q a, weight k| ≤
      (q.divisors.card : ℝ) * (2 * (X : ℝ) ^ (3/5 : ℝ) / q + 1) * Real.log X := by
  classical
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  let T := (progression X q a).filter (fun k => k.sqrt.Prime ∧ k.sqrt^2 = k)
  have hm {k : ℕ} (hk : k ∈ T) : k ≤ X ∧ k % q = a % q ∧ k.sqrt.Prime ∧ k.sqrt ^ 2 = k := by
    have H := mem_filter.mp hk
    have H' := mem_filter.mp H.1
    exact ⟨(mem_Icc.mp H'.1).2, H'.2, H.2⟩
  have hcount : T.card ≤ q.divisors.card * (2*X.sqrt/q+1) := by
    refine le_trans (card_le_card_of_injOn (fun k => Nat.sqrt k) (t := (range (X.sqrt+1)).filter (fun x => x^2 ≡ a [MOD q])) ?_ ?_) (roots_card hq ha)
    · intro k hk
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (hm hk).1)),
        by change k.sqrt^2 % q = a % q; rw [(hm hk).2.2.2]; exact (hm hk).2.1⟩
    · intro x hx' y hy' he
      exact (hm hx').2.2.2.symm.trans ((congrArg (fun z : ℕ => z^2) he).trans (hm hy').2.2.2)
  have hsum : (∑ k ∈ progression X q a, weight k) = ∑ k ∈ T, Real.log k.sqrt := by
    simp [T, sum_filter, weight]
  rw [hsum, abs_of_nonneg (sum_nonneg (fun k hk => Real.log_nonneg (by exact_mod_cast (hm hk).2.2.1.one_le)))]
  have hroot : (X.sqrt : ℝ) ≤ (X : ℝ) ^ (3/5 : ℝ) := by
    exact Real.nat_sqrt_le_real_sqrt.trans (by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  calc
    _ ≤ ∑ _ ∈ T, Real.log X := by
      apply sum_le_sum
      intro k hk
      apply Real.log_le_log (by exact_mod_cast (hm hk).2.2.1.pos)
      exact_mod_cast (Nat.sqrt_le_self k).trans (hm hk).1
    _ = (T.card : ℝ) * Real.log X := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hx)
      refine (by exact_mod_cast hcount : (T.card : ℝ) ≤ (q.divisors.card : ℝ) * ((2*X.sqrt/q : ℕ) + 1 : ℕ)).trans ?_
      push_cast
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add_left
      refine (Nat.cast_div_le (α := ℝ)).trans ?_
      push_cast
      gcongr

/-- Summing the square-root residue budget over the moduli of level 3/5. -/
theorem square_budget_of_divisor_bound
    (divisorBound : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ D * (n : ℝ)^ε) :
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ∃ S : ℕ → ℝ,
      (∀ q ∈ Icc 1 ⌊(X : ℝ) ^ (3/5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |∑ k ∈ progression X q a, weight k| ≤ S q) ∧
      (∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (3/5 : ℝ)⌋₊, S q) ≤ C * (X : ℝ) ^ (2/3 : ℝ) := by
  obtain ⟨D,hD,hdiv⟩ := divisorBound (1/60) (by norm_num)
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/60)).bound (by norm_num : (0:ℝ) < 1))
  refine ⟨5*D, max 1 ⌈R⌉₊, by positivity, ?_⟩
  intro X hX
  have hXn : 1 ≤ X := (le_max_left _ _).trans hX
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hXn
  have hxpos : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hXR : R ≤ (X : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast ((le_max_right _ _).trans hX : ⌈R⌉₊ ≤ X))
  let M := (X : ℝ)^(3/5 : ℝ)
  let Z := (X : ℝ)^(1/60 : ℝ)
  let Q := ⌊M⌋₊
  have hZ : 1 ≤ Z := Real.one_le_rpow hx (by norm_num)
  have hM : 1 ≤ M := Real.one_le_rpow hx (by norm_num)
  have hZ0 : 0 ≤ Z := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hMX : M ≤ (X : ℝ) := (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3/5 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hQ : (Q : ℝ) ≤ M := Nat.floor_le hM0
  have hlog : Real.log X ≤ Z := by
    have hzlog : ‖Real.log (X : ℝ)‖ ≤ 1 * ‖Z‖ := hR (X : ℝ) hXR
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx), abs_of_nonneg hZ0, one_mul] using hzlog
  let S := fun q : ℕ => (D*Z*Z) * (2*M*(q : ℝ)⁻¹ + 1)
  refine ⟨S, ?_, ?_⟩
  · intro q hq a ha
    have hq1 := (mem_Icc.mp hq).1
    have hqX : (q : ℝ) ≤ X := (by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ Q).trans (hQ.trans hMX)
    have hd : (q.divisors.card : ℝ) ≤ D*Z :=
      (hdiv q).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hqX (by norm_num)) hD.le)
    refine (square_mass hXn hq1 ha).trans ?_
    change _ ≤ D*Z*Z*(2*M*(q:ℝ)⁻¹+1)
    calc
      _ ≤ (D*Z) * (2*M/(q:ℝ)+1) * Z := by gcongr
      _ = _ := by rw [div_eq_mul_inv]; ring
  · have hH : (∑ q ∈ Icc 1 Q, (q : ℝ)⁻¹) ≤ 2*Z := by
      have H := harmonic_floor_le_one_add_log M hM
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at H
      have hmLog := Real.log_le_log (by linarith : 0 < M) hMX
      exact H.trans (by linarith)
    have hsum : (∑ q ∈ Icc 1 Q, S q) =
        D*Z*Z*(2*M*(∑ q ∈ Icc 1 Q, (q:ℝ)⁻¹) + Q) := by
      simp only [S, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
    change (∑ q ∈ Icc 1 Q, S q) ≤ _
    rw [hsum]
    calc
      _ ≤ D*Z*Z * (2*M*(2*Z) + M) := by gcongr
      _ ≤ 5*D * (M * Z^3) := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hD.le (sq_nonneg Z)) hM0) (sub_nonneg.mpr hZ)]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [M,Z]
        rw [← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos]
        apply Real.rpow_le_rpow_of_exponent_le hx
        norm_num

#print axioms square_budget_of_divisor_bound

end
end Goldbach.SquarePrimePowerBudget

open Finset Filter
local notation "Moduli" =>
  (fun X : ℕ => Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊)

local notation "InProgression" =>
  (fun (X q a : ℕ) => Finset.filter (fun k => k % q = a % q) (Icc 1 X))

local notation "SquareSum" =>
  (fun X q a : ℕ =>
    ∑ k ∈ InProgression X q a,
      ite (Nat.Prime (Nat.sqrt k) ∧ (Nat.sqrt k) ^ 2 = k) (Real.log (Nat.sqrt k : ℝ)) 0)

/-- Contribution of prime squares to the progression sum at level three fifths. -/
theorem Goldbach.SquarePrimePowerBudget.square_budget : ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ∃ S : ℕ → ℝ,
      (∀ q ∈ Moduli X, ∀ a : ℕ, Nat.Coprime a q → |SquareSum X q a| ≤ S q) ∧
      (∑ q ∈ Moduli X, S q) ≤ C * (X : ℝ) ^ (2 / 3 : ℝ) :=
  Goldbach.SquarePrimePowerBudget.square_budget_of_divisor_bound Conjectures.Goldbach.QuarticSquareSlice_aux.divisor_bound

#print axioms Goldbach.SquarePrimePowerBudget.square_budget
