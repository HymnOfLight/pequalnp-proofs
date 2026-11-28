import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory Finset
namespace DoublingDeviation
noncomputable section

private theorem exp_poly {y : ℝ} (hy : |y| ≤ 1) :
    Real.exp y ≤ 1+y+y^2/2+y^3/6+5*y^4/96 := by
  have h := (abs_le.mp (Real.exp_bound hy (n := 4) (by decide))).2
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ y^4)] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The two preimages of the doubling map give opposite cosines. -/
private theorem pair_bound (u : ℝ) (hu : |u| ≤ 1) :
    ((1+u/7)*Real.exp (2*u/3) + (1-u/7)*Real.exp (-2*u/3))/2 ≤
      (117/100 : ℝ)*(1+(2*u^2-1)/7) := by
  have ha := abs_le.mp hu
  have hy : |2*u/3| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |-2*u/3| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hp := mul_le_mul_of_nonneg_left (exp_poly hy) (show 0 ≤ 1+u/7 by linarith)
  have hm := mul_le_mul_of_nonneg_left (exp_poly hz) (show 0 ≤ 1-u/7 by linarith)
  have hs : u^2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-u) (by linarith : 0 ≤ 1+u)]
  have hf : u^4 ≤ u^2 := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hs)]
  nlinarith only [hp,hm,hs,hf,sq_nonneg u]

private theorem rate : (117/100 : ℝ)*Real.exp (-(1/3)) ≤ 21/25 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

private def wave (x : ℝ) := Real.cos (2*Real.pi*x)
private def mass (n : ℕ) (x : ℝ) := ∑ j ∈ range n, wave (2^j*x)
private def mgf (n : ℕ) (x : ℝ) := Real.exp ((2/3:ℝ)*(mass n x-n/2))
private def weight (x : ℝ) := 1 + wave x/7
private def weighted (n : ℕ) (x : ℝ) := weight x * mgf n x

private lemma mass_cont (n : ℕ) : Continuous (mass n) := by unfold mass wave; fun_prop
private lemma mgf_cont (n : ℕ) : Continuous (mgf n) := by
  unfold mgf
  exact Real.continuous_exp.comp (continuous_const.mul ((mass_cont n).sub continuous_const))
private lemma weighted_cont (n : ℕ) : Continuous (weighted n) := by
  have hw : Continuous weight := by unfold weight wave; fun_prop
  exact hw.mul (mgf_cont n)

private lemma periodic_mass (n : ℕ) (x : ℝ) : mass n (x+1) = mass n x := by
  unfold mass wave
  apply sum_congr rfl
  intro j _
  convert Real.cos_add_nat_mul_two_pi (2*Real.pi*(2^j*x)) (2^j) using 2 <;> push_cast <;> ring

private lemma mgf_period (n : ℕ) (x : ℝ) : mgf n (x+1) = mgf n x := by
  simp only [mgf, periodic_mass]

private lemma mgf_succ (n : ℕ) (x : ℝ) :
    mgf (n+1) x = Real.exp ((2/3:ℝ)*wave x) * Real.exp (-(1/3)) * mgf n (2*x) := by
  have h : mass (n+1) x = wave x + mass n (2*x) := by
    unfold mass
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    rw [add_comm (wave x)]
    apply congrArg (fun y : ℝ => y + wave x)
    apply sum_congr rfl
    intro i _
    rw [show (2:ℝ)^(i+1)*x=2^i*(2*x) by rw [pow_succ]; ring]
  unfold mgf
  rw [h, ← Real.exp_add, ← Real.exp_add]
  push_cast
  congr 1
  ring

private lemma halves (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ x in (0:ℝ)..1, F x) =
      ∫ x in (0:ℝ)..1, (F (x/2) + F (x/2+1/2))/2 := by
  have hl := intervalIntegral.integral_comp_div (a:= (0:ℝ)) (b:=1) F (by norm_num : (2:ℝ) ≠ 0)
  have hr := intervalIntegral.integral_comp_div_add (a:= (0:ℝ)) (b:=1) F (by norm_num : (2:ℝ) ≠ 0) (1/2)
  have h1 : Continuous (fun x : ℝ => F (x/2)) := by fun_prop
  have h2 : Continuous (fun x : ℝ => F (x/2+1/2)) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (h1.intervalIntegrable ..) (h2.intervalIntegrable ..),hl,hr]
  norm_num [smul_eq_mul] at *
  linarith [intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ:=volume) 0 (1/2)) (hF.intervalIntegrable (μ:=volume) (1/2) 1)]

private lemma step (n : ℕ) (x : ℝ) :
    (weighted (n+1) (x/2) + weighted (n+1) (x/2+1/2))/2 ≤
      (21/25:ℝ)*weighted n x := by
  let u := wave (x/2)
  have hneg : wave (x/2+1/2) = -u := by
    dsimp [u,wave]
    rw [show 2*Real.pi*(x/2+1/2) = 2*Real.pi*(x/2)+Real.pi by ring, Real.cos_add_pi]
  have hd : wave x = 2*u^2-1 := by
    dsimp [u,wave]
    rw [show 2*Real.pi*x = 2*(2*Real.pi*(x/2)) by ring, Real.cos_two_mul]
  have h := pair_bound u (Real.abs_cos_le_one _)
  have hw : 0 ≤ 1+(2*u^2-1)/7 := by nlinarith [sq_nonneg u]
  have hm : 0 ≤ mgf n x := (Real.exp_pos _).le
  unfold weighted weight
  rw [mgf_succ,mgf_succ,show 2*(x/2)=x by ring,show 2*(x/2+1/2)=x+1 by ring,mgf_period,hneg,hd]
  change ((1+u/7)*(Real.exp ((2/3)*u)*Real.exp (-(1/3))*mgf n x) +
    (1+ -u/7)*(Real.exp ((2/3)*(-u))*Real.exp (-(1/3))*mgf n x))/2 ≤ _
  convert (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right h (Real.exp_pos (-(1/3))).le).trans
      (show 117/100*(1+(2*u^2-1)/7)*Real.exp (-(1/3)) ≤ 21/25*(1+(2*u^2-1)/7) by
        nlinarith only [mul_le_mul_of_nonneg_right rate hw])) hm) using 1 <;> ring_nf


private lemma moment (n : ℕ) :
    (∫ x in (0:ℝ)..1, weighted n x) ≤ (8/7:ℝ)*(21/25:ℝ)^n := by
  induction n with
  | zero =>
    simp only [pow_zero, mul_one]
    calc
      _ ≤ ∫ _ in (0:ℝ)..1, (8/7:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) ((weighted_cont _).intervalIntegrable ..) intervalIntegrable_const
        intro x _
        simp [weighted,mgf,mass,weight,wave]
        linarith [Real.cos_le_one (2*Real.pi*x)]
      _ = _ := by norm_num
  | succ n ih =>
    rw [halves _ (weighted_cont _)]
    have hF := weighted_cont (n+1)
    have hG := weighted_cont n
    calc
      _ ≤ ∫ x in (0:ℝ)..1, (21/25:ℝ)*weighted n x := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((show Continuous _ by fun_prop).intervalIntegrable ..)
          ((show Continuous _ by fun_prop).intervalIntegrable ..)
        intro x _
        exact step n x
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul, pow_succ]
        linarith

theorem deviation (n : ℕ) :
    (∫ x in (0:ℝ)..1, if (n:ℝ)/2 < mass n (2*x) then (1:ℝ) else 0)
       ≤ 2 * (21/25:ℝ)^n := by
  have hM : Continuous (fun x : ℝ => mass n (2*x)) :=
    (mass_cont n).comp (by fun_prop : Continuous (fun x : ℝ => 2*x))
  have hG := mgf_cont n
  have hMeas : MeasurableSet {x : ℝ | (n:ℝ)/2 < mass n (2*x)} :=
    measurableSet_lt measurable_const hM.measurable
  have hi : IntervalIntegrable (fun x : ℝ => if (n:ℝ)/2 < mass n (2*x) then (1:ℝ) else 0)
      volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_const (a:=(0:ℝ)) (b:=1) (μ:=volume) (c:=(1:ℝ))).def'.integrable.indicator hMeas
  calc
    _ ≤ ∫ x in (0:ℝ)..1, mgf n (2*x) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi
        ((show Continuous _ by fun_prop).intervalIntegrable ..)
      intro x _
      split_ifs with hx
      · apply Real.one_le_exp
        linarith
      · exact (Real.exp_pos _).le
    _ = ∫ x in (0:ℝ)..1, mgf n x := by
      rw [halves _ (show Continuous (fun x : ℝ => mgf n (2*x)) by fun_prop)]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [show 2*(x/2)=x by ring,show 2*(x/2+1/2)=x+1 by ring,mgf_period]
      ring
    _ ≤ ∫ x in (0:ℝ)..1, (7/6:ℝ)*weighted n x := by
      have hW := weighted_cont n
      apply intervalIntegral.integral_mono_on (by norm_num) (hG.intervalIntegrable ..)
        ((show Continuous _ by fun_prop).intervalIntegrable ..)
      intro x _
      have hw : 1 ≤ (7/6:ℝ)*weight x := by
        unfold weight wave
        linarith [Real.neg_one_le_cos (2*Real.pi*x)]
      simpa only [weighted, ← mul_assoc,one_mul] using
        mul_le_mul_of_nonneg_right hw (show 0 ≤ mgf n x from (Real.exp_pos _).le)
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul]
      nlinarith only [moment n, pow_nonneg (by norm_num : (0:ℝ) ≤ 21/25) n]

theorem frozen (n : ℕ) :
    (∫ x in (0:ℝ)..1, if (n:ℝ)/2 < ∑ j ∈ range n, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x)
           then (1:ℝ) else 0) ≤ 2*(21/25:ℝ)^n := by
  have h (x : ℝ) : mass n (2*x) = ∑ j ∈ range n, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x) := by
    unfold mass wave
    apply sum_congr rfl
    intro i _
    congr 1
    ring
  simpa only [h] using deviation n

end
end DoublingDeviation

theorem Conjectures.Cuts.Taskc47543a5f4a9f338db5e8f4e : (∀ (x1 : ℕ), (∫ (x2 : ℝ) in (0 : ℝ)..(1 : ℝ), if ↑x1 / (2 : ℝ) < ∑ x3 ∈ Finset.range x1, Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x3 + (1 : ℕ)) * x2) then (1 : ℝ) else (0 : ℝ)) ≤ (2 : ℝ) * (21 / 25 : ℝ) ^ x1) := by
  exact DoublingDeviation.frozen
