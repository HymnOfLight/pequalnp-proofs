import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-! The principal-window estimate below adapts the proof of
GoldbachOC103.actual_principal_window_of_zero_weights in DyadicCellShortPrimeFloor
(upstream goldbach-proofs, Apache-2.0). Amplifying all three eventual error
budgets by an arbitrary positive factor yields a uniform relative error tending to zero. -/
/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Authors of the reused source portions: Robby Sneiderman, Matteo Cipollina.

Licensed under the Apache License, Version 2.0.
The full license and original notices accompany this source in the proof archive.
License text: https://www.apache.org/licenses/LICENSE-2.0

Additional adapted source and retained contributor credits:
openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
AlexKontorovich/PrimeNumberTheoremAnd,
commit c39a751132c88b6e8080b74c74023fd95b3d8be0;
rectangle reference commit 2c476fa6441c607096d93c8fc7ac0a227a655dae.
CGandGameEngineLearner/goldbach-proofs:
DNZJSJ, PR 2486, commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f;
muxkin, PR 2458, commit 25c1ef60495052eb22212b5560f90bbc6a4a0917;
DFQDZZ, PR 316, commit e4ab24712555ae8c2c926adf19d368a9fb392c35;
XianWu18, PR 207; wzhxzkk, PR 203.

Modification notice, 2026-11-26: adapted source versions are documented in the
accompanying archive. Unused declarations were removed; module bodies were
joined; auxiliary mathematical identifiers were shortened consistently;
ordinary expressions and local resource limits were normalized. The final
registered theorem name and its statement remain unchanged. Original readable
sources, attribution, exact edits and the identifier map accompany this file.
-/

open Finset
open scoped BigOperators Classical

namespace UniformShortPrimeWindows
noncomputable section
open GoldbachOC103 Vx V7e V86 V1e V6i
theorem scaled_principal (s : ℝ) (hs : 0 < s) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      s * ‖V42 h X‖ ≤ (h : ℝ) := by
  obtain ⟨C, hC, Xz, hz⟩ := actual_zero_weight_bounds
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (s*D) (s*C) (s*C) (by positivity)
  refine ⟨max Xz Xb, ?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_right _ _).trans hX)
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have low : s * (2*(h:ℝ)*(C/(Real.log X)^4)) ≤ (h:ℝ)/16 := by
    have H := mul_le_mul_of_nonneg_left hbud.low_budget hh
    convert H using 1 <;> ring
  have high : s*(576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))) ≤ (h:ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    calc
      _ = _ := by exact (show s * (576*C*X^2*Real.log X^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2)) = 576*(s*C)*X^2*Real.log X^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2) by ring)
      _ ≤ _ := by linarith only [hbud.high_budget, hlower]
  have packet := mul_le_mul_of_nonneg_left hpacket hs.le
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have residual := mul_le_mul_of_nonneg_left hres hs.le
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  linarith only [mul_le_mul_of_nonneg_left hnorm hs.le, residual,
    hbud.residual_budget, hlower, packet, low, high, hh]

theorem theta_relative_error (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x → (x:ℝ)^(3/4:ℝ) ≤ h → h ≤ x →
      |(Chebyshev.theta ((x:ℝ)+h) - Chebyshev.theta x) - h| ≤ ε*h := by
  let s := 2/ε
  have hs : 0 < s := by dsimp [s]; positivity
  have hsε : s * ε = 2 := by dsimp [s]; field_simp
  obtain ⟨X,hX⟩ := scaled_principal s hs
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨M,hM⟩ := exists_nat_ge (max X (GoldbachPrimeBridge.primePowerCutoff (s*|C|)))
  refine ⟨M, ?_⟩
  intro x h hx hl hu
  have hxR : (M:ℝ) ≤ x := by exact_mod_cast hx
  have huR : (h:ℝ) ≤ x := by exact_mod_cast hu
  have h₁ := hX x ((le_max_left _ _).trans (hM.trans hxR)) h hl huR
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at h₁
  have h₂ := GoldbachPrimeBridge.prime_power_error_small (s*|C|) x h
    ((le_max_right _ _).trans (hM.trans hxR)) hl huR
  have hp (z : ℝ) (hz : z ≤ (x:ℝ)+h) :
      s*(Chebyshev.psi z - Chebyshev.theta z) ≤ (h:ℝ)/4 := by
    calc
      _ ≤ s*(C*Real.sqrt z) := mul_le_mul_of_nonneg_left (hC z) hs.le
      _ ≤ s*(|C| * Real.sqrt z) := by gcongr; exact le_abs_self _
      _ ≤ s*(|C| * Real.sqrt ((x:ℝ)+h)) := by gcongr
      _ ≤ _ := by rwa [← mul_assoc]
  have h₃ := hp (x+h : ℝ) le_rfl
  have h₄ := hp (x:ℝ) (by linarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h)])
  have h₅ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_psi (x:ℝ)) hs.le
  have h₆ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_psi ((x:ℝ)+h)) hs.le
  rw [abs_le]
  have hp₁ := mul_le_mul_of_nonneg_left (le_abs_self ((Chebyshev.psi ((x:ℝ)+h)-Chebyshev.psi x)-h)) hs.le
  have hp₂ := mul_le_mul_of_nonneg_left (neg_le_abs ((Chebyshev.psi ((x:ℝ)+h)-Chebyshev.psi x)-h)) hs.le
  constructor <;> apply (mul_le_mul_iff_right₀ hs).mp <;> linarith only [h₁, h₃, h₄, h₅, h₆, hp₁, hp₂, congrArg (fun t : ℝ => t*(h:ℝ)) hsε, (Nat.cast_nonneg h : (0:ℝ) ≤ h)]

end
end UniformShortPrimeWindows
#print axioms UniformShortPrimeWindows.theta_relative_error
