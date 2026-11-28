import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-! The principal-window estimate below adapts the proof of
GoldbachOC103.actual_principal_window_of_zero_weights in DyadicCellShortPrimeFloor
(upstream goldbach-proofs, Apache-2.0). Amplifying all three eventual error
budgets by 32 gives relative error at most one percent. -/
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

namespace DyadicCellUpperMass
noncomputable section
def w (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

private theorem weight_nonnegative (p : ℕ) : 0 ≤ w p := by
  unfold w
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rfl

private theorem locations (N H P W k M : ℕ) (hN : 8*W=N) (hP : P+H≤W)
    (hk : 8*M+16 ≤ k) (hkN : k<N) :
    let A := N/2+P
    let y := A-1
    let z := N-(A+H)
    (M≤y ∧ H≤y ∧ y≤N ∧ y+1=A) ∧ (M≤z ∧ H≤z ∧ z≤N ∧ z+A+H=N) := by
  dsimp only
  omega

/-- The reflected block uses exactly the same half-open interval in reverse order. -/
theorem cell_bounds_of_window
    (hwin : ∃ M : ℕ, ∀ x H : ℕ, M ≤ x → x^3 ≤ H^4 → H ≤ x →
      (∑ t ∈ range H, w (x + 1 + t)) ≤ 101 * (H : ℝ) / 100) :
    ∃ K : ℕ, ∀ k ≥ K, let N := 2^k; let H := 2^(k-k/4); let B := 2^(k/4-3)
    ∀ j ∈ range B,
      (0 ≤ ∑ t ∈ range H, w (N/2+j*H+t)) ∧
      (∑ t ∈ range H, w (N/2+j*H+t)) ≤ 101*(H:ℝ)/100 ∧
      (0 ≤ ∑ t ∈ range H, w (N-(N/2+j*H+t))) ∧
      (∑ t ∈ range H, w (N-(N/2+j*H+t))) ≤ 101*(H:ℝ)/100 := by
  obtain ⟨M, hM⟩ := hwin
  refine ⟨8*M+16, ?_⟩
  intro k hk
  let N : ℕ := 2^k
  let H : ℕ := 2^(k-k/4)
  let B : ℕ := 2^(k/4-3)
  dsimp only
  intro j hj
  change j ∈ range B at hj
  have hjB := mem_range.mp hj
  have hpart : 8 * (B * H) = N := by
    change 2^3 * (2^(k/4-3)*2^(k-k/4)) = (2:ℕ)^k
    rw [←pow_add, ←pow_add]
    congr 1
    omega
  have hBH : (j+1)*H ≤ B*H := Nat.mul_le_mul_right _ hjB
  rw [Nat.add_mul, one_mul] at hBH
  have hkN : k < N := Nat.lt_two_pow_self
  have hc : N^3 ≤ H^4 := by
    dsimp [N,H]
    rw [← pow_mul, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  let A := N/2 + j*H
  let y := A-1
  let z := N-(A+H)
  obtain ⟨hy,hz⟩ := locations N H (j*H) (B*H) k M hpart hBH hk hkN
  have hL := hM y H hy.1 ((Nat.pow_le_pow_left hy.2.2.1 3).trans hc) hy.2.1
  have hR := hM z H hz.1 ((Nat.pow_le_pow_left hz.2.2.1 3).trans hc) hz.2.1
  change (0 ≤ ∑ t ∈ range H, w (A+t)) ∧ _ ∧ _ ∧ _
  refine ⟨sum_nonneg (fun _ _ => weight_nonnegative _), ?_,
    sum_nonneg (fun _ _ => weight_nonnegative _), ?_⟩
  · have hyA : y+1 = A := hy.2.2.2
    rw [hyA] at hL
    exact hL
  · change (∑ t ∈ range H, w (N-(A+t))) ≤ _
    rw [← sum_range_reflect (fun t => w (N-(A+t))) H]
    refine le_trans (le_of_eq (sum_congr rfl fun t ht => ?_)) hR
    congr 1
    have := mem_range.mp ht
    omega


open GoldbachOC103 Vx V7e V86 V1e V6i
private theorem principal_one_percent :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/100 := by
  obtain ⟨C, hC, Xz, hz⟩ := actual_zero_weight_bounds
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (32*D) (32*C) (32*C) (by positivity)
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
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/512 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/512) := by
        apply mul_le_mul_of_nonneg_left _ hh
        linarith only [hbud.low_budget, show 2*(32*C)/(Real.log X)^4 = 32*(2*C/(Real.log X)^4) by ring]
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/512 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    have H := hbud.high_budget
    rw [show 576*(32*C)*X^2*(Real.log X)^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2) =
        32*(576*C*X^2*(Real.log X)^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2)) by ring] at H
    linarith only [H, hlower]
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/256 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/512 := by
    apply hres.trans
    have H := hbud.residual_budget
    rw [mul_assoc 32 D] at H
    linarith only [H, hlower]
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
  linarith only [hnorm, hResidualBudget, hPacketBudget, hh]


private theorem window_upper : ∃ M : ℕ, ∀ x H : ℕ, M ≤ x → x^3 ≤ H^4 → H ≤ x →
    (∑ t ∈ range H, w (x + 1 + t)) ≤ 101 * (H : ℝ) / 100 := by
  obtain ⟨R,hR⟩ := principal_one_percent
  obtain ⟨M,hM⟩ := exists_nat_ge R
  refine ⟨M, ?_⟩
  intro x H hx hpow hHx
  have h := hR (x : ℝ) (hM.trans (by exact_mod_cast hx)) H
    (GoldbachDyadicBridge.rpow_three_quarters_le_of_cube_le_fourth x H hpow) (by exact_mod_cast hHx)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi,
    GoldbachPrimeBridge.psi_nat_add_sub] at h
  have hw (p : ℕ) : w p ≤ ArithmeticFunction.vonMangoldt p := by
    by_cases hp : p.Prime
    · simp [w, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa [w, hp] using ArithmeticFunction.vonMangoldt_nonneg (n := p)
  have heq : (∑ p ∈ Ioc x (x+H), w p) = ∑ t ∈ range H, w (x+1+t) := by
    simpa using GoldbachDyadicBridge.sum_Ioc_pred_eq_range w (x+1) H (by omega)
  rw [← heq]
  have hle := sum_le_sum (s := Ioc x (x+H)) (fun i _ => hw i)
  linarith only [hle, (abs_le.mp h).2]

end
end DyadicCellUpperMass

theorem Conjectures.Cuts.Task0b0706e7f141ead08767f3ce : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∃ (x2 : ℕ),   ∀ x3 ≥ x2,     have x5 : ℕ := (2 : ℕ) ^ x3;     have x6 : ℕ := (2 : ℕ) ^ (x3 - x3 / (4 : ℕ));     have x7 : ℕ := (2 : ℕ) ^ (x3 / (4 : ℕ) - (3 : ℕ));     have x8 : ℕ → ℕ → ℕ := fun (x8 x9 : ℕ) => x5 / (2 : ℕ) + x8 * x6 + x9;     have x9 : ℕ → ℕ → ℝ := fun (x9 x10 : ℕ) => x1 (x8 x9 x10);     have x10 : ℕ → ℕ → ℝ := fun (x10 x11 : ℕ) => x1 (x5 - x8 x10 x11);     ∀ x11 ∈ Finset.range x7, ((0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ)) ∧ (0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ)) := by
  obtain ⟨K,hK⟩ := DyadicCellUpperMass.cell_bounds_of_window DyadicCellUpperMass.window_upper
  refine ⟨K, ?_⟩
  intro k hk
  dsimp only
  intro j hj
  obtain ⟨hl,hu,hr,hv⟩ := hK k hk j hj
  exact ⟨⟨hl,hu⟩,hr,hv⟩
