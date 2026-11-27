import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor
/- Adapted from the unconditional zero-weight estimates and window assembly in upstream PR #3746 (commit 58074f8dcc8f681c066f31da555185ed0f33cd5d). The loss factor 64 and the local block estimates below accommodate the shorter frozen window. -/

namespace GoldbachOC103
noncomputable section
open Finset Filter Vx V7e V86 V1e V6i
open scoped BigOperators Classical Topology
structure BlockBudgets (D L H X : ℝ) : Prop where
  scale_ge_four : 4 ≤ X
  log_ge_one : 1 ≤ Real.log X
  smoothing_ge_one : 1 ≤ X^(2/3 : ℝ)
  smoothing_le_half : X^(2/3 : ℝ) ≤ X/2
  split_ge_two : 2 ≤ X^(5/16 : ℝ)
  split_le_scale : X^(5/16 : ℝ) ≤ X
  low_budget : 2*L/(Real.log X)^4 ≤ 1/16
  high_budget :
    576*H*X^2*(Real.log X)^14/
      (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2) ≤ X^(3/4 : ℝ)/1024
  residual_budget :
    D*(X^(2/3 : ℝ)*Real.log X +
      Real.sqrt X*Real.log X/X^(2/3 : ℝ) +
      X^2*Real.log X/(X^(2/3 : ℝ)*X)) ≤ X^(3/4 : ℝ)/1024

theorem eventual_block_budgets (D L H : ℝ) (hD : 0 ≤ D) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → BlockBudgets D L H X := by
  have hd := eventually_power_log_bound (2/3) 1 2 1 0 (by norm_num) (by norm_num)
  have hr := eventually_power_log_bound (2/3) (3/4) (3*D) (1/1024) 1
    (by norm_num) (by norm_num)
  have hh := eventually_power_log_bound (17/24) (3/4) (576*H) (1/1024) 14
    (by norm_num) (by norm_num)
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5/16)).eventually_ge_atTop 2
  have he : ∀ᶠ X : ℝ in atTop, BlockBudgets D L H X := by
    filter_upwards [hd, hr, hh, ht, eventually_ge_atTop (4 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (32*L))]
      with X hδ hres hhi hV hX hlog
    have hX1 : 1 ≤ X := by linarith
    have hXp : 0 < X := by linarith
    have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
    have hL32 : 32*L ≤ Real.log X := (le_max_right _ _).trans hlog
    have hLp : 0 < Real.log X := by linarith
    refine ⟨hX, hL1, Real.one_le_rpow hX1 (by norm_num), ?_, hV, ?_, ?_, ?_, ?_⟩
    · have h := hδ.2
      norm_num only [pow_zero, mul_one, Real.rpow_one, one_mul] at h
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
        simpa only [mul_comm] using h)
    · exact (Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (5/16 : ℝ) ≤ 1)).trans_eq (Real.rpow_one X)
    · apply (div_le_iff₀ (pow_pos hLp 4)).mpr
      have hp : Real.log X ≤ (Real.log X)^4 := by
        simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 4)
      nlinarith
    · have hid := high_packet_power_identity X hXp
      have heq : 576*H*X^2*(Real.log X)^14/
          (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2)=
            576*H*X^(17/24 : ℝ)*(Real.log X)^14 := by
        calc
          _ = (576*H)*(X^2/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2))*(Real.log X)^14 := by ring
          _ = _ := by rw [hid]
      rw [heq]
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hhi.2
    · calc
        _ ≤ D*(3*X^(2/3 : ℝ)*Real.log X) :=
          mul_le_mul_of_nonneg_left (smoothing_residual_le X hX1) hD
        _ ≤ X^(3/4 : ℝ)/1024 := by
          simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hres.2
  exact eventually_atTop.mp he

theorem block_principal_window
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ 64*(h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_block_budgets D C C hD.le
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
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/16 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/16) := mul_le_mul_of_nonneg_left hbud.low_budget hh
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    linarith only [hbud.high_budget, hlower]
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/8 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/16 := by
    linarith only [hres,hbud.residual_budget,hlower]
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
  linarith

theorem block_nat_window (hzero : ActualZeroWeightBounds) :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x →
      (x : ℝ)^(3/4 : ℝ) ≤ 64*(h : ℝ) → h ≤ x →
      ‖V42 h (x : ℝ)‖ ≤ (h : ℝ)/4 := by
  obtain ⟨X₀, hX₀⟩ := block_principal_window hzero
  obtain ⟨M, hM⟩ := exists_nat_ge X₀
  refine ⟨M, ?_⟩
  intro x h hx hlower hupper
  exact hX₀ x (hM.trans (by exact_mod_cast hx)) h hlower (by exact_mod_cast hupper)


end
end GoldbachOC103
namespace Goldbach.BlockArrivals
open Real
noncomputable def blockCutoff (C : ℝ) : ℝ := max 1 ((512 * |C|) ^ 4)

/-- The fixed cutoff is independent of the short-window length. -/
theorem block_prime_power_error (C X h : ℝ)
    (hX : blockCutoff C ≤ X)
    (hlower : X ^ (3 / 4 : ℝ) ≤ 64*h) (hupper : h ≤ X) :
    C * Real.sqrt (X + h) ≤ h / 4 := by
  have hXone : 1 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hfourth : (512 * |C|) ^ 4 ≤ X := (le_max_right _ _).trans hX
  have hroot : 512 * |C| ≤ X ^ (1 / 4 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (512 * |C|) ^ 4)
      hfourth (by norm_num : 0 ≤ (1 / 4 : ℝ))
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ 512 * |C|)] at hh
    norm_num at hh
    exact hh
  have hsqrt : Real.sqrt (X + h) ≤ 2 * Real.sqrt X := by
    calc
      Real.sqrt (X + h) ≤ Real.sqrt (4 * X) :=
        Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt X := by
        rw [Real.sqrt_mul (by norm_num)]
        congr 1
        exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hprod : X ^ (1 / 4 : ℝ) * Real.sqrt X = X ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg X)
  calc
    C * Real.sqrt (X + h) ≤ |C| * Real.sqrt (X + h) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * (2 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ ≤ h / 4 := by nlinarith [hprod]


end Goldbach.BlockArrivals
open Finset Filter
open scoped Topology

/- The theta bounds and dyadic prime count adapt the upstream DynFirstMass proof.
The local pair injection adapts DynInteriorBox to arbitrary block origins. -/
namespace Goldbach.BlockArrivals

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

private theorem window_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := (mem_Ioc.mp hp'.1)
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

theorem small_prime_mass : ∃ X₀ : ℕ, ∀ X ≥ X₀,
    (2/5 : ℝ) * Real.sqrt (X:ℝ) ≤
    (((Ioc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime).card : ℝ) * Real.log X := by
  obtain ⟨K,hK⟩ := theta_bounds
  refine ⟨(K+16)^2, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := by nlinarith [Nat.zero_le K]
  set s := Nat.sqrt X with hs
  have hsK : K ≤ s := by
    rw [hs]; exact le_trans (by omega) (Nat.le_sqrt.mpr (by nlinarith [hX] : (K+16)*(K+16) ≤ X))
  have hs4 : 4 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2 * s)).filter Nat.Prime
  have hx16 : (16:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX16
  set r := Real.sqrt (X:ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = (X:ℝ) := Real.mul_self_sqrt (by linarith)
  have hsr : (s:ℝ) * (s:ℝ) ≤ (X:ℝ) := by exact_mod_cast hss
  have hsl' : (X:ℝ) < ((s:ℝ)+1)*((s:ℝ)+1) := by exact_mod_cast hsl
  have hs4' : (4:ℝ) ≤ s := by exact_mod_cast hs4
  have hsle : (s:ℝ) ≤ r := by nlinarith
  have hrs : r ≤ (s:ℝ) + 1 := by nlinarith
  have hr2 : r ≤ 2 * (s:ℝ) := by linarith
  have hL : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  set L := Real.log (X:ℝ) with hLdef
  -- P count
  have hP1 := window_le s (2*s) (by omega)
  have hbs := hK s hsK
  have hb2s := hK (2*s) (by omega)
  push_cast at hb2s hP1
  have hlog2s : Real.log (2 * (s:ℝ)) ≤ L := by
    apply Real.log_le_log (by linarith)
    have : (4 * s : ℝ) ≤ (X:ℝ) := by exact_mod_cast h4s
    linarith
  have hPc : (0:ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP2 : (17/20 : ℝ) * s ≤ (P.card : ℝ) * L := by
    have h1 : (P.card : ℝ) * Real.log (2 * (s:ℝ)) ≤ (P.card : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlog2s hPc
    linarith [hbs.2, hb2s.1]
  change (2/5:ℝ)*r ≤ (P.card:ℝ)*L
  linarith

def block (X y W : ℕ) := ((Icc X (2*X)).filter Even).filter (fun n => y ≤ n ∧ n < y+W)
def small (X : ℕ) := (Icc X.sqrt (2*X.sqrt)).filter Nat.Prime
def hits (X n : ℕ) := ((small X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card

theorem block_pairs (X y W : ℕ) (hx : 16 ≤ X) (hy : X ≤ y) (hw : y+W ≤ 2*X)
    (hroom : 2*X.sqrt ≤ W/2) :
    (((Ioc X.sqrt (2*X.sqrt)).filter Nat.Prime).card *
      ((Ico y (y+W/2)).filter Nat.Prime).card) ≤ ∑ n ∈ block X y W, hits X n := by
  have hs : 4 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
  have key : ∑ n ∈ block X y W, hits X n =
      (((block X y W) ×ˢ (small X)).filter (fun x => x.2 ≤ x.1 ∧ Nat.Prime (x.1-x.2))).card := by
    rw [card_filter, sum_product]
    apply sum_congr rfl
    intro n _
    unfold hits
    rw [card_filter]
  rw [key, ← card_product]
  apply card_le_card_of_injOn (fun x => (x.2+x.1,x.1))
  · intro x hx'
    simp only [Finset.coe_product, Set.mem_prod, mem_coe, mem_filter, mem_Ioc,
      mem_Ico, mem_Icc, mem_product, block, small] at hx' ⊢
    obtain ⟨⟨⟨h1,h2⟩,hp⟩,⟨⟨h3,h4⟩,hq⟩⟩ := hx'
    have hev : Even (x.2+x.1) := (hq.odd_of_ne_two (by omega)).add_odd (hp.odd_of_ne_two (by omega))
    exact ⟨⟨⟨⟨⟨by omega,by omega⟩,hev⟩,by omega,by omega⟩,⟨⟨by omega,h2⟩,hp⟩⟩,by omega,by simpa using hq⟩
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega

def width (X : ℕ) := X.sqrt * X.sqrt.sqrt

theorem of_short_prime_count {d : ℝ} (hd : 0 < d) {N : ℕ}
    (hshort : ∀ X ≥ N, ∀ y : ℕ, X ≤ y → y+width X ≤ 2*X →
      d*(width X : ℝ) ≤ (((Ico y (y+width X/2)).filter Nat.Prime).card : ℝ)*Real.log X) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y+width X ≤ 2*X →
      c*(width X:ℝ)*(Real.sqrt X/(Real.log X)^2) ≤ ∑ n ∈ block X y (width X), (hits X n:ℝ) := by
  obtain ⟨K,hK⟩ := small_prime_mass
  refine ⟨d*(2/5),by positivity,max 256 (max N K),?_⟩
  intro X hX y hy hw
  have ha : 256 ≤ X := le_trans (le_max_left ..) hX
  have hb : N ≤ X := le_trans (le_max_left ..) ((le_max_right ..).trans hX)
  have hc : K ≤ X := le_trans (le_max_right ..) ((le_max_right ..).trans hX)
  have hs : 16 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
  have ht : 4 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr (by omega)
  have hr : 2*X.sqrt ≤ width X/2 := by
    have hm := Nat.mul_le_mul_left X.sqrt ht
    unfold width
    omega
  have hp := hK X hc
  have hq := hshort X hb y hy hw
  have hpair := block_pairs X y (width X) (by omega) hy hw hr
  have hl : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hreal := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hreal
  have hh := mul_le_mul hp hq (mul_nonneg hd.le (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hl.le)
  rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hl)]
  have final := mul_le_mul_of_nonneg_right hreal (sq_nonneg (Real.log (X:ℝ)))
  nlinarith only [hh,final]

/-- Local counts add without endpoint loss when a longer interval is tiled. -/
theorem prime_tile_floor (a h k : ℕ) {D : ℝ}
    (hlocal : ∀ j < k, D ≤ (((Ico (a+j*h) (a+(j+1)*h)).filter Nat.Prime).card : ℝ)) :
    (k:ℝ)*D ≤ (((Ico a (a+k*h)).filter Nat.Prime).card : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := ih fun j hj => hlocal j (by omega)
    have hq := hlocal k (by omega)
    have hcut : a+k*h ≤ a+(k+1)*h := by simp [Nat.add_mul]
    let A := (Ico a (a+k*h)).filter Nat.Prime
    let B := (Ico (a+k*h) (a+(k+1)*h)).filter Nat.Prime
    have hd : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x h₁ h₂
      have hu := (mem_Ico.mp (mem_filter.mp h₁).1).2
      have hv := (mem_Ico.mp (mem_filter.mp h₂).1).1
      omega
    have hu : A ∪ B = (Ico a (a+(k+1)*h)).filter Nat.Prime := by
      ext x
      simp only [A,B,mem_union,mem_filter,mem_Ico]
      constructor
      · rintro (⟨⟨h₁,h₂⟩,hx⟩|⟨⟨h₁,h₂⟩,hx⟩) <;> exact ⟨⟨by omega,by omega⟩,hx⟩
      · rintro ⟨⟨h₁,h₂⟩,hx⟩
        by_cases hh : x < a+k*h
        · exact Or.inl ⟨⟨h₁,hh⟩,hx⟩
        · exact Or.inr ⟨⟨by omega,h₂⟩,hx⟩
    rw [← hu,card_union_of_disjoint hd]
    change (↑(k+1):ℝ)*D ≤ ((A.card+B.card : ℕ):ℝ)
    push_cast
    change (k:ℝ)*D ≤ (A.card:ℝ) at hp
    change D ≤ (B.card:ℝ) at hq
    linarith

/-- A single uniform theta-increment estimate suffices for the frozen block target. -/
theorem of_theta_increment {d : ℝ} (hd : 0 < d) {N : ℕ}
    (hθ : ∀ X ≥ N, ∀ y : ℕ, X ≤ y → y+width X ≤ 2*X →
      d*(width X:ℝ) ≤ Chebyshev.theta ((y+width X/2-1:ℕ):ℝ) - Chebyshev.theta (y:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y+width X ≤ 2*X →
      c*(width X:ℝ)*(Real.sqrt X/(Real.log X)^2) ≤ ∑ n ∈ block X y (width X), (hits X n:ℝ) := by
  apply of_short_prime_count (d := d/2) (N := max N 256) (by positivity)
  intro X hX y hy hw
  have hn := (le_max_left N 256).trans hX
  have h256 := (le_max_right N 256).trans hX
  have hs : 16 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
  have ht : 4 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr (by omega)
  have hW : 64 ≤ width X := Nat.mul_le_mul hs ht
  let b := y+width X/2-1
  have hyb : y ≤ b := by dsimp [b]; omega
  have hbmax : b ≤ 2*X := by dsimp [b]; omega
  have hlog : Real.log (b:ℝ) ≤ 2*Real.log (X:ℝ) := by
    have hx : (2:ℝ) ≤ X := by exact_mod_cast (show 2≤X by omega)
    have hb : (b:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hbmax
    calc
      _ ≤ Real.log ((X:ℝ)*(X:ℝ)) := Real.log_le_log (by exact_mod_cast (show 0<b by omega)) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by linarith) (by linarith)]; ring
  have hcount : ((Ioc y b).filter Nat.Prime).card ≤
      ((Ico y (y+width X/2)).filter Nat.Prime).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hh,hp⟩ := mem_filter.mp hp
    obtain ⟨ha,hb⟩ := mem_Ioc.mp hh
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by dsimp [b] at hb; omega⟩,hp⟩
  have hpos : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤b by omega))
  have hprod := mul_le_mul (Nat.cast_le (α := ℝ).mpr hcount) hlog hpos (Nat.cast_nonneg _)
  have hmain := (hθ X hn y hy hw).trans ((window_le y b hyb).trans hprod)
  linarith

end Goldbach.BlockArrivals
namespace Goldbach.BlockArrivals

private theorem window_scale {X y : ℕ} (hX : 256 ≤ X) (hy : y ≤ 2*X) :
    (y:ℝ)^(3/4:ℝ) ≤ 64 * ((width X/2-1:ℕ):ℝ) := by
  let s := X.sqrt
  let t := s.sqrt
  have hs : 16 ≤ s := Nat.le_sqrt.mpr (by omega)
  have ht : 4 ≤ t := Nat.le_sqrt.mpr (by omega)
  have hx₁ : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have hs₁ : s < (t+1)*(t+1) := Nat.lt_succ_sqrt s
  have hx₂ : X ≤ (2*s)^2 := by nlinarith
  have hs₂ : s ≤ (2*t)^2 := by nlinarith
  have hroot : Real.sqrt (y:ℝ) ≤ 4*(s:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · exact_mod_cast (show y ≤ (4*s)^2 by nlinarith)
  have hfourth : Real.sqrt (Real.sqrt (y:ℝ)) ≤ 4*(t:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hroot.trans ?_⟩
    exact_mod_cast (show 4*s ≤ (4*t)^2 by nlinarith)
  have hpow : (y:ℝ)^(3/4:ℝ) = Real.sqrt y * Real.sqrt (Real.sqrt y) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      ← Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num)]
    norm_num
  have hw : 64 ≤ width X := Nat.mul_le_mul hs ht
  have hd : width X ≤ 4*(width X/2-1) := by omega
  rw [hpow]
  calc _ ≤ (4*(s:ℝ))*(4*(t:ℝ)) := mul_le_mul hroot hfourth (Real.sqrt_nonneg _) (by positivity)
       _ = 16*(width X:ℝ) := by simp [width,s,t]; ring
       _ ≤ _ := by exact_mod_cast (show 16*width X ≤ 64*(width X/2-1) by omega)
end Goldbach.BlockArrivals
namespace Goldbach.BlockArrivals
theorem of_wide_psi
    (hp : ∃ M : ℕ, ∀ x h : ℕ, M ≤ x → (x:ℝ)^(3/4:ℝ) ≤ 64*(h:ℝ) → h ≤ x →
      |(Chebyshev.psi ((x:ℝ)+(h:ℝ)) - Chebyshev.psi (x:ℝ)) - (h:ℝ)| ≤ (h:ℝ)/4)
    (hq : ∀ C : ℝ, ∃ K : ℕ, ∀ x h : ℕ, K ≤ x → (x:ℝ)^(3/4:ℝ) ≤ 64*(h:ℝ) → h ≤ x →
      C*Real.sqrt ((x:ℝ)+(h:ℝ)) ≤ (h:ℝ)/4) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y+width X ≤ 2*X →
      c*(width X:ℝ)*(Real.sqrt X/(Real.log X)^2) ≤ ∑ n ∈ block X y (width X), (hits X n:ℝ) := by
  obtain ⟨M,hM⟩ := hp
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨K,hK⟩ := hq C
  apply of_theta_increment (d := 1/8) (N := max 256 (max M K)) (by norm_num)
  intro X hx y hxy hw
  have h256 : 256 ≤ X := (le_max_left ..).trans hx
  have hM' : M ≤ y := (le_max_left ..).trans (((le_max_right ..).trans hx).trans hxy)
  have hK' : K ≤ y := (le_max_right ..).trans (((le_max_right ..).trans hx).trans hxy)
  let h := width X/2-1
  have hsmall : h ≤ y := by dsimp [h]; omega
  have he := window_scale h256 (show y ≤ 2*X by omega)
  have he₁ := (abs_le.mp (hM y h hM' he hsmall)).1
  have he₂ := (hC ((y:ℝ)+(h:ℝ))).trans (hK y h hK' he hsmall)
  have he₃ := Chebyshev.theta_le_psi (y:ℝ)
  have hs : 16 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
  have ht : 4 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr (by omega)
  have hw' : 64 ≤ width X := Nat.mul_le_mul hs ht
  have hw'' : (width X:ℝ) ≤ 4*(h:ℝ) := by exact_mod_cast (show width X ≤ 4*h by dsimp [h]; omega)
  have hb : y+width X/2-1=y+h := by dsimp [h]; omega
  rw [hb, Nat.cast_add]
  linarith
end Goldbach.BlockArrivals

theorem Conjectures.Goldbach.DynBlockFirstMass :
let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P H W B M
  apply Goldbach.BlockArrivals.of_wide_psi
  · obtain ⟨K,hK⟩ := GoldbachOC103.block_nat_window GoldbachOC103.actual_zero_weight_bounds
    refine ⟨K,fun x h hx hlo hhi => ?_⟩
    rw [← GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi]
    exact hK x h hx hlo hhi
  · intro C
    obtain ⟨K,hK⟩ := exists_nat_ge (Goldbach.BlockArrivals.blockCutoff C)
    exact ⟨K, fun x h hx hlo hhi => Goldbach.BlockArrivals.block_prime_power_error C x h
      (hK.trans (by exact_mod_cast hx)) hlo (by exact_mod_cast hhi)⟩
