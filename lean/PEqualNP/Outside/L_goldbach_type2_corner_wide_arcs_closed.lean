import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Order.OrderClosed

theorem PEqualNP.Outside.L_goldbach_type2_corner_wide_arcs_closed :
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n : ℕ, IsClosed (wideArcs n) := by
  dsimp only
  intro n
  let Q := (Nat.log 2 (n + 2)) ^ 2
  let B := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  let H := 256 * B * Q
  let A (q a : ℕ) := {t : ℝ | |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}
  have closedA (q a : ℕ) : IsClosed (A q a) :=
    isClosed_le (continuous_id.sub continuous_const).abs continuous_const
  let J := (Finset.Icc 1 B).biUnion fun q => ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).image (fun a => (q,a))
  have heq : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ A q a}
      = ⋃ p ∈ (↑J : Set (ℕ × ℕ)), A p.1 p.2 := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, J, Finset.mem_biUnion,
      Finset.mem_Icc, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨q,a,hq,hB,ha,hc,ht⟩
      exact ⟨(q,a), ⟨q, ⟨hq,hB⟩, a, ⟨by omega, hc⟩, rfl⟩, ht⟩
    · rintro ⟨p,⟨q,⟨hq,hB⟩,a,⟨ha,hc⟩,rfl⟩,ht⟩
      exact ⟨q,a,hq,hB,by omega,hc,ht⟩
  change IsClosed {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ A q a}
  rw [heq]
  exact J.finite_toSet.isClosed_biUnion (fun p _ => closedA p.1 p.2)
