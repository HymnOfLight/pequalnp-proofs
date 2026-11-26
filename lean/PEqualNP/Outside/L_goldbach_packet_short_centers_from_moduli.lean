import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
namespace ShortCenterCount

private theorem count_bound (q : ℕ) (hq : 0 < q) (P : ℕ → Prop) [DecidablePred P] :
    ((range (q+1)).filter (fun a => Nat.Coprime a q ∧ P a)).card ≤ 2*q.totient := by
  have hs : (range (q+1)).filter (fun a => Nat.Coprime a q ∧ P a) ⊆
      insert q ((range q).filter (fun a => Nat.Coprime q a)) := by
    intro a ha
    obtain ⟨har,hac,_⟩ := mem_filter.mp ha
    have h := mem_range.mp har
    by_cases he : a = q
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_range.mpr (by omega),hac.symm⟩))
  have hcard := (card_le_card hs).trans (card_insert_le _ _)
  rw [← Nat.totient_eq_card_coprime] at hcard
  have hphi := Nat.totient_pos.mpr hq
  omega

theorem sum_bound (s : Finset ℕ) (o sm : ℕ → Prop) [DecidablePred o] [DecidablePred sm]
    (P : ℕ → ℕ → Prop) [∀ q, DecidablePred (P q)] (w : ℕ → ℝ)
    (hs : ∀ q ∈ s, 0 < q) (hw : ∀ q ∈ s, 0 ≤ w q) :
    (∑ q ∈ s.filter o, w q * (((range (q+1)).filter
        (fun a => Nat.Coprime a q ∧ P q a)).card:ℝ) / (q.totient:ℝ)^2) ≤
    2*((∑ q ∈ s.filter sm, w q / q.totient) +
        ∑ q ∈ s.filter (fun q => o q ∧ ¬sm q), w q / q.totient) := by
  classical
  simp only [sum_filter, ← sum_add_distrib, mul_sum]
  apply sum_le_sum
  intro q hq
  have ht : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (hs q hq)
  have hc : (((range (q+1)).filter (fun a => Nat.Coprime a q ∧ P q a)).card:ℝ)
      ≤ 2*(q.totient:ℝ) := by exact_mod_cast count_bound q (hs q hq) (P q)
  have bound : w q * (((range (q+1)).filter (fun a => Nat.Coprime a q ∧ P q a)).card:ℝ) /
      (q.totient:ℝ)^2 ≤ 2*(w q/q.totient) := by
    calc _ ≤ (w q*(2*q.totient))/(q.totient:ℝ)^2 := by gcongr; exact hw q hq
         _ = _ := by field_simp
  have hwq := hw q hq
  by_cases ho : o q <;> by_cases hm : sm q <;> simp [ho,hm,bound]; positivity

end ShortCenterCount

theorem PEqualNP.Outside.L_goldbach_packet_short_centers_from_moduli :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) := by
  classical
  dsimp only
  intro hs hn ε he
  obtain ⟨A,hA⟩ := hs (ε/4) (by positivity)
  obtain ⟨B,hB⟩ := hn (ε/4) (by positivity)
  refine ⟨max A B, ?_⟩
  intro n h
  have lo := hA n (le_trans (le_max_left _ _) h)
  have hi := hB n (le_trans (le_max_right _ _) h)
  let Q := (Nat.log 2 (n+2))^2
  let L := max 1 (Nat.log 2 n / 2)
  let o := fun q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 Q+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty
  let sm := fun q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 Q)^8
  let P := fun (q a : ℕ) => (1:ℝ)/3 < (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*((a:ℝ)/q))) / (L:ℝ)
  let w := fun q : ℕ => min (1:ℝ) ((q:ℝ)/Q)
  apply le_trans (ShortCenterCount.sum_bound (Finset.Icc 1 (Q^2)) o sm P w ?_ ?_)
  · dsimp only [sm,o,w,Q]
    linarith
  · intro q hq
    exact (Finset.mem_Icc.mp hq).1
  · intro q hq
    apply le_min (by norm_num) (by positivity)
