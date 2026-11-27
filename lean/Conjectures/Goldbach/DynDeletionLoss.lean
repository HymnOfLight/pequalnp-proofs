import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem Conjectures.Goldbach.DynDeletionLoss :
∀ (A B D E : Finset ℕ) (t : ℕ), let r := fun (B' : Finset ℕ) (n : ℕ) => (A.filter (fun p => p≤n ∧ n-p ∈ B')).card; t * (E.filter (fun n => t ≤ r B n ∧ r (B \ D) n = 0)).card ≤ A.card * (B ∩ D).card := by
  intro A B D E t
  let r (B' : Finset ℕ) (n : ℕ) := (A.filter (fun p => p ≤ n ∧ n-p ∈ B')).card
  let F := E.filter (fun n => t ≤ r B n ∧ r (B \ D) n = 0)
  change t * F.card ≤ A.card * (B ∩ D).card
  have charge (n : ℕ) (hn : n ∈ F) :
      t ≤ (A.filter (fun p => p ≤ n ∧ n-p ∈ B ∩ D)).card := by
    obtain ⟨_, ht, hzero⟩ := Finset.mem_filter.mp hn
    refine ht.trans (Finset.card_le_card ?_)
    intro p hp
    obtain ⟨hpA, hpn, hpB⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpA, hpn, Finset.mem_inter.mpr ⟨hpB, ?_⟩⟩
    by_contra hD
    have hp' : p ∈ A.filter (fun q => q ≤ n ∧ n-q ∈ B \ D) :=
      Finset.mem_filter.mpr ⟨hpA, hpn, Finset.mem_sdiff.mpr ⟨hpB, hD⟩⟩
    have hpos : 0 < r (B \ D) n := Finset.card_pos.mpr ⟨p, hp'⟩
    omega
  have bound (p : ℕ) :
      (F.filter (fun n => p ≤ n ∧ n-p ∈ B ∩ D)).card ≤ (B ∩ D).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n - p)
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
    · intro n hn m hm heq
      have hn' := (Finset.mem_filter.mp hn).2.1
      have hm' := (Finset.mem_filter.mp hm).2.1
      change n - p = m - p at heq
      omega
  calc
    t * F.card = ∑ _n ∈ F, t := by simp [Nat.mul_comm]
    _ ≤ ∑ n ∈ F, (A.filter (fun p => p ≤ n ∧ n-p ∈ B ∩ D)).card :=
      Finset.sum_le_sum charge
    _ = ∑ p ∈ A, (F.filter (fun n => p ≤ n ∧ n-p ∈ B ∩ D)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _p ∈ A, (B ∩ D).card := Finset.sum_le_sum (fun p _ => bound p)
    _ = A.card * (B ∩ D).card := by simp
