import Mathlib.Tactic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem Conjectures.Goldbach.DynInteriorBox :
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
