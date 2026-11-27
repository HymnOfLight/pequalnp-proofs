import Mathlib.Tactic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem Conjectures.Goldbach.DynFactorialCollisions :
  let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let K := fun (X p q : ℕ) => ((E X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card; ∀ X : ℕ, (∑ n ∈ E X, H X n * (H X n - 1)) = ∑ p ∈ P X, ∑ q ∈ (P X).erase p, K X p q := by
  classical
  intro E P H K X
  let R (p n : ℕ) : Prop := p ≤ n ∧ Nat.Prime (n - p)
  let A (n : ℕ) := (P X).filter (fun p => R p n)
  have row (n : ℕ) :
      H X n * (H X n - 1) =
        ∑ p ∈ P X, ∑ q ∈ (P X).erase p, if R p n ∧ R q n then 1 else 0 := by
    change (A n).card * ((A n).card - 1) = _
    calc
      _ = ∑ p ∈ A n, ((A n).erase p).card := by
        rw [Finset.sum_congr rfl (fun p hp => Finset.card_erase_of_mem hp)]
        simp
      _ = ∑ p ∈ P X, ∑ q ∈ (P X).erase p, if R p n ∧ R q n then 1 else 0 := by
        unfold A
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : R p n
        · have he : ((P X).filter (fun q => R q n)).erase p =
              ((P X).erase p).filter (fun q => R q n) := by
            ext q
            simp [and_assoc, and_left_comm, and_comm]
          simp [h, he, Finset.sum_boole]
        · simp [h]
  calc
    _ = ∑ n ∈ E X, ∑ p ∈ P X, ∑ q ∈ (P X).erase p, if R p n ∧ R q n then 1 else 0 :=
      Finset.sum_congr rfl (fun n _ => row n)
    _ = ∑ p ∈ P X, ∑ n ∈ E X, ∑ q ∈ (P X).erase p, if R p n ∧ R q n then 1 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      simp [Finset.sum_boole, K, R, and_assoc, and_left_comm, and_comm]
