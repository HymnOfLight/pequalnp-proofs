import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem Conjectures.Goldbach.DynIncidenceFirst :
let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ X : ℕ, ∑ n ∈ E X, H X n = ∑ p ∈ P X, ((E X).filter (fun n => p≤n ∧ Nat.Prime (n-p))).card := by
  dsimp only
  intro X
  simp only [Finset.card_filter]
  exact Finset.sum_comm
