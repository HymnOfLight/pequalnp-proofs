import Mathlib

theorem Conjectures.Cuts.Taskecdd8286c6771351e50a0f23 : (∀ (x1 : ℕ), (∃ (x2 : ℕ) (x3 : ℕ), x1 = x2 ^ (2 : ℕ) + x3 ^ (2 : ℕ)) ↔ {x2 ∈ x1.primeFactors | x2 % (4 : ℕ) = (3 : ℕ) ∧ ¬Even (padicValNat x2 x1)}.card = (0 : ℕ)) := by
  classical
  intro m
  rw [Nat.eq_sq_add_sq_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h q hq hh
    exact hh.2 (h q hq hh.1)
  · intro h q hq hmod
    by_contra hodd
    exact h hq ⟨hmod, hodd⟩
