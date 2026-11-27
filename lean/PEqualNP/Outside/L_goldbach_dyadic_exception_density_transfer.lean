import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_dyadic_exception_density_transfer :
  let reps (n : ℕ) := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p)); let D (X : ℕ) := (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n); let bad (X : ℕ) := (D X).filter (fun n => (reps n).card = 0); let exc (N : ℕ) := (Finset.range (N + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0); ∀ (K N : ℕ) (ε : ℝ), 0 ≤ ε → (∀ n : ℕ, 4 ≤ n → n < 2 ^ K → Even n → (reps n).Nonempty) → (∀ j : ℕ, K ≤ j → ((bad (2 ^ j)).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ)) → ((exc N).card : ℝ) ≤ 2 * ε * (N : ℝ) := by
  classical
  intro reps D bad exc K N ε hε hsmall hlarge
  let C (j : ℕ) := (Finset.range (2^j)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)
  have blockBound (j : ℕ) : ((C j).card : ℝ) ≤ ε * ((2^j : ℕ) : ℝ) := by
    induction j with
    | zero =>
      have hzero : C 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        simp [C] at hn
        omega
      simp [hzero, hε]
    | succ j ih =>
      by_cases hj : K ≤ j
      · have subset : C (j+1) ⊆ C j ∪ bad (2^j) := by
          intro n hn
          obtain ⟨hr, h4, he, h0⟩ := Finset.mem_filter.mp hn
          have hlt := Finset.mem_range.mp hr
          rw [pow_succ] at hlt
          apply Finset.mem_union.mpr
          by_cases hlow : n < 2^j
          · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlow, h4, he, h0⟩)
          · right
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, h4, he⟩, h0⟩
        have hcount := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
        have hc : ((C (j+1)).card : ℝ) ≤ ((C j).card : ℝ) + ((bad (2^j)).card : ℝ) := by exact_mod_cast hcount
        specialize hlarge j hj
        push_cast at *
        rw [pow_succ]
        linarith
      · have hzero : C (j+1) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro n hn
          obtain ⟨hr, h4, he, h0⟩ := Finset.mem_filter.mp hn
          have hlt := (Finset.mem_range.mp hr).trans_le
            (Nat.pow_le_pow_right (by decide : 0 < 2) (show j+1 ≤ K by omega))
          have hp := (hsmall n h4 hlt he).card_pos
          omega
        rw [hzero]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
  by_cases hz : N = 0
  · subst N
    simp [exc]
  · let j := Nat.log 2 N
    have hu : N < 2^(j+1) := Nat.lt_pow_succ_log_self (by decide) _
    have hl : 2^j ≤ N := Nat.pow_log_le_self 2 hz
    have subset : exc N ⊆ C (j+1) := by
      intro n hn
      obtain ⟨hr,hprop⟩ := Finset.mem_filter.mp hn
      have hlower := Finset.mem_range.mp hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprop⟩
    calc
      _ ≤ ((C (j+1)).card : ℝ) := by exact_mod_cast Finset.card_le_card subset
      _ ≤ _ := blockBound _
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (show ((2^j : ℕ) : ℝ) ≤ (N:ℝ) by exact_mod_cast hl) hε
        push_cast at *
        rw [pow_succ]
        linarith
