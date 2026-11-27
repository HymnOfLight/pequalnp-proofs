import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

private theorem ladderCover (G : ℕ → Prop) (B : ℕ) (ends : List ℕ)
    (hB : ∀ n, 4 ≤ n → n ≤ B → Even n → G n)
    (h : (B :: ends).IsChain (fun lo hi => lo ≤ hi ∧ ∀ n, lo < n → n ≤ hi → Even n → G n)) :
    ∀ n, 4 ≤ n → n ≤ ends.getLastD B → Even n → G n := by
  induction ends generalizing B with
  | nil => simpa using hB
  | cons a xs ih =>
    obtain ⟨hBa, hxs⟩ := List.isChain_cons_cons.mp h
    have ha : ∀ n, 4 ≤ n → n ≤ a → Even n → G n := by
      intro n hn hna he
      by_cases hle : n ≤ B
      · exact hB n hn hle he
      · exact hBa.2 n (by omega) hna he
    simpa only [List.getLastD_cons] using ih a ha hxs

theorem PEqualNP.Outside.L_goldbach_segmented_ladder_coverage :
let G (n : ℕ) := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n; let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; ∀ (B : ℕ) (ends : List ℕ), (∀ n, 4 ≤ n → n ≤ B → Even n → G n) → ((B :: ends).IsChain (fun lo hi => lo ≤ hi ∧ ∀ n, lo < n → n ≤ hi → Even n → G n)) → ∀ n, 4 ≤ n → n ≤ ends.getLastD B → Even n → G n ∧ 0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  dsimp only
  intro B ends hB hc n hn hlast he
  obtain hG := ladderCover _ B ends hB hc n hn hlast he
  refine ⟨hG, ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hG
  apply Finset.sum_pos'
  · intro i hi
    apply mul_nonneg <;> split <;> positivity
  · refine ⟨p, Finset.mem_range.mpr (by omega), ?_⟩
    have hnp : n-p=q := by omega
    rw [ite_eq_left hp, hnp, ite_eq_left hq]
    exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.log_pos (by exact_mod_cast hq.one_lt))
