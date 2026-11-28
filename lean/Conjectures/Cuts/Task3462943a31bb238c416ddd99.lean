import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Local factors for the four linear forms in ChenPairAdmissibleShifts. -/
namespace ChenAdmissibleShifts

def admissible (n h k : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℤ, ¬ (p : ℤ) ∣ a*(a+h)*(n-a)*((n:ℤ)-a+k)

def forbidden (p : ℕ) (n h k : ZMod p) : Finset (ZMod p) :=
  {0, -h, n, n+k}

theorem local_iff (p : ℕ) (n : ℤ) (hp : p.Prime) (h k : ℤ) :
    (∃ a : ℤ, ¬ (p : ℤ) ∣ a*(a+h)*(n-a)*((n:ℤ)-a+k)) ↔
    ∃ x : ZMod p, x ∉ forbidden p n h k := by
  let : Fact p.Prime := ⟨hp⟩
  have equiv (a : ℤ) : (p : ℤ) ∣ a*(a+h)*(n-a)*((n:ℤ)-a+k) ↔
      (a : ZMod p) ∈ forbidden p n h k := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [forbidden, Finset.mem_insert, Finset.mem_singleton, mul_eq_zero]
    grind
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun hm => ha ((equiv a).mpr hm)⟩
  · rintro ⟨x, hx⟩
    refine ⟨(x.val : ℤ), fun hd => hx ?_⟩
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using (equiv (x.val : ℤ)).mp hd

theorem number_of_allowed (p : ℕ) [NeZero p] (n h k : ZMod p) :
    (Finset.univ \ forbidden p n h k).card = p - (forbidden p n h k).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]

theorem exists_allowed (p : ℕ) (hp : 5 ≤ p) (n h k : ZMod p) :
    ∃ x : ZMod p, x ∉ forbidden p n h k := by
  let : NeZero p := ⟨by omega⟩
  have hc : (forbidden p n h k).card ≤ 4 := Finset.card_le_four
  have hn := number_of_allowed p n h k
  have pos : 0 < (Finset.univ \ forbidden p n h k).card := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp pos
  exact ⟨x,(Finset.mem_sdiff.mp hx).2⟩

theorem test_two : ∀ n h k : ZMod 2,
    (∃ x : ZMod 2, x ∉ forbidden 2 n h k) ↔ n = 0 ∧ h = 0 ∧ k = 0 := by decide

def modThree (n h k : ZMod 3) : Prop :=
  ((h = 0 ∧ k = 0) ∨ (h = 0 ∧ k ≠ 0 ∧ n-k ≠ 0) ∨ (h ≠ 0 ∧ k = 0 ∧ n-h ≠ 0) ∨ (h ≠ 0 ∧ k ≠ 0 ∧ n-h-k = 0))

theorem test_three : ∀ n h k : ZMod 3,
    (∃ x : ZMod 3, x ∉ forbidden 3 n h k) ↔ modThree n h k := by unfold modThree; decide

theorem criterion (n h k : ℤ) :
    admissible n h k ↔
      ((n : ZMod 2) = 0 ∧ (h : ZMod 2) = 0 ∧ (k : ZMod 2) = 0) ∧
      modThree n h k := by
  constructor
  · intro H
    exact ⟨(test_two ..).mp ((local_iff 2 n Nat.prime_two h k).mp (H 2 Nat.prime_two)),
      (test_three ..).mp ((local_iff 3 n Nat.prime_three h k).mp (H 3 Nat.prime_three))⟩
  · rintro ⟨H₂,H₃⟩ p hp
    apply (local_iff p n hp h k).mpr
    by_cases h₂ : p = 2
    · subst p
      exact (test_two ..).mpr H₂
    by_cases h₃ : p = 3
    · subst p
      exact (test_three ..).mpr H₃
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have := hp.two_le
    exact exists_allowed p (by omega) _ _ _

end ChenAdmissibleShifts

theorem Conjectures.Cuts.Task3462943a31bb238c416ddd99 : (∀ (x1 x2 x3 : ℤ), (∀ (x4 : ℕ), Nat.Prime x4 → ∃ (x6 : ℤ), ¬↑x4 ∣ x6 * (x6 + x2) * (x1 - x6) * (x1 - x6 + x3)) ↔ Even x1 ∧ Even x2 ∧ Even x3 ∧ ((3 : ℤ) ∣ x2 ∧ (3 : ℤ) ∣ x3 ∨ (3 : ℤ) ∣ x2 ∧ ¬(3 : ℤ) ∣ x3 ∧ ¬(3 : ℤ) ∣ x1 - x3 ∨ ¬(3 : ℤ) ∣ x2 ∧ (3 : ℤ) ∣ x3 ∧ ¬(3 : ℤ) ∣ x1 - x2 ∨ ¬(3 : ℤ) ∣ x2 ∧ ¬(3 : ℤ) ∣ x3 ∧ (3 : ℤ) ∣ x1 - x2 - x3)) := by
  intro n h k
  have evenCast (u : ℤ) : ((u : ZMod 2) = 0) ↔ Even u := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    rfl
  have divCast (u : ℤ) : (3 : ℤ) ∣ u ↔ (u : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd u 3).symm
  rw [show (∀ p : ℕ, p.Prime → ∃ a : ℤ, ¬ (p:ℤ) ∣ a*(a+h)*(n-a)*(n-a+k)) ↔ _ from
    ChenAdmissibleShifts.criterion n h k]
  simp only [ChenAdmissibleShifts.modThree, evenCast, divCast, Int.cast_sub, and_assoc]

