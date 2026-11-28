import Mathlib
import Conjectures.Goldbach.FiniteWeightedSieveRemoveUnit
import Conjectures.Goldbach.FiniteWeightedSieveFactorCap

private theorem other_factor_le {n p r v q : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hv : v.Prime) (hrv : r < v)
    (hrn : ¬r ∣ n) (hn : n = p + r * v) (hpn : p ∣ n)
    (hq : q.Prime) (hqn : q ∣ n) (hne : q ≠ p) : q ≤ p := by
  have hmul : p ∣ r * v := by
    have t : p ∣ p + r * v := hn ▸ hpn
    exact Nat.dvd_add_self_left.mp t
  rcases hp.dvd_mul.mp hmul with h | h
  · have he : p = r := (Nat.dvd_prime hr).mp h |>.resolve_left hp.ne_one
    exact (hrn (he ▸ hpn)).elim
  · have he : p = v := (Nat.dvd_prime hv).mp h |>.resolve_left hp.ne_one
    subst v
    have hprod : n = (r+1)*p := by rw [hn]; ring
    have hdiv : q ∣ (r+1)*p := hprod ▸ hqn
    rcases hq.dvd_mul.mp hdiv with h | h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (hne ((Nat.dvd_prime hp).mp h |>.resolve_left hq.ne_one)).elim

theorem Conjectures.Cuts.Taskb688ff562472faed7f30960a : (∀ (x1 x2 x3 x4 x5 x6 x7 : ℕ), Nat.Prime x2 → Nat.Prime x3 → Nat.Prime x4 → x3 < x4 → ¬x3 ∣ x1 → x1 = x2 + x3 * x4 → x2 ∣ x1 → Nat.Prime x5 → Nat.Prime x6 → Nat.Prime x7 → x6 < x7 → ¬x6 ∣ x1 → x1 = x5 + x6 * x7 → x5 ∣ x1 → x2 = x5) := by
  intro n p r v q s w hp hr hv hrv hrn hn hpn hq hs hw hsw hsn hn' hqn
  by_contra h
  exact h (Nat.le_antisymm
    (other_factor_le hq hs hw hsw hsn hn' hqn hp hpn h)
    (other_factor_le hp hr hv hrv hrn hn hpn hq hqn (Ne.symm h)))
