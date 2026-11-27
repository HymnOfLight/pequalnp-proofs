import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Log

theorem PEqualNP.Outside.L_goldbach_arc_disjoint_explicit_cutoff :
    ∀ n : ℕ, 1000000 ≤ n → 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 < n := by
  intro n hn
  have growth (u : ℕ) : 2 * (u+19)^4 + 3 ≤ 2^(u+19) := by
    induction u with
    | zero => norm_num
    | succ u ih =>
      change 2 * (u+19+1)^4 + 3 ≤ 2^(u+19+1)
      rw [pow_succ 2 (u+19)]
      apply le_trans (b := (2 * (u+19)^4 + 3) * 2) _ (Nat.mul_le_mul_right 2 ih)
      ring_nf
      omega
  let k := Nat.log 2 (n+2)
  have hk : 19 ≤ k := (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega)).2 (by norm_num; omega)
  have hd := growth (k-19)
  rw [Nat.sub_add_cancel hk] at hd
  have hp := Nat.pow_log_le_self 2 (x := n+2) (by omega)
  change 2^k ≤ n+2 at hp
  change 2*(k^2)^2 < n
  rw [← pow_mul]
  change 2 * k^4 < n
  omega
