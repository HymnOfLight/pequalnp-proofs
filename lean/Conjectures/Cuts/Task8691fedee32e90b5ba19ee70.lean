import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

private theorem residue_table : ∀ d c k : Fin 6, d.val.Coprime 6 →
    ((d.val * k.val + c.val) % 6 = 4 ↔ k.val =
      if d.val = 1 then (10 - c.val) % 6 else (c.val + 2) % 6) := by decide

theorem Conjectures.Cuts.Task8691fedee32e90b5ba19ee70 : (∀ (x1 x2 x3 : ℕ), x1.Coprime (6 : ℕ) → ((x1 * x3 + x2) % (6 : ℕ) = (4 : ℕ) ↔ x3 % (6 : ℕ) = if x1 % (6 : ℕ) = (1 : ℕ) then ((10 : ℕ) - x2 % (6 : ℕ)) % (6 : ℕ) else (x2 % (6 : ℕ) + (2 : ℕ)) % (6 : ℕ))) := by
  intro d c k hd
  have hmod : (d % 6).Coprime 6 := by
    change Nat.gcd (d % 6) 6 = 1
    rw [← Nat.gcd_rec 6 d, Nat.gcd_comm]
    exact hd
  let res (n : ℕ) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by decide)⟩
  have h := residue_table (res d) (res c) (res k) hmod
  change ((d % 6 * (k % 6) + c % 6) % 6 = 4 ↔ _) at h
  have he : (d % 6 * (k % 6) + c % 6) % 6 = (d*k+c) % 6 :=
    ((Nat.mod_modEq d 6).mul (Nat.mod_modEq k 6)).add (Nat.mod_modEq c 6)
  rw [he] at h
  exact h
