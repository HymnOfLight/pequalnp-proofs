import Mathlib.Data.Nat.BitIndices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace BinaryPowerRefinement

private def mass (s : List ℕ) : ℕ := (s.map (fun e => 2^e)).sum

private theorem split_once (s : List ℕ) (h : s.length < mass s) :
    ∃ t : List ℕ, t.length = s.length + 1 ∧ mass t = mass s := by
  induction s with
  | nil => simp [mass] at h
  | cons e s ih =>
    cases e with
    | zero =>
      have hs : s.length < mass s := by
        simp [mass] at h ⊢
        omega
      obtain ⟨t, ht, hm⟩ := ih hs
      exact ⟨0::t, by simp [ht], by simpa [mass] using hm⟩
    | succ e =>
      exact ⟨e::e::s, by simp, by simp [mass, pow_succ]; omega⟩

private theorem refine_by (d : ℕ) (s : List ℕ) (h : s.length + d ≤ mass s) :
    ∃ t : List ℕ, t.length = s.length + d ∧ mass t = mass s := by
  induction d generalizing s with
  | zero => exact ⟨s, by simp, rfl⟩
  | succ d ih =>
    obtain ⟨u, hu, hm⟩ := split_once s (by omega)
    obtain ⟨t, ht, hM⟩ := ih u (by omega)
    exact ⟨t, by omega, hM.trans hm⟩

private theorem powers_as_sum (s : List ℕ) :
    mass s = ∑ i : Fin s.length, 2^s[i.val] := by
  rw [← List.sum_ofFn]
  change (s.map (fun e => 2^e)).sum = _
  calc
    _ = ((List.ofFn (fun i : Fin s.length => s[i.val])).map (fun e => 2^e)).sum := by
      rw [List.ofFn_getElem]
    _ = _ := by rw [List.map_ofFn]; rfl

end BinaryPowerRefinement

theorem Conjectures.Cuts.Taska126dd796add6b9dea852d9a : (∀ (x1 : ℕ), (13 : ℕ) ≤ x1 → x1.bitIndices.length ≤ (13 : ℕ) → ∃ (x4 : Fin (13 : ℕ) → ℕ), (2 : ℕ) * x1 = ∑ x5 : Fin (13 : ℕ), (2 : ℕ) ^ (x4 x5 + (1 : ℕ))) := by
  intro m hm hbits
  have hmass : BinaryPowerRefinement.mass m.bitIndices = m := Nat.sum_map_two_pow_bitIndices m
  obtain ⟨s, hs, hweight⟩ := BinaryPowerRefinement.refine_by (13 - m.bitIndices.length) m.bitIndices (by omega)
  have hlen : s.length = 13 := by omega
  let e (i : Fin 13) := s[(Fin.cast hlen.symm i).val]
  refine ⟨e, ?_⟩
  have hsum : (∑ i : Fin 13, 2 ^ e i) = m := by
    rw [← hmass, ← hweight, BinaryPowerRefinement.powers_as_sum]
    exact (Finset.sum_equiv (finCongr hlen.symm) (by simp) (by intro i hi; rfl))
  simp only [pow_succ]
  rw [← Finset.sum_mul, hsum, Nat.mul_comm]
