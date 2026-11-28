import Mathlib

theorem Conjectures.Cuts.Taska571f1c3077acc5aaa440e63 : (∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Bool) (x5 : ℝ), (0 : ℕ) < x3 → (∀ x7 ∈ Finset.Icc (x1 / x3) ((x1 + x2) / x3), ↑{x9 ∈ Finset.Ico (x7 * x3) ((x7 + (1 : ℕ)) * x3) | x4 x9 = Bool.true}.card ≤ x5) → ↑{x8 ∈ Finset.Icc x1 (x1 + x2) | x4 x8 = Bool.true}.card ≤ ↑(Finset.Icc (x1 / x3) ((x1 + x2) / x3)).card * x5) := by
  classical
  intro X H w P M hw hb
  let J := Finset.Icc (X / w) ((X + H) / w)
  let B (j : ℕ) := (Finset.Ico (j*w) ((j+1)*w)).filter (fun n => P n = true)
  have sub : ((Finset.Icc X (X+H)).filter (fun n => P n = true)) ⊆ J.biUnion B := by
    intro n hn
    obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hx,hy⟩ := Finset.mem_Icc.mp hi
    refine Finset.mem_biUnion.mpr ⟨n/w, Finset.mem_Icc.mpr
      ⟨Nat.div_le_div_right hx, Nat.div_le_div_right hy⟩, Finset.mem_filter.mpr ⟨?_,hp⟩⟩
    exact Finset.mem_Ico.mpr ⟨Nat.div_mul_le_self _ _, by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n hw⟩
  have hn := (Finset.card_le_card sub).trans Finset.card_biUnion_le
  calc
    _ ≤ ((∑ j ∈ J, (B j).card : ℕ) : ℝ) := by exact_mod_cast hn
    _ = ∑ j ∈ J, ((B j).card : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ _j ∈ J, M := Finset.sum_le_sum fun j hj => hb j hj
    _ = _ := by simp [J]
