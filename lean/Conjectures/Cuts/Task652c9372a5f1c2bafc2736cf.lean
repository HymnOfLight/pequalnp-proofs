import Mathlib

/-- A single positive constant bounds the whole finite range, starting at one. -/
private theorem bounded_energy (F : ℕ → ℝ) (B : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → n ≤ B → F n ≤ C * (n : ℝ)^s := by
  let C := 1 + ∑ j ∈ Finset.range (B+1), |F j|
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn hB
  have hsumm := Finset.single_le_sum (f := fun j => |F j|)
    (fun j _ => abs_nonneg (F j)) (Finset.mem_range.mpr (show n < B+1 by omega))
  have hf : F n ≤ C := by dsimp only [C]; linarith [le_abs_self (F n)]
  exact hf.trans (le_mul_of_one_le_right hC.le
    (Real.one_le_rpow (by exact_mod_cast hn) hs))

theorem Conjectures.Cuts.Task652c9372a5f1c2bafc2736cf : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → x13 ≤ (10 : ℕ) ^ (12 : ℕ) → ∑ x16 ∈ Finset.Icc x13 ((2 : ℕ) * x13) with Even x16, Max.max (0 : ℝ) (-x8 x16) ^ (2 : ℕ) ≤ x11 * (↑x13 : ℝ) ^ ((18 / 7 : ℝ) + x9)) := by
  intro w E S Q arcs f major minor ε hε
  obtain ⟨C, hC, h⟩ := bounded_energy
    (fun X => ∑ m ∈ (Finset.Icc X (2*X)).filter Even, (max 0 (-minor m))^2)
    (10^12) (18/7+ε) (by positivity)
  exact ⟨C, 1, hC, h⟩
