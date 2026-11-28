import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
open Finset
open Finset in
private theorem residue_square_sum {R : Type*} [AddCommMonoid R] (p : ℕ) (hp : 0 < p) (f : ℕ → R) :
    (∑ r ∈ range (p^2), f r) = ∑ c ∈ range p, ∑ j ∈ range p, f (c+p*j) := by
  classical
  rw [← sum_product']
  refine sum_bij' (fun r _ => (r%p,r/p)) (fun s _ => s.1+p*s.2) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp),
      mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa [pow_two] using mem_range.mp hr))⟩
  · rintro ⟨c,j⟩ hs
    obtain ⟨hc,hj⟩ := mem_product.mp hs
    have hc' := mem_range.mp hc
    have hj' := mem_range.mp hj
    dsimp at hc' hj'
    have h := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hj')
    apply mem_range.mpr
    dsimp
    nlinarith only [h,hc']
  · intro r _
    exact Nat.mod_add_div _ _
  · rintro ⟨c,j⟩ hs
    have hc := mem_range.mp (mem_product.mp hs).1
    dsimp at hc
    simp [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc,Nat.mod_eq_of_lt hc]
  · intro r _
    simp [Nat.mod_add_div]

theorem Conjectures.Cuts.Taska315e3c3ebb6e113f5a86bc3 : (have x1 : (ℕ → ℝ) → ℕ → ℝ → ℂ := fun (x1 : ℕ → ℝ) (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, ↑(x1 x4) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) =>   have x5 : ℕ → ℕ → ℝ := fun (x5 x6 : ℕ) => ∑ x7 ∈ Finset.range x3 with x7 % x4 ^ (2 : ℕ) = x5 + x4 * x6, x2 x7;   ∑ x6 ∈ Finset.range x4, ∑ x7 ∈ Finset.range x4, (x5 x6 x7 - (∑ x8 ∈ Finset.range x4, x5 x6 x8) / ↑x4) ^ (2 : ℕ); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ) (x6 : ℤ), Nat.Prime x5 → x6.natAbs.Coprime (x5 ^ (2 : ℕ)) → ‖x1 x3 x4 (↑x6 / ↑(x5 ^ (2 : ℕ)))‖ ≤ ↑x5 * √(x2 x3 x4 x5)) := by
  classical
  intro S V w X p a hp ha
  let z := Complex.exp (2*Real.pi*Complex.I*((a:ℂ)/((p^2:ℕ):ℂ)))
  have hp2 : 0 < p^2 := pow_pos hp.pos _
  have hz : IsPrimitiveRoot z (p^2) := Complex.isPrimitiveRoot_exp_of_isCoprime a _ hp2.ne'
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa using ha))
  have hu : ‖z‖ = 1 := hz.norm'_eq_one hp2.ne'
  let row (c j : ℕ) := ∑ m ∈ (range X).filter (fun m => m % p^2 = c+p*j), w m
  let avg (c : ℕ) := (∑ j ∈ range p, row c j)/(p:ℝ)
  let D (s : ℕ × ℕ) := row s.1 s.2-avg s.1
  let boxes := (range p) ×ˢ (range p)
  have hgrid : S w X ((a:ℝ)/(p^2:ℕ)) = ∑ m ∈ range X, (w m:ℂ)*z^m := by
    dsimp [S]
    apply sum_congr rfl
    intro m _
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hblock : (∑ m ∈ range X, (w m:ℂ)*z^m) =
      ∑ c ∈ range p, ∑ j ∈ range p, (row c j:ℂ)*z^(c+p*j) := by
    let F (r : ℕ) := (∑ m ∈ (range X).filter (fun m => m % p^2 = r), w m : ℝ)
    change _ = ∑ c ∈ range p, ∑ j ∈ range p, (F (c+p*j):ℂ)*z^(c+p*j)
    rw [← residue_square_sum p hp.pos (fun r => (F r:ℂ)*z^r)]
    rw [← sum_fiberwise_of_maps_to (t:=range (p^2)) (g:=fun m : ℕ => m % p^2)
      (fun m _ => mem_range.mpr (Nat.mod_lt m hp2)) (fun m => (w m:ℂ)*z^m)]
    apply sum_congr rfl
    intro r _
    simp only [F,Complex.ofReal_sum,sum_mul]
    apply sum_congr rfl
    intro m hm
    have he := (mem_filter.mp hm).2
    rw [← he]
    congr 1
    have h := congrArg (fun l : ℕ => z^l) (Nat.mod_add_div m (p^2))
    simpa only [pow_add,pow_mul,hz.pow_eq_one,one_pow,mul_one] using h.symm
  have hrow (c : ℕ) : ∑ j ∈ range p, z^(c+p*j) = 0 := by
    simp only [pow_add,pow_mul,← mul_sum]
    rw [(IsPrimitiveRoot.pow hp2 hz (show p^2=p*p by ring)).geom_sum_eq_zero hp.one_lt, mul_zero]
  have hcenter (c : ℕ) : (∑ j ∈ range p, (row c j:ℂ)*z^(c+p*j)) =
      ∑ j ∈ range p, ((row c j-avg c:ℝ):ℂ)*z^(c+p*j) := by
    simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib,← mul_sum,hrow,mul_zero,sub_zero]
  rw [hgrid,hblock]
  simp_rw [hcenter]
  change ‖∑ c ∈ range p, ∑ j ∈ range p, (D (c,j):ℂ)*z^(c+p*j)‖ ≤ _
  rw [← sum_product']
  calc
    _ ≤ ∑ s ∈ boxes, |D s| := by
      refine (norm_sum_le _ _).trans (sum_le_sum (fun s _ => ?_))
      simp [norm_mul,norm_pow,hu,Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ s ∈ boxes, (1:ℝ)^2) * Real.sqrt (∑ s ∈ boxes, |D s|^2) := by
      simpa only [one_mul] using Real.sum_mul_le_sqrt_mul_sqrt boxes (fun _ => 1) (fun s => |D s|)
    _ = _ := by
      simp [V,boxes,D,row,avg,Finset.sum_product, sq_abs,Real.sqrt_mul_self (Nat.cast_nonneg p : (0:ℝ) ≤ p)]

