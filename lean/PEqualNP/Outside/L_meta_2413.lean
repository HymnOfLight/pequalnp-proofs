import Mathlib.Data.List.Forall2
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2413

private abbrev rises (a b : Bool) := a = true → b = true

private theorem rise_get {a b : List Bool} (h : List.Forall₂ rises a b) (i : ℕ) :
    rises (a.getD i false) (b.getD i false) := by
  induction h generalizing i with
  | nil => exact fun e => e
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

/-- Wire monotonicity with an explicit relation on input lists. -/
private theorem wires_mono (C : Circuit) (hm : PEqualNP.EdgeOwnership.AndOrOnly C)
    {a b : List Bool} (h : List.Forall₂ (fun u v : Bool => u=true → v=true) a b) (i : ℕ) :
    (C.wires a).getD i false=true → (C.wires b).getD i false=true := by
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have ind (gs : List Gate) (hgs : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) :
      ∀ (w z : List Bool), List.Forall₂ rises w z →
        List.Forall₂ rises (gs.foldl step w) (gs.foldl step z) := by
    induction gs with
    | nil => exact fun _ _ e => e
    | cons g gs ih =>
      intro w z e
      apply ih (fun v hv => hgs v (by simp [hv]))
      apply List.rel_append e
      apply List.Forall₂.cons _ .nil
      change g.op.eval _ =true → g.op.eval _ =true
      rcases hgs g (by simp) with hg | hg
      · simp only [hg,GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
        rintro hs v ⟨k,hk,rfl⟩
        exact rise_get e k (hs _ ⟨k,hk,rfl⟩)
      · simp only [hg,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
        rintro ⟨v,⟨k,hk,rfl⟩,hv⟩
        exact ⟨_,⟨k,hk,rfl⟩,rise_get e k hv⟩
  exact rise_get (ind C.gates hm a b h) i

end PEqualNP.Outside.L_meta_2413

open PEqualNP.Outside.L_meta_2413

/-- The two point signals fire the output on a soundness test with no line. -/
theorem PEqualNP.Outside.L_meta_2413 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ (j a b : ℕ) (p p' : Fin N), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) → a ≠ b → (∀ z1 : Fin n → Bool, (∃ h1 : pw p < n, z1 ⟨pw p, h1⟩ = true) → (C.wires (List.ofFn z1)).getD (b) false = true → PEqualNP.MetaComplexity.circuitFun n C z1 = true) → (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val = pw p)))).getD (a) false = true → (∀ z2 : Fin n → Bool, (∃ h2 : pw p' < n, z2 ⟨pw p', h2⟩ = true) → (C.wires (List.ofFn z2)).getD (a) false = true → PEqualNP.MetaComplexity.circuitFun n C z2 = true) → (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val = pw p')))).getD (b) false = true → False := by
  intro n N M pw lw I C hAO _ _ _ hpn _ hreject j a b p p' _ _ hout _ _ hb
  let P : Finset (Fin N) := {p,p'}
  let z (k : Fin n) : Bool := decide (k.val ∈ P.image pw ∪ (∅ : Finset (Fin M)).image lw)
  let single (k : Fin n) : Bool := decide (k.val = pw p')
  have contains (r : Fin N) (hr : r ∈ P) : z ⟨pw r,hpn r⟩ = true := by
    apply decide_eq_true
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  have hinc (k : Fin n) (hk : single k = true) : z k = true := by
    have e : k.val = pw p' := of_decide_eq_true hk
    apply decide_eq_true
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p',by simp [P],e.symm⟩)
  have listInc : List.Forall₂ (fun u v : Bool => u=true → v=true) (List.ofFn single) (List.ofFn z) := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp, ?_⟩
    intro i h₁ h₂
    have hi : i < n := by simpa using h₁
    simpa using hinc ⟨i,hi⟩
  have hb' := wires_mono C hAO.1 listInc b hb
  have accepted := hout z ⟨hpn p, contains p (by simp [P])⟩ hb'
  have small : P.card ≤ 2 := by
    simpa [P] using (Finset.card_insert_le p ({p'} : Finset (Fin N)))
  have rejected := hreject P (∅ : Finset (Fin M)) small (by simp) (by simp)
  change PEqualNP.MetaComplexity.circuitFun n C z = false at rejected
  simp [accepted] at rejected
