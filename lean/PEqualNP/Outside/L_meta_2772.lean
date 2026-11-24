import PEqualNP.Defs
import Mathlib.Data.List.Forall2

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def rewritten (C : Circuit) (g b w' : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨(gateAt C g).op, (gateAt C g).inputs.set b w'⟩, C.output⟩

/-- Changing one operand preserves both the binary basis and the topological order. -/
private theorem rewrite_model {n : ℕ} (C : Circuit) (g b w' : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length) (hw' : w' < n+g) :
    PEqualNP.TopForm.IsAO2 n (rewritten C g b w') := by
  have hm : gateAt C g ∈ C.gates := by
    rw [gateAt,List.getD_eq_getElem _ _ hg]
    exact List.getElem_mem ..
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain h | rfl := List.mem_or_eq_of_mem_set hz
    · exact hAO.1 z h
    · exact hAO.1 (gateAt C g) hm
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [rewritten] using hj
    by_cases h : g=j
    · subst j
      have hs : i ∈ (gateAt C g).inputs.set b w' := by
        simpa only [gateAt,rewritten,List.getD_eq_getElem?_getD,List.getElem?_set_self hg,
          Option.getD_some] using hi
      rcases List.mem_or_eq_of_mem_set hs with ho | rfl
      · exact hAO.2.1 g hg i ho
      · exact hw'
    · apply hAO.2.1 j hj' i
      simpa only [gateAt,rewritten,List.getD_eq_getElem?_getD,List.getElem?_set_ne h] using hi
  · intro z hz
    obtain h | rfl := List.mem_or_eq_of_mem_set hz
    · exact hAO.2.2 z h
    · exact (List.length_set ..).trans (hAO.2.2 _ hm)


private abbrev Inc (a b : Bool) := a=true → b=true

private def evalStep (a : List Bool) (g : Gate) :=
  a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]

private theorem wireRefl (u : List Bool) : List.Forall₂ Inc u u := by
  induction u with
  | nil => exact .nil
  | cons a as ih => exact .cons (fun h => h) ih

private theorem readInc {a b : List Bool} (h : List.Forall₂ Inc a b) (i : ℕ) :
    Inc (a.getD i false) (b.getD i false) := by
  induction h generalizing i with
  | nil => exact fun e => e
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

private theorem opInc {a b : List Bool} (o : GateOp) (ho : o=.and ∨ o=.or)
    (h : List.Forall₂ Inc a b) : Inc (o.eval a) (o.eval b) := by
  rcases ho with rfl|rfl
  · induction h with
    | nil => exact fun e => e
    | cons ha _ ih => simpa [Inc,GateOp.eval,List.all_cons] using
        (fun e : _ ∧ _ => And.intro (ha e.1) (ih e.2))
  · induction h with
    | nil => exact fun e => e
    | cons ha _ ih => simpa [Inc,GateOp.eval,List.any_cons] using
        (fun e : _ ∨ _ => e.imp ha ih)

private theorem setInc (u : List Bool) (i : ℕ) {a b : Bool} (hab : Inc a b) :
    List.Forall₂ Inc (u.set i a) (u.set i b) := by
  induction u generalizing i with
  | nil => exact .nil
  | cons h t ih => cases i with
    | zero => exact .cons hab (wireRefl t)
    | succ i => exact .cons (fun e => e) (ih i)

private theorem tailInc (gs : List Gate) (hgs : ∀ g∈gs,g.op=.and ∨ g.op=.or)
    (u z : List Bool) (h : List.Forall₂ Inc u z) :
    List.Forall₂ Inc (gs.foldl evalStep u) (gs.foldl evalStep z) := by
  induction gs generalizing u z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun v hv => hgs v (by simp [hv]))
    apply List.rel_append h
    apply List.Forall₂.cons _ .nil
    apply opInc g.op (hgs _ (by simp))
    induction g.inputs with
    | nil => exact .nil
    | cons i is ih => exact .cons (readInc h i) ih

private theorem runLength (gs : List Gate) (u : List Bool) :
    (gs.foldl evalStep u).length = u.length + gs.length := by
  induction gs generalizing u with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp [evalStep]; omega

private theorem savedRead (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i<u.length) :
    (gs.foldl evalStep u).getD i false = u.getD i false := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,ih _ (by simp [evalStep]; omega),evalStep,List.getD_append _ _ _ _ hi]

private theorem rewrite_fun {n : ℕ} (C : Circuit) (g b w w' : ℕ)
    (ao : PEqualNP.TopForm.IsAO2 n C) (hg : g<C.gates.length) (hb : b<2)
    (hw : (gateAt C g).inputs.getD b 0=w) (hw' : w'<n+g)
    (low : ∀ x : Fin n→Bool, (⟨C.gates,w⟩ : Circuit).eval (List.ofFn x)=true →
       (⟨C.gates,w'⟩ : Circuit).eval (List.ofFn x)=true)
    (high : ∀ x : Fin n→Bool, (⟨C.gates,w'⟩ : Circuit).eval (List.ofFn x)=true →
       circuitFun n C x=true) : circuitFun n (rewritten C g b w') = circuitFun n C := by
  funext x
  let gate := gateAt C g
  let tail := C.gates.drop (g+1)
  let pre := (C.gates.take g).foldl evalStep (List.ofFn x)
  let val := fun i => pre.getD i false
  -- Remaining computation with a chosen Boolean value in the edited operand slot.
  let ctx := fun a => (tail.foldl evalStep (pre ++ [gate.op.eval ((gate.inputs.map val).set b a)])).getD C.output false
  have gateEq : gate = C.gates[g] := List.getD_eq_getElem _ _ hg
  have gateMem : gate ∈ C.gates := gateEq ▸ List.getElem_mem _
  have blt : b < gate.inputs.length := by rw [ao.2.2 gate gateMem]; exact hb
  have pos : gate.inputs[b] = w := (List.getD_eq_getElem _ _ blt).symm.trans hw
  have fac : C.gates.take g ++ gate :: tail = C.gates := by
    rw [gateEq,List.getElem_cons_drop hg,List.take_append_drop]
  have len : pre.length=n+g := by simp [pre,runLength,List.length_take,Nat.min_eq_left (Nat.le_of_lt hg)]
  -- Every wire read by the edited gate already has its final value.
  have hold (i : ℕ) (hi : i<n+g) :
      (⟨C.gates,i⟩ : Circuit).eval (List.ofFn x)=val i := by
    change (C.gates.foldl evalStep (List.ofFn x)).getD i false = pre.getD i false
    conv_lhs => rw [← fac,List.foldl_append]
    exact savedRead _ pre i (len ▸ hi)
  have oldpos : w<n+g := ao.2.1 g hg w (pos ▸ List.getElem_mem _)
  have old : circuitFun n C x=ctx (val w) := by
    change (C.gates.foldl evalStep (List.ofFn x)).getD C.output false=_
    conv_lhs => rw [← fac,List.foldl_append,List.foldl_cons]
    have et : (gate.inputs.map val)[b]'(by simpa using blt)=val w := by rw [List.getElem_map,pos]
    simp only [ctx,← et,List.set_getElem_self]
    rfl
  have new : circuitFun n (rewritten C g b w') x=ctx (val w') := by
    change ((C.gates.set g ⟨gate.op,gate.inputs.set b w'⟩).foldl evalStep (List.ofFn x)).getD C.output false=_
    rw [List.set_eq_take_append_cons_drop,ite_eq_left hg,List.foldl_append,List.foldl_cons]
    simp only [ctx,evalStep, List.map_set]
    rfl
  have mono {a z : Bool} (h : Inc a z) : Inc (ctx a) (ctx z) := by
    apply readInc
    apply tailInc
    · intro k hk
      exact ao.1 _ (List.mem_of_mem_drop hk)
    · exact List.rel_append (wireRefl pre)
        (.cons (opInc gate.op (ao.1 gate gateMem) (setInc (gate.inputs.map val) b h)) .nil)
  have lo : Inc (val w) (val w') := by simpa only [hold w oldpos,hold w' hw'] using low x
  have hi : Inc (val w') (ctx (val w)) := by simpa only [hold w' hw',old] using high x
  rw [old,new]
  -- If the two values differ, the new one is true and already forces the old output.
  by_cases he : val w=val w'
  · rw [he]
  · have htrue : val w'=true := by cases h : val w' with
      | true => rfl
      | false => cases h' : val w with
        | false => exact (he (h'.trans h.symm)).elim
        | true => exact (Bool.noConfusion (h.symm.trans (lo h')))
    exact (mono lo (hi htrue)).trans (hi htrue).symm

end PEqualNP.Outside.L_meta_2772

open PEqualNP.Outside.L_meta_2772

theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' h
  obtain ⟨ao, _, hg, hb, hw, hw', low, high⟩ := h
  exact ⟨rewrite_model C g b w' ao hg hw', rewrite_fun C g b w w' ao hg hb hw hw' low high,
    List.length_set ..⟩
