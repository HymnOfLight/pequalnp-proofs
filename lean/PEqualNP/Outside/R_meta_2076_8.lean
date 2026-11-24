import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

/-- In a square-free graph, independent false pairs on the two operands of a safe AND must cross on a graph edge. Separate the resulting bounded-cover invariant from the charging argument. -/
theorem PEqualNP.Outside.R_meta_2076_8
  (blockers : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, IsAO2 n C → ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j →
      ∀ b : Fin 2, ∃ (s : Fin 2) (T : Finset (Fin n)), T.card ≤ (if s = b then 8 else 80) ∧
        ∀ u v : Fin n, ¬ G.Adj u v →
          (C.wires (List.ofFn (pairInput u v))).getD (opnd C j s) false = true → u ∈ T ∨ v ∈ T)
  (charge : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
    ∀ (C : Circuit) (H : SimpleGraph (Fin n)), IsLeastAO G C → TopForm G C →
    (∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j →
      ∀ b : Fin 2, ∃ (s : Fin 2) (T : Finset (Fin n)), T.card ≤ (if s = b then 8 else 80) ∧
        ∀ u v : Fin n, ¬ G.Adj u v →
          (C.wires (List.ofFn (pairInput u v))).getD (opnd C j s) false = true → u ∈ T ∨ v ∈ T) →
    H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
    (∀ v, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
    H.edgeSet.ncard ≤ c * (C.size+1)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c,hc⟩ := charge
  refine ⟨c,?_⟩
  intro n G _ hg he C H least top hsub hdeg
  exact hc n G hg he C H least top (blockers n G hg C least.1) hsub hdeg
