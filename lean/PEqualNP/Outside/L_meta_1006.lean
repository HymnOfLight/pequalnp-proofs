import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1006

private def rowMask (i : Fin 11) : ℕ :=
  [6, 85, 35, 224, 1602, 652, 26, 1320, 1152, 48, 400].getD i.val 0

private def edge (u v : Fin 11) : Bool := (rowMask u).testBit v.val

private def graph : SimpleGraph (Fin 11) where
  Adj u v := edge u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private def graphDec : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (edge u v = true))

set_option maxRecDepth 100000 in
private theorem noFour : ∀ a b c d : Fin 11, a ≠ c → b ≠ d →
    graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬ graph.Adj d a := by
  letI : DecidableRel graph.Adj := graphDec
  decide

private theorem seven (T : Finset (Fin 11)) (a b c d e f g : Fin 11)
    (hc : ({a,b,c,d,e,f,g} : Finset (Fin 11)).card = 7)
    (ha : a ∈ T) (hb : b ∈ T) (hc' : c ∈ T) (hd : d ∈ T)
    (he : e ∈ T) (hf : f ∈ T) (hg : g ∈ T) : 7 ≤ T.card := by
  rw [← hc]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem coverLower (T : Finset (Fin 11))
    (cover : ∀ v w, graph.Adj v w → v ∈ T ∨ w ∈ T) : 7 ≤ T.card := by
  letI : DecidableRel graph.Adj := graphDec
  by_cases h1 : (1 : Fin 11) ∈ T
  · by_cases h4 : (4 : Fin 11) ∈ T
    · by_cases h2 : (2 : Fin 11) ∈ T
      · by_cases h3 : (3 : Fin 11) ∈ T
        · by_cases h5 : (5 : Fin 11) ∈ T
          · by_cases h7 : (7 : Fin 11) ∈ T
            · by_cases h8 : (8 : Fin 11) ∈ T
              · exact seven T 1 2 3 4 5 7 8 (by decide) h1 h2 h3 h4 h5 h7 h8
              · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
                exact seven T 1 2 3 4 5 7 10 (by decide) h1 h2 h3 h4 h5 h7 h10
            · have h8 : (8 : Fin 11) ∈ T := (cover 7 8 (by decide)).resolve_left h7
              have h10 : (10 : Fin 11) ∈ T := (cover 7 10 (by decide)).resolve_left h7
              exact seven T 1 2 3 4 5 8 10 (by decide) h1 h2 h3 h4 h5 h8 h10
          · have h7 : (7 : Fin 11) ∈ T := (cover 5 7 (by decide)).resolve_left h5
            have h9 : (9 : Fin 11) ∈ T := (cover 5 9 (by decide)).resolve_left h5
            by_cases h8 : (8 : Fin 11) ∈ T
            · exact seven T 1 2 3 4 7 8 9 (by decide) h1 h2 h3 h4 h7 h8 h9
            · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
              exact seven T 1 2 3 4 7 9 10 (by decide) h1 h2 h3 h4 h7 h9 h10
        · have h5 : (5 : Fin 11) ∈ T := (cover 3 5 (by decide)).resolve_left h3
          have h6 : (6 : Fin 11) ∈ T := (cover 3 6 (by decide)).resolve_left h3
          have h7 : (7 : Fin 11) ∈ T := (cover 3 7 (by decide)).resolve_left h3
          by_cases h8 : (8 : Fin 11) ∈ T
          · exact seven T 1 2 4 5 6 7 8 (by decide) h1 h2 h4 h5 h6 h7 h8
          · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
            exact seven T 1 2 4 5 6 7 10 (by decide) h1 h2 h4 h5 h6 h7 h10
      · have h0 : (0 : Fin 11) ∈ T := (cover 2 0 (by decide)).resolve_left h2
        have h5 : (5 : Fin 11) ∈ T := (cover 2 5 (by decide)).resolve_left h2
        by_cases h3 : (3 : Fin 11) ∈ T
        · by_cases h7 : (7 : Fin 11) ∈ T
          · by_cases h8 : (8 : Fin 11) ∈ T
            · exact seven T 0 1 3 4 5 7 8 (by decide) h0 h1 h3 h4 h5 h7 h8
            · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
              exact seven T 0 1 3 4 5 7 10 (by decide) h0 h1 h3 h4 h5 h7 h10
          · have h8 : (8 : Fin 11) ∈ T := (cover 7 8 (by decide)).resolve_left h7
            have h10 : (10 : Fin 11) ∈ T := (cover 7 10 (by decide)).resolve_left h7
            exact seven T 0 1 3 4 5 8 10 (by decide) h0 h1 h3 h4 h5 h8 h10
        · have h6 : (6 : Fin 11) ∈ T := (cover 3 6 (by decide)).resolve_left h3
          have h7 : (7 : Fin 11) ∈ T := (cover 3 7 (by decide)).resolve_left h3
          by_cases h8 : (8 : Fin 11) ∈ T
          · exact seven T 0 1 4 5 6 7 8 (by decide) h0 h1 h4 h5 h6 h7 h8
          · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
            exact seven T 0 1 4 5 6 7 10 (by decide) h0 h1 h4 h5 h6 h7 h10
    · have h6 : (6 : Fin 11) ∈ T := (cover 4 6 (by decide)).resolve_left h4
      have h9 : (9 : Fin 11) ∈ T := (cover 4 9 (by decide)).resolve_left h4
      have h10 : (10 : Fin 11) ∈ T := (cover 4 10 (by decide)).resolve_left h4
      by_cases h5 : (5 : Fin 11) ∈ T
      · by_cases h7 : (7 : Fin 11) ∈ T
        · by_cases h0 : (0 : Fin 11) ∈ T
          · exact seven T 0 1 5 6 7 9 10 (by decide) h0 h1 h5 h6 h7 h9 h10
          · have h2 : (2 : Fin 11) ∈ T := (cover 0 2 (by decide)).resolve_left h0
            exact seven T 1 2 5 6 7 9 10 (by decide) h1 h2 h5 h6 h7 h9 h10
        · have h3 : (3 : Fin 11) ∈ T := (cover 7 3 (by decide)).resolve_left h7
          have h8 : (8 : Fin 11) ∈ T := (cover 7 8 (by decide)).resolve_left h7
          exact seven T 1 3 5 6 8 9 10 (by decide) h1 h3 h5 h6 h8 h9 h10
      · have h2 : (2 : Fin 11) ∈ T := (cover 5 2 (by decide)).resolve_left h5
        have h3 : (3 : Fin 11) ∈ T := (cover 5 3 (by decide)).resolve_left h5
        have h7 : (7 : Fin 11) ∈ T := (cover 5 7 (by decide)).resolve_left h5
        exact seven T 1 2 3 6 7 9 10 (by decide) h1 h2 h3 h6 h7 h9 h10
  · have h0 : (0 : Fin 11) ∈ T := (cover 1 0 (by decide)).resolve_left h1
    have h2 : (2 : Fin 11) ∈ T := (cover 1 2 (by decide)).resolve_left h1
    have h4 : (4 : Fin 11) ∈ T := (cover 1 4 (by decide)).resolve_left h1
    have h6 : (6 : Fin 11) ∈ T := (cover 1 6 (by decide)).resolve_left h1
    by_cases h5 : (5 : Fin 11) ∈ T
    · by_cases h7 : (7 : Fin 11) ∈ T
      · by_cases h8 : (8 : Fin 11) ∈ T
        · exact seven T 0 2 4 5 6 7 8 (by decide) h0 h2 h4 h5 h6 h7 h8
        · have h10 : (10 : Fin 11) ∈ T := (cover 8 10 (by decide)).resolve_left h8
          exact seven T 0 2 4 5 6 7 10 (by decide) h0 h2 h4 h5 h6 h7 h10
      · have h3 : (3 : Fin 11) ∈ T := (cover 7 3 (by decide)).resolve_left h7
        have h8 : (8 : Fin 11) ∈ T := (cover 7 8 (by decide)).resolve_left h7
        have h10 : (10 : Fin 11) ∈ T := (cover 7 10 (by decide)).resolve_left h7
        exact seven T 0 2 3 4 5 6 8 (by decide) h0 h2 h3 h4 h5 h6 h8
    · have h3 : (3 : Fin 11) ∈ T := (cover 5 3 (by decide)).resolve_left h5
      have h7 : (7 : Fin 11) ∈ T := (cover 5 7 (by decide)).resolve_left h5
      have h9 : (9 : Fin 11) ∈ T := (cover 5 9 (by decide)).resolve_left h5
      exact seven T 0 2 3 4 6 7 9 (by decide) h0 h2 h3 h4 h6 h7 h9

private def circuit : PEqualNP.AndCount.AndCountCircuit 11 where
  size := 6
  leftVars := ![{5, 6}, {0}, {8}, {9}, {7}, {1}]
  leftGates := ![∅, {0}, {0}, ∅, {0}, {0}]
  rightVars := ![{3, 4}, {1, 2}, {7, 10}, {4, 5}, {3, 10}, {2, 6}]
  rightGates := ![∅, ∅, ∅, {0}, ∅, ∅]
  outVars := ∅
  outGates := {1, 2, 3, 4, 5}

private theorem circuitWF : circuit.WellFormed := by
  unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
  decide

private def mis1006 : Finset (Finset (Fin 11)) :=
  {{0,4,7},
    {2,4,7},
    {0,3,4,8},
    {2,3,4,8},
    {1,5,8},
    {0,4,5,8},
    {0,5,6,8},
    {1,7,9},
    {0,6,7,9},
    {2,6,7,9},
    {0,3,8,9},
    {1,3,8,9},
    {2,3,8,9},
    {0,6,8,9},
    {2,6,8,9},
    {1,5,10},
    {0,5,6,10},
    {0,3,9,10},
    {1,3,9,10},
    {2,3,9,10},
    {0,6,9,10},
    {2,6,9,10}}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem allMIS : ∀ I : Finset (Fin 11),
    (∀ v ∈ I, ∀ w ∈ I, ¬ graph.Adj v w) →
    (∀ u, u ∉ I → ∃ v ∈ I, graph.Adj u v) → I ∈ mis1006 := by
  letI : DecidableRel graph.Adj := graphDec
  decide

private theorem testsOnMIS (I : Finset (Fin 11)) (hm : I ∈ mis1006) :
    circuit.eval I = false ∧ ∀ u, u ∉ I → circuit.eval (insert u I) = true := by
  simp only [mis1006,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst I <;> decide

end PEqualNP.Outside.L_meta_1006

theorem PEqualNP.Outside.L_meta_1006 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    (∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧
      ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → C.size ≤ T.card) ∧
    (∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ∃ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) ∧ T.card ≤ C.size)) := by
  intro claim
  obtain ⟨T, hT, hsmall⟩ := (claim 11 PEqualNP.Outside.L_meta_1006.graph
    PEqualNP.Outside.L_meta_1006.noFour).2 PEqualNP.Outside.L_meta_1006.circuit
    PEqualNP.Outside.L_meta_1006.circuitWF (fun I hi hm =>
      PEqualNP.Outside.L_meta_1006.testsOnMIS I (PEqualNP.Outside.L_meta_1006.allMIS I hi hm))
  have hlower := PEqualNP.Outside.L_meta_1006.coverLower T hT
  change T.card ≤ 6 at hsmall
  omega
