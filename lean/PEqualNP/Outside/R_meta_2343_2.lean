import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A free OR on at most two raw inputs can be studied on four genuine two-input pairs. -/
theorem PEqualNP.Outside.R_meta_2343_2
  (genuine : let rb := fun (C : Circuit) => ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27+i.val
    ∀ (C : Circuit) (s : List ℕ), s.length≤2 → Monotone2 C → rb C →
      ∃ (B : Circuit) (t : Fin 26 × Fin 26), t.1≠t.2 ∧ B.size≤C.size ∧ Monotone2 B ∧ rb B ∧
        ∀ x : List Bool, x.length=26 → B.eval (x++[x.getD t.1.val false || x.getD t.2.val false]) =
          C.eval (x++[s.any (fun w => x.getD w false)]))
  (transport : let rb := fun (C : Circuit) => ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27+i.val
    let fits (C : Circuit) (t : Fin 26 × Fin 26) := 
      let K : Finset (Fin 13) := {0,1,3,9}
      let ext (x : List Bool) := x ++ [x.getD t.1.val false || x.getD t.2.val false]
      (∀ p l : Fin 13, p-l∈K → C.eval (ext ((List.ofFn (fun i : Fin 13 => decide (i=p))) ++
        (List.ofFn (fun i : Fin 13 => decide (i=l))))) = true) ∧
      ∀ Q : Finset (Fin 13), Q.card=4 → (∀ l : Fin 13, (Q.filter (fun p => p-l∈K)).card ≤ 2) →
        C.eval (ext ((List.ofFn (fun i : Fin 13 => decide (i∈Q))) ++
          (List.ofFn (fun i : Fin 13 => decide (∀ p∈Q, p-i∉K))))) = false
    ∀ (C : Circuit) (s : Fin 26 × Fin 26), s.1≠s.2 → Monotone2 C → rb C → fits C s →
      ∃ (B : Circuit), ∃ t ∈ ([(0,1),(13,14),(0,13),(0,14)] : List (Fin 26 × Fin 26)), B.size≤C.size ∧ Monotone2 B ∧ rb B ∧ fits B t)
  (fixed : let rb := fun (C : Circuit) => ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27+i.val
    let fits (C : Circuit) (t : Fin 26 × Fin 26) := 
      let K : Finset (Fin 13) := {0,1,3,9}
      let ext (x : List Bool) := x ++ [x.getD t.1.val false || x.getD t.2.val false]
      (∀ p l : Fin 13, p-l∈K → C.eval (ext ((List.ofFn (fun i : Fin 13 => decide (i=p))) ++
        (List.ofFn (fun i : Fin 13 => decide (i=l))))) = true) ∧
      ∀ Q : Finset (Fin 13), Q.card=4 → (∀ l : Fin 13, (Q.filter (fun p => p-l∈K)).card ≤ 2) →
        C.eval (ext ((List.ofFn (fun i : Fin 13 => decide (i∈Q))) ++
          (List.ofFn (fun i : Fin 13 => decide (∀ p∈Q, p-i∉K))))) = false
    ∀ (C : Circuit), ∀ t ∈ ([(0,1),(13,14),(0,13),(0,14)] : List (Fin 26 × Fin 26)), Monotone2 C → rb C → fits C t → 63≤C.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C s hs hm hb
  dsimp only
  intro hp hn
  obtain ⟨B,t,ht,hs0,hm0,hb0,hfun⟩ := genuine C s hs hm hb
  obtain ⟨A,u,hu,hs1,hm1,hb1,hfit⟩ := transport B t ht hm0 hb0 (by
    constructor
    · intro p l hpl
      exact (hfun _ (by simp)).trans (hp p l hpl)
    · intro Q hQ hcap
      exact (hfun _ (by simp)).trans (hn Q ⟨hQ,hcap⟩))
  exact (fixed A u hu hm1 hb1 hfit).trans (hs1.trans hs0)
