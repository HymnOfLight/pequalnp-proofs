import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds

def reads885 {n : ℕ} (L : List Gate) (j : Fin L.length) (x : Fin n → Bool) : Bool :=
  ((L.get j).inputs.map (fun i => (Circuit.wires ⟨L.take j.val, 0⟩
    (List.ofFn x)).getD i false)).headD false

def applyWire885 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Evaluate the input to each NOT at the chosen base and replace the gate with a constant.
def freezeGate885 (g : Gate) (w : List Bool) : Gate :=
  match g.op with
  | .not => if (g.inputs.map (fun i => w.getD i false)).headD false
      then ⟨.or, []⟩ else ⟨.and, []⟩
  | _ => g

def freezeList885 : List Gate → List Bool → List Gate
  | [], _ => []
  | g :: gs, w => freezeGate885 g w :: freezeList885 gs (applyWire885 w g)

theorem freeze_len885 (L : List Gate) (w : List Bool) :
    (freezeList885 L w).length = L.length := by
  induction L generalizing w <;> simp_all [freezeList885]

theorem freeze_ok885 (L : List Gate) (w : List Bool)
    (hops : ∀ g ∈ L, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ freezeList885 L w, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  induction L generalizing w with
  | nil => simp [freezeList885]
  | cons g gs ih =>
    intro v hv
    rcases List.mem_cons.mp hv with h | h
    · subst v
      rcases hops g (by simp) with ⟨h1 | h1 | h1, h2⟩
      · simpa [freezeGate885, h1] using h2
      · simpa [freezeGate885, h1] using h2
      · simp only [freezeGate885, h1]
        split <;> simp
    · exact ih (applyWire885 w g) (fun u hu => hops u (by simp [hu])) v h

theorem freeze_eq885 (L : List Gate) (w z : List Bool)
    (h : ∀ j : Fin L.length, (L.get j).op = .not →
       ((L.get j).inputs.map (fun i => ((L.take j.val).foldl applyWire885 z).getD i false)).headD false =
       ((L.get j).inputs.map (fun i => ((L.take j.val).foldl applyWire885 w).getD i false)).headD false) :
    (freezeList885 L w).foldl applyWire885 z = L.foldl applyWire885 z := by
  induction L generalizing w z with
  | nil => rfl
  | cons g gs ih =>
    have head_imp : g.op = .not →
        (g.inputs.map (fun i => z.getD i false)).headD false =
        (g.inputs.map (fun i => w.getD i false)).headD false := by
      simpa using h ⟨0, by simp⟩
    have he : applyWire885 z (freezeGate885 g w) = applyWire885 z g := by
      cases g with
      | mk op ins =>
        cases op <;> simp only [freezeGate885]
        have hv := head_imp rfl
        simp only at hv
        cases hread : (ins.map (fun i => w.getD i false)).headD false <;>
          simp [applyWire885, GateOp.eval] <;> simpa using hv.trans hread
    simp only [freezeList885, List.foldl_cons, he]
    apply ih
    intro j hj
    have H := h ⟨j.val+1, by simp⟩
    simpa [List.get_eq_getElem] using H hj

theorem replaceStable885 (n : ℕ) (L : List Gate) (W : (Fin n → Bool) → Prop)
    (a : Fin n → Bool)
    (hops : ∀ g ∈ L, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hstable : ∀ x, W x → ∀ j : Fin L.length, (L.get j).op = .not →
       reads885 L j x = reads885 L j a) :
    ∃ M : List Gate, M.length = L.length ∧
      (∀ g ∈ M, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x, W x → Circuit.wires ⟨M, 0⟩ (List.ofFn x) =
        Circuit.wires ⟨L, 0⟩ (List.ofFn x) := by
  refine ⟨freezeList885 L (List.ofFn a), freeze_len885 _ _, freeze_ok885 _ _ hops, ?_⟩
  intro x hx
  exact freeze_eq885 L (List.ofFn a) (List.ofFn x) (hstable x hx)

-- Each unstable small extension permanently switches at least one previously false read.
theorem greedy885 {n r t k : ℕ} (h : Fin r → Finset (Fin n) → Bool)
    (hm : ∀ i, Monotone (h i)) (hrt : r ≤ t) (ht : 1 ≤ t) (_hk : 1 ≤ k) :
    ∃ B : Finset (Fin n),
      (B.card ≤ (t-1)*k ∧ ∀ X : Finset (Fin n), X.card ≤ k → ∀ i, h i (B ∪ X) = h i B) ∨
      (B.card ≤ t*k ∧ ∀ X : Finset (Fin n), ∀ i, h i (B ∪ X) = h i B) := by
  classical
  let inactive (B : Finset (Fin n)) : Finset (Fin r) :=
    Finset.univ.filter (fun i => h i B = false)
  have anti {B D : Finset (Fin n)} (hBD : B ⊆ D) : inactive D ⊆ inactive B := by
    intro i hi
    simp only [inactive, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hi' := hm i hBD
    rw [hi] at hi'
    exact le_antisymm hi' (Bool.false_le _)
  have grow (s : ℕ) (hs : s ≤ t) (B : Finset (Fin n))
      (hB : B.card ≤ (t-s)*k) (hI : (inactive B).card ≤ s) :
      ∃ D : Finset (Fin n),
        (D.card ≤ (t-1)*k ∧ ∀ X : Finset (Fin n), X.card ≤ k → ∀ i, h i (D ∪ X) = h i D) ∨
        (D.card ≤ t*k ∧ ∀ X : Finset (Fin n), ∀ i, h i (D ∪ X) = h i D) := by
    induction s generalizing B with
    | zero =>
      refine ⟨B, Or.inr ⟨by simpa using hB, ?_⟩⟩
      have he : inactive B = ∅ := Finset.card_eq_zero.mp (by omega)
      intro X i
      have hon : h i B = true := by
        by_contra hh
        have hi : i ∈ inactive B := by simp [inactive, Bool.eq_false_iff.mpr hh]
        simp [he] at hi
      have hle := hm i (Finset.subset_union_left (s₂ := X) : B ⊆ B ∪ X)
      rw [hon] at hle ⊢
      exact le_antisymm (Bool.le_true _) hle
    | succ s ih =>
      by_cases stable : ∀ X : Finset (Fin n), X.card ≤ k → ∀ i, h i (B ∪ X) = h i B
      · refine ⟨B, Or.inl ⟨?_, stable⟩⟩
        exact hB.trans (Nat.mul_le_mul_right k (by omega))
      · push Not at stable
        obtain ⟨X, hX, i, hdiff⟩ := stable
        have hsub : B ⊆ B ∪ X := Finset.subset_union_left
        have hle := hm i hsub
        have h0 : h i B = false := by
          apply Bool.eq_false_iff.mpr
          intro hb
          rw [hb] at hle
          exact hdiff ((le_antisymm (Bool.le_true _) hle).trans hb.symm)
        have h1 : h i (B ∪ X) = true := by
          cases hb : h i (B ∪ X) with
          | false => exact (hdiff (hb.trans h0.symm)).elim
          | true => rfl
        have hstrict : inactive (B ∪ X) ⊂ inactive B := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨anti hsub, ?_⟩
          intro he
          have hi : i ∈ inactive B := by simp [inactive, h0]
          rw [← he] at hi
          simp [inactive, h1] at hi
        have hless := Finset.card_lt_card hstrict
        apply ih (by omega) (B ∪ X) _ (by omega)
        calc
          (B ∪ X).card ≤ B.card + X.card := Finset.card_union_le _ _
          _ ≤ (t-(s+1))*k + k := Nat.add_le_add hB hX
          _ = (t-s)*k := by
            have he : t - s = (t-(s+1))+1 := by omega
            rw [he, Nat.add_mul, Nat.one_mul]
  apply grow t le_rfl ∅ (by simp)
  exact (Finset.card_le_univ _).trans (by simpa using hrt)

theorem window885 {n t k : ℕ} (L : List Gate)
    (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hnot : Set.ncard {j : Fin L.length | (L.get j).op = GateOp.not} ≤ t)
    (hmono : ∀ (j : ℕ) (g : Gate), L[j]? = some g → g.op = GateOp.not →
      Monotone (fun x : Fin n → Bool =>
        (g.inputs.map (fun a => (Circuit.wires ⟨L.take j, 0⟩ (List.ofFn x)).getD a false)).headD false)) :
    ∃ B : Finset (Fin n),
      (B.card ≤ (t - 1) * k ∧ ∀ X : Finset (Fin n), X.card ≤ k →
        ∀ j : Fin L.length, (L.get j).op = GateOp.not →
          reads885 L j (fun p => decide (p ∈ B ∪ X)) =
            reads885 L j (fun p => decide (p ∈ B))) ∨
      (B.card ≤ t * k ∧ ∀ X : Finset (Fin n),
        ∀ j : Fin L.length, (L.get j).op = GateOp.not →
          reads885 L j (fun p => decide (p ∈ B ∪ X)) =
            reads885 L j (fun p => decide (p ∈ B))) := by
  classical
  let N : Set (Fin L.length) := {j | (L.get j).op = GateOp.not}
  let e := Fintype.equivFin N
  let h (i : Fin (Fintype.card N)) (A : Finset (Fin n)) :=
    reads885 L (e.symm i).val (fun p => decide (p ∈ A))
  have hr : Fintype.card N ≤ t := by
    rw [← Nat.card_eq_fintype_card]
    exact hnot
  have hm (i : Fin (Fintype.card N)) : Monotone (h i) := by
    let j := (e.symm i).val
    have hop : (L.get j).op = GateOp.not := (e.symm i).property
    have hj : L[j.val]? = some (L.get j) := List.getElem?_eq_getElem j.isLt
    have hjm : Monotone (reads885 (n := n) L j) := hmono j.val (L.get j) hj hop
    intro A B hAB
    apply hjm
    intro p
    apply Bool.le_iff_imp.mpr
    simpa only [decide_eq_true_eq] using (show p ∈ A → p ∈ B from fun hp => hAB hp)
  obtain ⟨B, small | large⟩ := greedy885 h hm hr ht hk
  · refine ⟨B, Or.inl ?_⟩
    refine ⟨small.1, ?_⟩
    intro X hX j hj
    let z : N := ⟨j, hj⟩
    simpa only [h, Equiv.symm_apply_apply] using small.2 X hX (e z)
  · refine ⟨B, Or.inr ?_⟩
    refine ⟨large.1, ?_⟩
    intro X j hj
    let z : N := ⟨j, hj⟩
    simpa only [h, Equiv.symm_apply_apply] using large.2 X (e z)

-- After the first point, each additional point meets at most q previously uncounted lines.
theorem lines_hit {P I : Type*} [DecidableEq P] [DecidableEq I]
    (A : P → Finset I) (q : ℕ) (degree : ∀ p, (A p).card = q + 1)
    (meet : ∀ p r, p ≠ r → ∃ i, i ∈ A p ∧ i ∈ A r)
    (Y : Finset P) : (Y.biUnion A).card ≤ Y.card * q + 1 := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert x Y hx ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hx, Nat.add_mul, Nat.one_mul]
    by_cases hY : Y.Nonempty
    · obtain ⟨r, hr⟩ := hY
      have hxr : x ≠ r := fun heq => hx (heq ▸ hr)
      obtain ⟨i, hi, hi'⟩ := meet x r hxr
      have hh : 0 < (A x ∩ Y.biUnion A).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_biUnion.mpr ⟨r, hr, hi'⟩⟩⟩
      have hu := Finset.card_union_add_card_inter (A x) (Y.biUnion A)
      rw [degree] at hu
      omega
    · have he : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
      simp [he, degree]

theorem surviving_lines {P I : Type*} [DecidableEq P] [DecidableEq I] [Fintype I]
    (A : P → Finset I) (q : ℕ) (degree : ∀ p, (A p).card = q + 1)
    (meet : ∀ p r, p ≠ r → ∃ i, i ∈ A p ∧ i ∈ A r)
    (Y : Finset P) :
    Fintype.card I ≤ ((Finset.univ : Finset I) \ Y.biUnion A).card + (Y.card * q + 1) := by
  have hh := lines_hit A q degree meet Y
  have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Y.biUnion A))
  rw [Finset.card_univ] at hpart
  omega

theorem early_arith (K k q m r t y : ℕ) (ht : 1 ≤ t)
    (hy : y ≤ (t - 1) * k) (hm : m ≤ r + (y*q+1))
    (hg : K + k*(t*k*q+1) ≤ k*m + k*k*q)
    (hq : K + q*(t*k*q+1) ≤ q*m + q*k*q) :
    K ≤ min k q * r := by
  have hid : t = (t-1)+1 := by omega
  have he : t*k*q = (t-1)*k*q+k*q := by
    conv_lhs => rw [hid]
    rw [Nat.add_mul,Nat.one_mul,Nat.add_mul]
  have hm' : m ≤ r + ((t-1)*k*q+1) := by
    have h := Nat.mul_le_mul_right q hy
    omega
  rw [he] at hg hq
  by_cases h : k ≤ q
  · rw [Nat.min_eq_left h]
    have hm'' := Nat.mul_le_mul_left k hm'
    simp only [Nat.mul_add,Nat.mul_one,← Nat.mul_assoc] at hg hm''
    omega
  · rw [Nat.min_eq_right (by omega : q ≤ k)]
    have hm'' := Nat.mul_le_mul_left q hm'
    simp only [Nat.mul_add,Nat.mul_one,← Nat.mul_assoc] at hq hm''
    omega

theorem late_arith (K q m r t k y : ℕ) (hy : y ≤ t*k)
    (hm : m ≤ r + (y*q+1)) (hg : K + q*(t*k*q+1) ≤ q*m) :
    K ≤ q*r := by
  have h := Nat.mul_le_mul_right q hy
  have h' : m ≤ r + (t*k*q+1) := by omega
  have h'' := Nat.mul_le_mul_left q h'
  rw [Nat.mul_add] at h''
  omega



theorem surviving_fam {n m q : ℕ} (Fam : Fin m → Finset (Fin n))
    (meet : ∀ p r : Fin n, p ≠ r → ∃ i, p ∈ Fam i ∧ r ∈ Fam i)
    (deg : ∀ p : Fin n, (Finset.univ.filter (fun i => p ∈ Fam i)).card = q+1)
    (Y : Finset (Fin n)) :
    m ≤ (Finset.univ.filter (fun i => Disjoint (Fam i) Y)).card + (Y.card*q+1) := by
  classical
  let A (p : Fin n) := Finset.univ.filter (fun i => p ∈ Fam i)
  have hmeet p r (hn : p ≠ r) : ∃ i, i ∈ A p ∧ i ∈ A r := by
    obtain ⟨i,hi,hr⟩ := meet p r hn
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  have h := surviving_lines A q deg hmeet Y
  have eq : (Finset.univ : Finset (Fin m)) \ Y.biUnion A =
      Finset.univ.filter (fun i => Disjoint (Fam i) Y) := by
    ext i
    simp [A, Finset.disjoint_left]
    aesop
  simpa [eq] using h

theorem early_window_arith {K k q m r t y : ℕ} (ht : 1 ≤ t)
    (hy : y ≤ (t-1)*k) (hm : m ≤ r + (y*q+1))
    (hempty : y = 0 → r = m)
    (hb : (t = 1 ∧ K ≤ k*m ∧ K ≤ q*m) ∨
      (K + k*(t*k*q+1) ≤ k*m + k*k*q ∧ K + q*(t*k*q+1) ≤ q*m + q*k*q)) :
    K ≤ min k q * r := by
  rcases hb with ⟨rfl,hk,hq⟩ | ⟨hk,hq⟩
  · simp at hy
    rw [hempty hy]
    by_cases h : k ≤ q
    · simpa [Nat.min_eq_left h] using hk
    · simpa [Nat.min_eq_right (by omega : q ≤ k)] using hq
  · exact early_arith K k q m r t y ht hy hm hk hq

theorem empty_live {n m : ℕ} (Fam : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hy : Y.card = 0) : (Finset.univ.filter (fun i => Disjoint (Fam i) Y)).card = m := by
  have he := Finset.card_eq_zero.mp hy
  simp [he]

private abbrev Count885 : Prop := (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size)

private abbrev Prop885 : Prop := (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))

private theorem localCount (hc : Count885) (hp : Prop885)
    {n m q k : ℕ} (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (L : List Gate) (B : Finset (Fin n))
    (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hcard : ∀ i, (S i).card = q + 1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsem : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k →
      Circuit.eval ⟨L, o i⟩ (List.ofFn (fun p => if p ∈ B then true else x p)) =
        decide (∃ v ∈ S i, x v = true)) :
    m * min k q ≤ L.length := by
  classical
  obtain ⟨M, r, hMG, hML, hr⟩ := hp n L B ∅ hgate
  have hzero : (Finset.univ.filter (fun _ : Fin n => false = true)).card ≤ k := by simp
  have hsingle (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ k := by
    have hs : Finset.univ.filter (fun q : Fin n => decide (q = p) = true) = {p} := by
      ext a
      simp
    rw [hs, Finset.card_singleton]
    exact hk
  have hnon (i : Fin m) :
      ∃ x y : Fin n → Bool,
        Circuit.eval ⟨L, o i⟩ (List.ofFn (fun p => if p ∈ B then true else if p ∈ (∅ : Finset (Fin n)) then false else x p)) ≠
        Circuit.eval ⟨L, o i⟩ (List.ofFn (fun p => if p ∈ B then true else if p ∈ (∅ : Finset (Fin n)) then false else y p)) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (S i).card by rw [hcard]; omega)
    refine ⟨fun _ => false, fun z => decide (z = p), ?_⟩
    simp only [Finset.notMem_empty, ite_false]
    rw [hsem i _ hzero, hsem i _ (hsingle p)]
    simp [hp]
  have hMeval (i : Fin m) (x : Fin n → Bool)
      (hx : (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k) :
      Circuit.eval ⟨M, r (o i)⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true) := by
    simpa using (hr (o i) (hnon i) x).trans (by simpa using hsem i x hx)
  have hsetw (i : Fin m) (p : Fin n) :
      (Circuit.wires ⟨M, 0⟩ (List.ofFn (fun v : Fin n => decide (v = p)))).getD (r (o i)) false = true ↔ p ∈ S i := by
    change Circuit.eval ⟨M, r (o i)⟩ _ = true ↔ _
    rw [hMeval i _ (hsingle p)]
    simp
  have hoff (i : Fin m) (x : Fin n → Bool)
      (hx : (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ k)
      (hd : ∀ v ∈ S i, x v = false) :
      (Circuit.wires ⟨M, 0⟩ (List.ofFn x)).getD (r (o i)) false = false := by
    change Circuit.eval ⟨M, r (o i)⟩ _ = false
    rw [hMeval i x hx]
    simpa using hd
  have hfin := hc n m k S ⟨M,0⟩ (fun i => r (o i)) (fun _ => min k q)
    hcross (fun i => by rw [hcard]; omega) hMG hsetw hoff (fun _ => min_le_left _ _)
    (fun i => by rw [hcard]; omega)
  simpa [Circuit.size] using hfin.trans hML


-- Restrict the line family to the lines disjoint from the base before applying the count.
theorem countOnBase885 (hc : Count885) (hp : Prop885)
    {n m q k : ℕ} (Fam : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (M : List Gate) (B : Finset (Fin n))
    (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hcard : ∀ i, (Fam i).card = q + 1)
    (hcross : ∀ i j, i ≠ j → (Fam i ∩ Fam j).card ≤ 1)
    (hgate : ∀ g ∈ M, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsem : ∀ (i : Fin m) (X : Finset (Fin n)), X.card ≤ k →
      Circuit.eval ⟨M, o i⟩ (List.ofFn (fun p => decide (p ∈ B ∪ X))) =
        decide (∃ v ∈ Fam i, v ∈ B ∪ X)) :
    (Finset.univ.filter (fun i => Disjoint (Fam i) B)).card * min k q ≤ M.length := by
  classical
  let G := Finset.univ.filter (fun i => Disjoint (Fam i) B)
  let e := G.orderEmbOfFin rfl
  apply localCount hc hp (fun i => Fam (e i)) (fun i => o (e i)) M B hq hk
    (fun i => hcard (e i)) (fun i j hij => hcross _ _ (e.injective.ne hij)) hgate
  intro i x hx
  let X := Finset.univ.filter (fun p : Fin n => x p = true)
  have hd : Disjoint (Fam (e i)) B := (Finset.mem_filter.mp (G.orderEmbOfFin_mem rfl i)).2
  have heq : (fun p => if p ∈ B then true else x p) = (fun p => decide (p ∈ B ∪ X)) := by
    funext p
    by_cases h : p ∈ B <;> simp [h, X]
  rw [heq, hsem (e i) X hx]
  congr 1
  apply propext
  constructor
  · rintro ⟨p, hpi, hb⟩
    rcases Finset.mem_union.mp hb with hb | hx'
    · exact (Finset.disjoint_left.mp hd hpi hb).elim
    · exact ⟨p, hpi, (Finset.mem_filter.mp hx').2⟩
  · rintro ⟨p, hpi, hx'⟩
    exact ⟨p,hpi,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩)⟩

theorem countFromStable885 (hc : Count885) (hp : Prop885)
    {n m q k : ℕ} (Fam : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (L : List Gate) (B : Finset (Fin n))
    (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hcard : ∀ i, (Fam i).card = q + 1)
    (hcross : ∀ i j, i ≠ j → (Fam i ∩ Fam j).card ≤ 1)
    (hgate : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (horig : ∀ (i : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨L, o i⟩ (List.ofFn x) = decide (∃ v ∈ Fam i, x v = true))
    (hst : ∀ (X : Finset (Fin n)), X.card ≤ k → ∀ j : Fin L.length,
      (L.get j).op = GateOp.not →
      reads885 L j (fun p => decide (p ∈ B ∪ X)) = reads885 L j (fun p => decide (p ∈ B))) :
    (Finset.univ.filter (fun i => Disjoint (Fam i) B)).card * min k q ≤ L.length := by
  classical
  let W : (Fin n → Bool) → Prop := fun x => ∃ X : Finset (Fin n),
    X.card ≤ k ∧ x = fun p => decide (p ∈ B ∪ X)
  have hstable : ∀ x, W x → ∀ j : Fin L.length, (L.get j).op = GateOp.not →
      reads885 L j x = reads885 L j (fun p => decide (p ∈ B)) := by
    rintro _ ⟨X,hX,rfl⟩
    exact hst X hX
  obtain ⟨M, hML, hM, hw⟩ := replaceStable885 n L W _ hgate hstable
  rw [← hML]
  apply countOnBase885 hc hp Fam o M B hq hk hcard hcross hM
  intro i X hX
  let x := fun p => decide (p ∈ B ∪ X)
  have he := congrArg (fun w : List Bool => w.getD (o i) false) (hw x ⟨X,hX,rfl⟩)
  change Circuit.eval ⟨M, o i⟩ (List.ofFn x) = _
  calc
    _ = Circuit.eval ⟨L, o i⟩ (List.ofFn x) := he
    _ = _ := by simpa [x] using horig i x

end PEqualNP.Outside.L_meta_885

theorem PEqualNP.Outside.L_meta_885 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length := by
  classical
  intro hc hp n m q Fam hcard hcross hmeet hdeg t k L o ht hk hops hnot hmono horig K hb hlast
  by_cases hzero : q = 0
  · subst q
    simp at hlast
    omega
  have hq : 1 ≤ q := by omega
  obtain ⟨B, hB⟩ := PEqualNP.Outside.L_meta_885.window885 L ht hk hnot hmono
  have hsurv := PEqualNP.Outside.L_meta_885.surviving_fam Fam hmeet hdeg B
  rcases hB with ⟨hsize, hstable⟩ | ⟨hsize, hstable⟩
  · have harr := PEqualNP.Outside.L_meta_885.early_window_arith ht hsize hsurv
      (PEqualNP.Outside.L_meta_885.empty_live Fam B) hb
    have hbound := PEqualNP.Outside.L_meta_885.countFromStable885 hc hp Fam o L B hq hk
      hcard hcross hops horig hstable
    exact harr.trans (by simpa only [Nat.mul_comm] using hbound)
  · have harr := PEqualNP.Outside.L_meta_885.late_arith K q m _ t k B.card hsize hsurv hlast
    have hbound := PEqualNP.Outside.L_meta_885.countFromStable885 hc hp Fam o L B hq hq
      hcard hcross hops horig (fun X _ => hstable X)
    exact harr.trans (by simpa only [Nat.min_self, Nat.mul_comm] using hbound)
