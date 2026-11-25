import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.R_meta_4185_811
    (decompose : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ D : Finset (Fin n),
      let N := Finset.univ.filter fun v => ∃ u ∈ D, G.Adj u v
      let W := Finset.univ \ (D ∪ N)
      (∀ u ∈ D, ∀ v ∈ D, ¬G.Adj u v) ∧
      (∃ f : N → Fin n, Function.Injective f ∧ ∀ x : N, f x ∈ D ∧ G.Adj x.val (f x)) ∧
      ∀ A ⊆ W, (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) → A.Nonempty →
        A.card < (W.filter fun v => ∃ u ∈ A, G.Adj u v).card)
    (matching : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ (X : Finset (Fin n)) (f : X → Fin n), Function.Injective f →
      (∀ x : X, G.Adj x.val (f x) ∧ f x ∉ X) →
      X.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ D : Finset (Fin n),
      let N := Finset.univ.filter fun v => ∃ u ∈ D, G.Adj u v
      let W := Finset.univ \ (D ∪ N)
      let b := (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card
      let z := (Ustar G C).card
      (∀ u ∈ D, ∀ v ∈ D, ¬G.Adj u v) →
      (∃ f : N → Fin n, Function.Injective f ∧ ∀ x : N, f x ∈ D ∧ G.Adj x.val (f x)) →
      (∀ A ⊆ W, (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) → A.Nonempty →
        A.card < (W.filter fun v => ∃ u ∈ A, G.Adj u v).card) →
      W.Nonempty → b + 1 < N.card + W.card + z →
      ∃ I ⊆ W, (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) ∧ N.card + (W.card - I.card) + z ≤ b) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G inst C square edge least top
  obtain ⟨D, independent, sat, expand⟩ := decompose n G
  let N : Finset (Fin n) := Finset.univ.filter fun v => ∃ u ∈ D, G.Adj u v
  let W := Finset.univ \ (D ∪ N)
  let b := (tops G C \ centreless G C).card + 2 * (centreless G C).card +
    (junk G C).card + (orN G C \ lam G C).card
  let z := (Ustar G C).card
  have sep {v : Fin n} (hv : v ∈ D) : v ∉ N := by
    intro hn
    obtain ⟨_,u,hu,adj⟩ := Finset.mem_filter.mp hn
    exact independent u hu v hv adj
  obtain ⟨f, injective, fm⟩ := sat
  have charge : N.card + z ≤ b := matching n G C square edge least top N f injective
    (fun x => ⟨(fm x).2, sep (fm x).1⟩)
  have finish (I : Finset (Fin n)) (iw : I ⊆ W)
      (ii : ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v)
      (budget : N.card + (W.card - I.card) + z ≤ b) :
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card + z ≤ b := by
    refine ⟨N ∪ (W \ I), ?_, ?_⟩
    · intro u v adj
      by_cases un : u ∈ N
      · exact Or.inl (Finset.mem_union_left _ un)
      by_cases vn : v ∈ N
      · exact Or.inr (Finset.mem_union_left _ vn)
      have ud : u ∉ D := fun hu => vn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,adj⟩)
      have vd : v ∉ D := fun hv => un (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,adj.symm⟩)
      have uw : u ∈ W := by simp [W,ud,un]
      have vw : v ∈ W := by simp [W,vd,vn]
      by_cases ui : u ∈ I
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨vw, fun vi => ii u ui v vi adj⟩))
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨uw,ui⟩))
    · have h := Finset.card_union_le N (W \ I)
      rw [Finset.card_sdiff_of_subset iw] at h
      omega
  by_cases we : W.Nonempty
  · by_cases pressure : b + 1 < N.card + W.card + z
    · obtain ⟨I,iw,ii,budget⟩ :=
        core n G C square edge least top D independent ⟨f,injective,fm⟩ expand we pressure
      exact finish I iw ii budget
    · obtain ⟨w,hw⟩ := we
      refine finish {w} (Finset.singleton_subset_iff.mpr hw) ?_ ?_
      · intro u hu v hv
        obtain rfl := Finset.mem_singleton.mp hu
        obtain rfl := Finset.mem_singleton.mp hv
        exact G.loopless.irrefl _
      · simp only [Finset.card_singleton]
        have wp : 0 < W.card := Finset.card_pos.mpr ⟨w,hw⟩
        omega
  · have wc : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp we
    apply finish ∅ (Finset.empty_subset _)
    · simp
    · simpa [wc] using charge
