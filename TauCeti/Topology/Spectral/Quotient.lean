/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallyProConstructible

/-!
# Quotients of spectral and locally spectral spaces

This file establishes Scholze's topological criteria for quotients of spectral and locally spectral
spaces by locally pro-constructible equivalence relations:

* Invariant open neighbourhoods, generalizing quotient maps, and T₀ separation for quotients of
  locally spectral spaces by locally pro-constructible equivalence relations whose first projection
  is spectral and generalizing (Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.7).
* The spectral quotient criterion: a quotient of a spectral space by a pro-constructible
  equivalence relation with generalizing projections is spectral as soon as the quotient topology
  admits a basis of opens with compact preimages (Lemma 2.9).
* The open-projection criterion: for a locally pro-constructible equivalence relation on a
  quasiseparated locally spectral space whose first projection is spectral and open, the quotient
  is locally spectral and quasiseparated, and the quotient map is open, spectral, locally spectral,
  and generalizing (Lemma 2.10).

By symmetry of an equivalence relation, swapping the two coordinates of its graph
`{q : X × X // r q.1 q.2}` is a homeomorphism intertwining the two projections, so hypotheses on
the first projection automatically hold for the second as well.

## Main results

* `TauCeti.isOpenMap_quotientMk_of_isOpenMap`: openness of the first graph projection makes
  `Quotient.mk r` an open map.
* `TauCeti.isLocallyProConstructible_preimage_image_quotientMk`: saturations of locally
  pro-constructible sets remain locally pro-constructible.
* `TauCeti.exists_isOpen_invariant_between` and `TauCeti.exists_isOpen_invariant_subset_sInter`:
  invariant open neighbourhoods between a compact open subset and an invariant intersection of a
  nonempty family of compact opens (Lemma 2.7).
* `TauCeti.generalizingMap_quotientMk` and `TauCeti.t0Space_quotient`: the quotient map is
  generalizing and the quotient space is T₀ (Lemma 2.7).
* `TauCeti.spectralSpace_quotient`: the spectral quotient criterion (Lemma 2.9).
* `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap` and
  `TauCeti.spectralSpace_quotient_of_isOpenMap`: the locally spectral and spectral open-projection
  criteria (Lemma 2.10).

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Symmetry and saturation for equivalence relations -/

/-- Swapping coordinates is a self-homeomorphism of the graph of a `Setoid`. -/
private def setoidGraphSwap (r : Setoid X) :
    {q : X × X // r q.1 q.2} ≃ₜ {q : X × X // r q.1 q.2} :=
  (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨r.symm, r.symm⟩

omit [TopologicalSpace X] in
private lemma preimage_image_quotientMk (r : Setoid X) (A : Set X) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' A) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
        ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨x, hxA, hxy⟩
    exact ⟨⟨(x, y), Quotient.exact hxy⟩, hxA, rfl⟩
  · rintro ⟨⟨⟨x, _⟩, hxy⟩, hxA, rfl⟩
    exact ⟨x, hxA, Quotient.sound hxy⟩

private lemma generalizingMap_snd_of_fst {r : Setoid X}
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
  (setoidGraphSwap r).isOpenEmbedding.generalizingMap.comp hs

private lemma isSpectralMap_snd_of_fst {r : Setoid X}
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 where
  toContinuous := continuous_snd.comp continuous_subtype_val
  isCompact_preimage_of_isOpen := fun U hUo hUc ↦ by
    have heq : (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ⁻¹' U =
        setoidGraphSwap r ⁻¹' ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' U) := rfl
    rw [heq, (setoidGraphSwap r).isCompact_preimage]
    exact hs.isCompact_preimage_of_isOpen hUo hUc

private lemma isOpenMap_snd_of_fst {r : Setoid X}
    (hs : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
  hs.comp (setoidGraphSwap r).isOpenMap

private lemma isLocallySpectralMap_fst_graph (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) :
    IsLocallySpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  exact isLocallySpectralMap_fst.comp (hX.prod hX)
    (hR.isLocallySpectralMap_subtypeVal (hX.prod hX))

private lemma isLocallySpectralMap_snd_graph (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) :
    IsLocallySpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
  (isLocallySpectralMap_fst_graph hX r hR).comp_isOpenEmbedding (setoidGraphSwap r).isOpenEmbedding

/-- If the first projection from the graph of an equivalence relation is an open map, then the
quotient projection `Quotient.mk r` is an open map. -/
theorem isOpenMap_quotientMk_of_isOpenMap {r : Setoid X}
    (hs : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsOpenMap (Quotient.mk r) := by
  intro U hUo
  have hqm : IsQuotientMap (Quotient.mk r) := isQuotientMap_quotient_mk'
  rw [← hqm.isOpen_preimage, preimage_image_quotientMk]
  exact isOpenMap_snd_of_fst hs _ (hUo.preimage (continuous_fst.comp continuous_subtype_val))

/-! ### Invariant neighbourhoods, generalizing quotients, and T₀ separation -/

/-- The `r`-saturation of a locally pro-constructible subset of a locally spectral space is again
locally pro-constructible when the graph of `r` is locally pro-constructible with spectral first
projection. -/
theorem isLocallyProConstructible_preimage_image_quotientMk (hX : IsLocallySpectralSpace X)
    (r : Setoid X) (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {A : Set X} (hA : IsLocallyProConstructible A) :
    IsLocallyProConstructible (Quotient.mk r ⁻¹' (Quotient.mk r '' A)) := by
  rw [preimage_image_quotientMk]
  exact (hA.preimage hX (isLocallySpectralMap_fst_graph hX r hR)).image
    (hR.isLocallySpectralSpace (hX.prod hX))
    (isLocallySpectralMap_snd_graph hX r hR)
    (isSpectralMap_snd_of_fst hs)

/-- The closure of an `r`-invariant locally pro-constructible set is `r`-invariant whenever the
first projection from the graph of `r` is generalizing. -/
private lemma invariant_closure_of_isLocallyProConstructible (hX : IsLocallySpectralSpace X)
    (r : Setoid X) (hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {A : Set X} (hA : IsLocallyProConstructible A)
    (hAinv : ∀ ⦃x y : X⦄, r x y → x ∈ A → y ∈ A) :
    ∀ ⦃x y : X⦄, r x y → x ∈ closure A → y ∈ closure A := by
  intro x y hxy hx
  rw [hA.closure_eq_setOfPred_specializes hX] at hx ⊢
  obtain ⟨z, hzA, hzx⟩ := hx
  -- Lift `z ⤳ x` along the first projection from `(x, y) ∈ R` to get a specialization to `y`.
  obtain ⟨q, hqspec, hqfst⟩ := hg (a := (⟨(x, y), hxy⟩ : {q : X × X // r q.1 q.2})) hzx
  refine ⟨q.1.2, hAinv (hqfst ▸ q.2) hzA, ?_⟩
  exact hqspec.map (continuous_snd.comp continuous_subtype_val)

/-- Invariant-neighbourhood construction (Scholze, *Étale cohomology of diamonds*, §2, proof of
Lemma 2.7): given an open subset `W'` containing the `r`-saturation of an open subset `W`, there
exists an `r`-invariant open subset `U` with `W ⊆ U ⊆ W'`, namely the complement of the closure
of the `r`-saturation of `W'ᶜ`. -/
theorem exists_isOpen_invariant_between (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W W' : Set X} (hWo : IsOpen W) (hW'o : IsOpen W')
    (hWW' : Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W') :
    ∃ U : Set X,
      IsOpen U ∧ (∀ ⦃x y : X⦄, r x y → x ∈ U → y ∈ U) ∧ W ⊆ U ∧ U ⊆ W' := by
  let A : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W'ᶜ)
  have hA_lpc : IsLocallyProConstructible A :=
    isLocallyProConstructible_preimage_image_quotientMk hX r hR hs
      hW'o.isClosed_compl.isLocallyProConstructible
  have hA_inv : ∀ ⦃x y : X⦄, r x y → x ∈ A → y ∈ A := fun x y hxy hx ↦ by
    simpa only [A, mem_preimage, Quotient.sound hxy] using hx
  have hcl_inv := invariant_closure_of_isLocallyProConstructible hX r hg hA_lpc hA_inv
  refine ⟨(closure A)ᶜ, isClosed_closure.isOpen_compl,
    fun x y hxy hx hy ↦ hx (hcl_inv (r.symm hxy) hy), fun x hxW hxcl ↦ ?_, fun x hxU ↦ ?_⟩
  · -- `W` is open and disjoint from `A`, hence disjoint from `closure A`.
    obtain ⟨z, hzW, w, hw, hwz⟩ := mem_closure_iff.1 hxcl W hWo hxW
    exact hw (hWW' ⟨z, hzW, hwz.symm⟩)
  · by_contra hxW'
    exact hxU (subset_closure ⟨x, hxW', rfl⟩)

/-- **Invariant neighbourhoods for pro-constructible equivalence relations**
(Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.7). For a locally pro-constructible
equivalence relation `r` on a locally spectral space `X` whose first projection is spectral and
generalizing, every compact open subset `W ⊆ X` lies inside an `r`-invariant open subset `U`
contained in an `r`-invariant intersection of a nonempty family of compact open subsets of `X`. -/
theorem exists_isOpen_invariant_subset_sInter (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ (U : Set X) (S : Set (Set X)),
      IsOpen U ∧ (∀ ⦃x y : X⦄, r x y → x ∈ U → y ∈ U) ∧
      S.Nonempty ∧ (∀ V ∈ S, IsOpen V ∧ IsCompact V) ∧
      (∀ ⦃x y : X⦄, r x y → x ∈ ⋂₀ S → y ∈ ⋂₀ S) ∧
      W ⊆ U ∧ U ⊆ ⋂₀ S := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have hEc : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
    rw [preimage_image_quotientMk]
    exact (hs.isCompact_preimage_of_isOpen hWo hWc).image
      (continuous_snd.comp continuous_subtype_val)
  -- Enclose the compact saturation `E` in a compact open `W'`.
  obtain ⟨W', hW'c, hW'o, hEW', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc isOpen_univ (subset_univ _)
  obtain ⟨U, hUo, hUinv, hWU, hUW'⟩ :=
    exists_isOpen_invariant_between hX r hR hs hg hWo hW'o hEW'
  -- The saturation `E'` of `W'` is compact and stable under generalization, hence equals the
  -- intersection of the nonempty family of compact open subsets containing it.
  let E' : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W')
  have hE'c : IsCompact E' := by
    dsimp only [E']
    rw [preimage_image_quotientMk]
    exact (hs.isCompact_preimage_of_isOpen hW'o hW'c).image
      (continuous_snd.comp continuous_subtype_val)
  have hE'g : StableUnderGeneralization E' := by
    dsimp only [E']
    rw [preimage_image_quotientMk]
    exact (generalizingMap_snd_of_fst hg).stableUnderGeneralization_image
      (hW'o.preimage hs.continuous).stableUnderGeneralization
  let S : Set (Set X) := {V : Set X | IsOpen V ∧ IsCompact V ∧ E' ⊆ V}
  have hE'eq : E' = ⋂₀ S := hE'c.eq_sInter_of_stableUnderGeneralization hE'g
  obtain ⟨W'', hW''c, hW''o, hE'W'', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hE'c isOpen_univ (subset_univ _)
  refine ⟨U, S, hUo, hUinv, ⟨W'', hW''o, hW''c, hE'W''⟩,
    fun V hV ↦ ⟨hV.1, hV.2.1⟩, ?_, hWU, ?_⟩
  · intro x y hxy hx
    rw [← hE'eq] at hx ⊢
    simpa only [E', mem_preimage, Quotient.sound hxy] using hx
  · rw [← hE'eq]
    exact hUW'.trans fun x hx ↦ ⟨x, hx, rfl⟩

/-- The quotient map for a locally pro-constructible equivalence relation on a locally spectral
space whose first projection is spectral and generalizing is itself generalizing
(Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.7). -/
theorem generalizingMap_quotientMk (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap (Quotient.mk r) := by
  intro x y hy
  obtain ⟨y₀, rfl⟩ := Quotient.exists_rep y
  let O : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' {y₀})
  have hO_lpc : IsLocallyProConstructible O :=
    isLocallyProConstructible_preimage_image_quotientMk hX r hR hs
      (isLocallyProConstructible_singleton y₀)
  have hO_inv : ∀ ⦃a b : X⦄, r a b → a ∈ O → b ∈ O := fun a b hab ha ↦ by
    simpa only [O, mem_preimage, Quotient.sound hab] using ha
  have hcl_inv := invariant_closure_of_isLocallyProConstructible hX r hg hO_lpc hO_inv
  -- Because `closure O` is closed and `r`-invariant, its image is closed in the quotient.
  have hpre_cl : Quotient.mk r ⁻¹' (Quotient.mk r '' closure O) = closure O := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro a ⟨b, hb, hba⟩
    exact hcl_inv (Quotient.exact hba) hb
  have hqm : IsQuotientMap (Quotient.mk r) := isQuotientMap_quotient_mk'
  have hcl_quot : IsClosed (Quotient.mk r '' closure O) := by
    rw [← hqm.isClosed_preimage, hpre_cl]
    exact isClosed_closure
  have hxcl : x ∈ closure O := by
    rw [← hpre_cl]
    exact hy.mem_closed hcl_quot ⟨y₀, subset_closure ⟨y₀, mem_singleton y₀, rfl⟩, rfl⟩
  rw [hO_lpc.closure_eq_setOfPred_specializes hX] at hxcl
  obtain ⟨x', ⟨z, hz, hzx'⟩, hx'x⟩ := hxcl
  rw [mem_singleton_iff] at hz
  exact ⟨x', hx'x, hzx'.symm.trans (congrArg (Quotient.mk r) hz)⟩

/-- **Quotients by pro-constructible equivalence relations are T₀**
(Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.7). For a locally pro-constructible
equivalence relation on a locally spectral space whose first projection is spectral and
generalizing, the quotient space is Kolmogorov. -/
theorem t0Space_quotient (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    T0Space (Quotient r) := by
  have _ : T0Space X := hX.t0Space
  have hqgen : GeneralizingMap (Quotient.mk r) := generalizingMap_quotientMk hX r hR hs hg
  refine (t0Space_iff_inseparable (Quotient r)).mpr fun a b hab ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  -- Take a point `x₀` minimal for specialization in the orbit of `x` inside a spectral open `V`.
  obtain ⟨V, hVo, hxV, hVs⟩ := isLocallySpectralSpace_iff.mp hX x
  have _ : SpectralSpace V := hVs
  let O : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' {x})
  have hO_lpc : IsLocallyProConstructible O :=
    isLocallyProConstructible_preimage_image_quotientMk hX r hR hs
      (isLocallyProConstructible_singleton x)
  have hOV : IsProConstructible ((Subtype.val : V → X) ⁻¹' O) :=
    hO_lpc.isProConstructible_preimage hVo
  obtain ⟨x₀, hx₀O, -, hx₀min⟩ := hOV.exists_minimal_specializes (x₀ := ⟨x, hxV⟩)
    ⟨x, mem_singleton x, rfl⟩
  have hqx₀ : Quotient.mk r x₀.1 = Quotient.mk r x := by
    obtain ⟨z, hz, hzx₀⟩ := hx₀O
    rw [mem_singleton_iff] at hz
    exact hzx₀.symm.trans (congrArg (Quotient.mk r) hz)
  -- Lift `⟦y⟧ ⤳ ⟦x₀⟧` and then `⟦x⟧ ⤳ ⟦y₀⟧`; minimality forces `x₀ = y₀`.
  obtain ⟨y₀, hy₀x₀, hqy₀⟩ := hqgen (a := x₀.1) (hqx₀.symm ▸ hab.symm.specializes)
  obtain ⟨x₁, hx₁y₀, hqx₁⟩ := hqgen (a := y₀) (hqy₀.symm ▸ hab.specializes)
  have hx₁x₀ : x₁ ⤳ x₀.1 := hx₁y₀.trans hy₀x₀
  have hx₁V : x₁ ∈ V := hx₁x₀.mem_open hVo x₀.2
  have hx₁O : (⟨x₁, hx₁V⟩ : V) ∈ (Subtype.val : V → X) ⁻¹' O :=
    ⟨x, mem_singleton x, hqx₁.symm⟩
  have hx₀x₁' : x₀ ⤳ (⟨x₁, hx₁V⟩ : V) :=
    hx₀min ⟨x₁, hx₁V⟩ hx₁O
      (IsEmbedding.subtypeVal.isInducing.specializes_iff.mp hx₁x₀)
  have hx₀y₀ : x₀.1 ⤳ y₀ := (hx₀x₁'.map continuous_subtype_val).trans hx₁y₀
  have heq : x₀.1 = y₀ := (hx₀y₀.antisymm hy₀x₀).eq
  rw [← hqx₀, heq, hqy₀]

/-! ### Spectral and locally spectral quotients -/

private lemma isSpectralMap_fst_graph_of_spectralSpace [SpectralSpace X] (r : Setoid X)
    (hR : IsProConstructible {q : X × X | r q.1 q.2}) :
    IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
  isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal

/-- **The spectral quotient criterion** (Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.9).
For a spectral space `X` and an equivalence relation whose graph is pro-constructible in `X × X`
with generalizing first projection (hence generalizing second projection by symmetry), if the
quotient topology admits a basis of open subsets with compact preimages then `Quotient r` is
spectral and `Quotient.mk r` is spectral and generalizing. -/
theorem spectralSpace_quotient [SpectralSpace X] (r : Setoid X)
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hB : ∃ B : Set (Set (Quotient r)), IsTopologicalBasis B ∧
      ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) ∧ IsSpectralMap (Quotient.mk r) ∧
      GeneralizingMap (Quotient.mk r) := by
  obtain ⟨B, hB_basis, hB_pre⟩ := hB
  have hX : IsLocallySpectralSpace X := SpectralSpace.isLocallySpectralSpace
  have hR_lpc : IsLocallyProConstructible {q : X × X | r q.1 q.2} := hR.isLocallyProConstructible
  have hs_spec := isSpectralMap_fst_graph_of_spectralSpace r hR
  have hq_spec : IsSpectralMap (Quotient.mk r) :=
    isSpectralMap_of_isTopologicalBasis hB_basis continuous_quotient_mk' hB_pre
  have hq_gen : GeneralizingMap (Quotient.mk r) :=
    generalizingMap_quotientMk hX r hR_lpc hs_spec hs
  have hT0 : T0Space (Quotient r) := t0Space_quotient hX r hR_lpc hs_spec hs
  have hPre : PrespectralSpace (Quotient r) :=
    .of_isTopologicalBasis hB_basis fun V hV ↦
      Set.image_preimage_eq V Quotient.mk_surjective ▸
        (hB_pre V hV).image continuous_quotient_mk'
  have hQS : QuasiSeparatedSpace (Quotient r) :=
    hq_spec.quasiSeparatedSpace_of_surjective Quotient.mk_surjective
  have hSober : QuasiSober (Quotient r) :=
    hq_spec.quasiSober_of_surjective Quotient.mk_surjective
  exact ⟨{
    toT0Space := hT0
    toCompactSpace := Quotient.compactSpace
    toQuasiSober := hSober
    toQuasiSeparatedSpace := hQS
    toPrespectralSpace := hPre }, hq_spec, hq_gen⟩

/-- **The open-projection quotient criterion**
(Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.10). For a locally pro-constructible
equivalence relation on a quasiseparated locally spectral space whose first projection is spectral
and open (hence automatically generalizing, and likewise for the second projection by symmetry),
the quotient space is locally spectral and quasiseparated, and the quotient map is open, spectral,
locally spectral, and generalizing. -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X) (r : Setoid X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (ho : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallySpectralSpace (Quotient r) ∧ QuasiSeparatedSpace (Quotient r) ∧
      IsOpenMap (Quotient.mk r) ∧ IsSpectralMap (Quotient.mk r) ∧
      IsLocallySpectralMap (Quotient.mk r) ∧ GeneralizingMap (Quotient.mk r) := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have hR_lss : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have hg : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
    (isLocallySpectralMap_fst_graph hX r hR).generalizingMap_of_isOpenMap hR_lss hX ho
  have hq_open : IsOpenMap (Quotient.mk r) := isOpenMap_quotientMk_of_isOpenMap ho
  have hq_gen : GeneralizingMap (Quotient.mk r) := generalizingMap_quotientMk hX r hR hs hg
  have hT0 : T0Space (Quotient r) := t0Space_quotient hX r hR hs hg
  -- The images of compact open subsets of `X` form a basis of `Quotient r` with compact preimages.
  let B : Set (Set (Quotient r)) :=
    (Quotient.mk r '' ·) '' {W : Set X | IsOpen W ∧ IsCompact W}
  have hB_basis : IsTopologicalBasis B := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun y O hyO hOo ↦ ?_
    · rintro _ ⟨W, ⟨hWo, -⟩, rfl⟩
      exact hq_open W hWo
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep y
      obtain ⟨W, ⟨hWo, hWc⟩, hxW, hWO⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (a := x) hyO
          (hOo.preimage continuous_quotient_mk')
      exact ⟨Quotient.mk r '' W, ⟨W, ⟨hWo, hWc⟩, rfl⟩, ⟨x, hxW, rfl⟩,
        image_subset_iff.mpr hWO⟩
  have hB_pre : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V) := by
    rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
    rw [preimage_image_quotientMk]
    exact (hs.isCompact_preimage_of_isOpen hWo hWc).image
      (continuous_snd.comp continuous_subtype_val)
  have hq_spec : IsSpectralMap (Quotient.mk r) :=
    isSpectralMap_of_isTopologicalBasis hB_basis continuous_quotient_mk' hB_pre
  have hPre : PrespectralSpace (Quotient r) :=
    .of_isTopologicalBasis hB_basis <| by
      rintro _ ⟨_, ⟨-, hWc⟩, rfl⟩
      exact hWc.image continuous_quotient_mk'
  have hQS : QuasiSeparatedSpace (Quotient r) :=
    hq_spec.quasiSeparatedSpace_of_surjective Quotient.mk_surjective
  -- Each point `⟦x⟧` has a compact open neighbourhood `V = q '' W` whose preimage
  -- `U = q ⁻¹' V` is a spectral open in `X`, making `V` quasi-sober via `U → V`.
  have hLSS : IsLocallySpectralSpace (Quotient r) := by
    refine isLocallySpectralSpace_iff.mpr fun y ↦ ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep y
    obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
    have hWc : IsCompact W := isCompact_iff_compactSpace.mpr hWs.toCompactSpace
    let V : Set (Quotient r) := Quotient.mk r '' W
    have hVo : IsOpen V := hq_open W hWo
    have hVc : IsCompact V := hWc.image continuous_quotient_mk'
    refine ⟨V, hVo, ⟨x, hxW, rfl⟩, ?_⟩
    let U : Set X := Quotient.mk r ⁻¹' V
    have hUo : IsOpen U := hVo.preimage continuous_quotient_mk'
    have hUc : IsCompact U := hq_spec.isCompact_preimage_of_isOpen hVo hVc
    have _ : SpectralSpace U := hX.spectralSpace_of_isOpen_isCompact hUo hUc
    have _ : PrespectralSpace V := hVo.isOpenEmbedding_subtypeVal.prespectralSpace
    have _ : QuasiSeparatedSpace V := hVo.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
    have _ : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    let f : U → V := fun u ↦ ⟨Quotient.mk r u.1, u.2⟩
    have hf_surj : Function.Surjective f := fun ⟨z, hz⟩ ↦ by
      obtain ⟨a, rfl⟩ := Quotient.exists_rep z
      exact ⟨⟨a, hz⟩, rfl⟩
    have hf_spec : IsSpectralMap f := by
      refine ⟨(continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _,
        fun K hKo hKc ↦ ?_⟩
      have hK_open : IsOpen (Subtype.val '' K : Set (Quotient r)) := hVo.isOpenMap_subtype_val K hKo
      have hK_comp : IsCompact (Subtype.val '' K : Set (Quotient r)) :=
        hKc.image continuous_subtype_val
      have heq :
          (Subtype.val : U → X) '' (f ⁻¹' K) = Quotient.mk r ⁻¹' (Subtype.val '' K) := by
        ext a
        constructor
        · rintro ⟨u, huK, rfl⟩
          exact ⟨f u, huK, rfl⟩
        · rintro ⟨v, hvK, hqa⟩
          have haU : a ∈ U := mem_preimage.mpr (hqa ▸ v.2)
          refine ⟨⟨a, haU⟩, ?_, rfl⟩
          have hf_eq : f ⟨a, haU⟩ = v := Subtype.ext hqa.symm
          rwa [mem_preimage, hf_eq]
      rw [IsEmbedding.subtypeVal.isCompact_iff, heq]
      exact hq_spec.isCompact_preimage_of_isOpen hK_open hK_comp
    exact {
      toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := hf_spec.quasiSober_of_surjective hf_surj
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  exact ⟨hLSS, hQS, hq_open, hq_spec, hq_spec.isLocallySpectralMap, hq_gen⟩

/-- Spectral specialization of `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`: if `X` is
spectral and `r` is a pro-constructible equivalence relation whose first graph projection is open,
then `Quotient r` is spectral and `Quotient.mk r` is open, spectral, and generalizing. -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X] (r : Setoid X)
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (ho : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    SpectralSpace (Quotient r) ∧ IsOpenMap (Quotient.mk r) ∧
      IsSpectralMap (Quotient.mk r) ∧ GeneralizingMap (Quotient.mk r) := by
  obtain ⟨hLSS, hQS, hq_open, hq_spec, -, hq_gen⟩ :=
    isLocallySpectralSpace_quotient_of_isOpenMap SpectralSpace.isLocallySpectralSpace r
      hR.isLocallyProConstructible (isSpectralMap_fst_graph_of_spectralSpace r hR) ho
  exact ⟨spectralSpace_iff_isLocallySpectralSpace.mpr ⟨hLSS, Quotient.compactSpace, hQS⟩,
    hq_open, hq_spec, hq_gen⟩

end TauCeti
