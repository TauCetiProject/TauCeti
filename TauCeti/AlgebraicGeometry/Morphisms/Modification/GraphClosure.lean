/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The graph closure in Chow's lemma

Let `f : X ⟶ S` and `q : P ⟶ S` be morphisms of schemes, let `U ⊆ X` be an open subscheme with
quasi-compact inclusion, and let `g : U ⟶ P` be a morphism over `S`. The graph of `g` is an
immersion `U ⟶ X ×_S P`, and its scheme-theoretic image `X*` is the *graph closure* of `g`.
This is the construction at the heart of the proof of Chow's lemma (Stacks, Lemma 30.18.1
(0200)), where `P` is a fibre product of projective schemes over `S` into which the members of an
affine open cover of `X` embed.

The two projections `X* ⟶ X` and `X* ⟶ P` are determined by their restriction to `U`, which is
scheme-theoretically dense in `X*`. This gives the two properties of the construction used in
Chow's lemma:

* for `q` separated, the projection `X* ⟶ X` is an isomorphism over `U`; it is proper when `q`
  is, and then a modification when `U` is dense in `X`;
* if `X` is separated over `S` and covered by opens `V i` containing `U`, and each `V i` is
  embedded by an open immersion `j i : V i ⟶ P' i` over `S` into a separated `S`-scheme `P' i`
  receiving a morphism `h i : P ⟶ P' i` over `S` with `g ≫ h i` the restriction of `j i` to `U`,
  then the projection `X* ⟶ P` is an immersion. On the open of `X*` where `X* ⟶ P' i` lands in
  the image of `j i`, the first projection factors through the second, so there `X*` is cut out
  of `P` as a graph.

No Noetherian, reducedness or irreducibility hypothesis is needed: scheme-theoretic density
replaces topological density, and the quasi-compactness of `U ⟶ X` keeps it under restriction to
opens.

## Main definitions

* `TauCeti.AlgebraicGeometry.graphClosure f q U g hg`: the scheme-theoretic image of the graph
  `U ⟶ X ×_S P` of `g`.
* `TauCeti.AlgebraicGeometry.graphClosureFst`, `TauCeti.AlgebraicGeometry.graphClosureSnd`: its
  projections to `X` and to `P`.
* `TauCeti.AlgebraicGeometry.toGraphClosure`: the open immersion of `U` into the graph closure.

## Main results

* `TauCeti.AlgebraicGeometry.isIso_graphClosureFst_restrict`: the projection to `X` is an
  isomorphism over `U`.
* `TauCeti.AlgebraicGeometry.isModification_graphClosureFst`: for `q` proper and `U` dense, the
  projection to `X` is a modification.
* `TauCeti.AlgebraicGeometry.isImmersion_graphClosureSnd`: given open immersions of a cover of
  `X` compatible with `g`, the projection to `P` is an immersion.

## References

* [Stacks Project, Lemma 30.18.1](https://stacks.math.columbia.edu/tag/0200), the proof.
* [Stacks Project, Section 29.7](https://stacks.math.columbia.edu/tag/01RB), scheme theoretic
  closure and density.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

section Corestriction

variable {W Z : Scheme.{u}} (u : W ⟶ Z) [IsSchemeTheoreticallyDominant u] [QuasiCompact u]

/-- A quasi-compact scheme-theoretically dominant morphism stays scheme-theoretically dominant
after corestriction to an open containing its image. -/
theorem isSchemeTheoreticallyDominant_lift_opensι (O : Z.Opens) (hO : Set.range u ⊆ O) :
    IsSchemeTheoreticallyDominant (IsOpenImmersion.lift O.ι u (by simpa using hO)) :=
  IsSchemeTheoreticallyDominant.of_isPullback
    (IsOpenImmersion.isPullback_lift_id u O.ι (by simpa using hO)).flip

end Corestriction

variable {X S P : Scheme.{u}} (f : X ⟶ S) (q : P ⟶ S) (U : X.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ q = U.ι ≫ f)

/-- The graph `U ⟶ X ×_S P` of a morphism `g : U ⟶ P` over `S` defined on an open `U ⊆ X`. -/
def relativeGraph : U.toScheme ⟶ pullback f q :=
  pullback.lift U.ι g hg.symm

@[reassoc (attr := simp)]
theorem relativeGraph_fst : relativeGraph f q U g hg ≫ pullback.fst f q = U.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relativeGraph_snd : relativeGraph f q U g hg ≫ pullback.snd f q = g :=
  pullback.lift_snd _ _ _

/-- The graph of a morphism defined on an open is an immersion. -/
instance : IsImmersion (relativeGraph f q U g hg) := by
  have : IsImmersion (relativeGraph f q U g hg ≫ pullback.fst f q) := by
    rw [relativeGraph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst f q)

/-- The graph of a morphism to a quasi-separated `S`-scheme, defined on an open with
quasi-compact inclusion, is quasi-compact. -/
instance [QuasiCompact U.ι] [QuasiSeparated q] : QuasiCompact (relativeGraph f q U g hg) := by
  have : QuasiCompact (relativeGraph f q U g hg ≫ pullback.fst f q) := by
    rw [relativeGraph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst f q)

/-- The *graph closure* of `g : U ⟶ P` over `S`: the scheme-theoretic image of the graph of `g`
in `X ×_S P`. -/
abbrev graphClosure : Scheme.{u} :=
  (relativeGraph f q U g hg).image

/-- The projection of the graph closure to `X`. -/
def graphClosureFst : graphClosure f q U g hg ⟶ X :=
  (relativeGraph f q U g hg).imageι ≫ pullback.fst f q

/-- The projection of the graph closure to `P`. -/
def graphClosureSnd : graphClosure f q U g hg ⟶ P :=
  (relativeGraph f q U g hg).imageι ≫ pullback.snd f q

/-- The inclusion of `U` into the graph closure of `g`. -/
abbrev toGraphClosure : U.toScheme ⟶ graphClosure f q U g hg :=
  (relativeGraph f q U g hg).toImage

@[reassoc (attr := simp)]
theorem toGraphClosure_graphClosureFst :
    toGraphClosure f q U g hg ≫ graphClosureFst f q U g hg = U.ι := by
  simp [graphClosureFst]

@[reassoc (attr := simp)]
theorem toGraphClosure_graphClosureSnd :
    toGraphClosure f q U g hg ≫ graphClosureSnd f q U g hg = g := by
  simp [graphClosureSnd]

@[reassoc]
theorem graphClosureFst_comp :
    graphClosureFst f q U g hg ≫ f = graphClosureSnd f q U g hg ≫ q := by
  simp [graphClosureFst, graphClosureSnd, pullback.condition]

/-- The projection of the graph closure to `X` is proper when `q` is. -/
instance [IsProper q] : IsProper (graphClosureFst f q U g hg) := by
  rw [graphClosureFst]
  infer_instance

variable [QuasiCompact U.ι] [QuasiSeparated q]

variable {f q U g hg}

/-- Two morphisms from an open of the graph closure containing `U` to a separated `S`-scheme
agree if they agree on `U`. -/
theorem graphClosure_ext {T : Scheme.{u}} (s : T ⟶ S) [IsSeparated s]
    (O : (graphClosure f q U g hg).Opens) (hO : Set.range (toGraphClosure f q U g hg) ⊆ O)
    {a b : O.toScheme ⟶ T} (hab : a ≫ s = b ≫ s)
    (h : IsOpenImmersion.lift O.ι (toGraphClosure f q U g hg) (by simpa using hO) ≫ a =
      IsOpenImmersion.lift O.ι (toGraphClosure f q U g hg) (by simpa using hO) ≫ b) :
    a = b := by
  have := isSchemeTheoreticallyDominant_lift_opensι (toGraphClosure f q U g hg) O hO
  exact ext_of_isSchemeTheoreticallyDominant _ s hab h


omit [QuasiCompact U.ι] [QuasiSeparated q] in
/-- The inclusion of `U` into the graph closure lands in the preimage of every open `V ⊇ U`. -/
theorem range_toGraphClosure_subset_preimage {V : X.Opens} (hUV : U ≤ V) :
    Set.range (toGraphClosure f q U g hg) ⊆ graphClosureFst f q U g hg ⁻¹ᵁ V := by
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
    toGraphClosure_graphClosureFst]
  exact hUV x.2

omit [QuasiCompact U.ι] [QuasiSeparated q] in
/-- On the preimage of an open `V ⊇ U`, the corestricted inclusion of `U` followed by the
restricted first projection is the inclusion of `U` into `V`. -/
@[reassoc]
theorem lift_graphClosureFst_restrict {V : X.Opens} (hUV : U ≤ V) :
    IsOpenImmersion.lift (graphClosureFst f q U g hg ⁻¹ᵁ V).ι (toGraphClosure f q U g hg)
        (by simpa using range_toGraphClosure_subset_preimage hUV) ≫
      (graphClosureFst f q U g hg ∣_ V) = X.homOfLE hUV := by
  simp [← cancel_mono V.ι]

omit [QuasiSeparated q] in
/-- On the preimage of `U`, the projection to `P` is the projection to `U` followed by `g`. -/
theorem graphClosureFst_restrict_comp [IsSeparated q] :
    (graphClosureFst f q U g hg ∣_ U) ≫ g =
      (graphClosureFst f q U g hg ⁻¹ᵁ U).ι ≫ graphClosureSnd f q U g hg := by
  refine graphClosure_ext q _ (range_toGraphClosure_subset_preimage (le_refl U)) ?_ ?_
  · simp [hg, graphClosureFst_comp]
  · rw [lift_graphClosureFst_restrict_assoc (le_refl U), IsOpenImmersion.lift_fac_assoc]
    simp

omit [QuasiSeparated q] in
/-- **The graph closure is an isomorphism over `U`.** -/
instance isIso_graphClosureFst_restrict [IsSeparated q] :
    IsIso (graphClosureFst f q U g hg ∣_ U) := by
  have hO := range_toGraphClosure_subset_preimage (hg := hg) (le_refl U)
  refine ⟨IsOpenImmersion.lift (graphClosureFst f q U g hg ⁻¹ᵁ U).ι (toGraphClosure f q U g hg)
    (by simpa using hO), ?_,
    by simpa using lift_graphClosureFst_restrict (hg := hg) (le_refl U)⟩
  rw [← cancel_mono ((graphClosureFst f q U g hg ⁻¹ᵁ U).ι ≫ (relativeGraph f q U g hg).imageι),
    Category.assoc, IsOpenImmersion.lift_fac_assoc, Category.id_comp]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, Scheme.Hom.toImage_imageι, relativeGraph_fst,
      morphismRestrict_ι]
    rfl
  · simp only [Category.assoc, Scheme.Hom.toImage_imageι, relativeGraph_snd,
      graphClosureFst_restrict_comp]
    rfl

omit [QuasiSeparated q] in
/-- **The graph closure is a modification.** When `q` is proper and `U` is dense in `X`, the
projection of the graph closure to `X` is a modification, an isomorphism over `U`. -/
theorem isModification_graphClosureFst [IsProper q] (hU : Dense (U : Set X)) :
    IsModification (graphClosureFst f q U g hg) where
  exists_isIso_morphismRestrict :=
    ⟨U, hU, (toGraphClosure f q U g hg).denseRange.mono
      (range_toGraphClosure_subset_preimage le_rfl), inferInstance⟩

section Immersion

variable {V : X.Opens} (hUV : U ≤ V) {P' : Scheme.{u}} {q' : P' ⟶ S} {h : P ⟶ P'}
  (hh : h ≫ q' = q) {j : V.toScheme ⟶ P'} [IsOpenImmersion j] (hj : j ≫ q' = V.ι ≫ f)
  (hgj : g ≫ h = X.homOfLE hUV ≫ j)

include hh hj hgj in
/-- If `V ⊇ U` embeds openly into `P'`, compatibly with `g` and a map `h : P ⟶ P'`, then the
projection of the graph closure to `P` maps the preimage of `V` into the preimage under `h` of
the image of `V`. -/
theorem graphClosureFst_preimage_le [IsSeparated q'] :
    graphClosureFst f q U g hg ⁻¹ᵁ V ≤ graphClosureSnd f q U g hg ⁻¹ᵁ h ⁻¹ᵁ j.opensRange := by
  have key : (graphClosureFst f q U g hg ∣_ V) ≫ j =
      (graphClosureFst f q U g hg ⁻¹ᵁ V).ι ≫ graphClosureSnd f q U g hg ≫ h := by
    refine graphClosure_ext q' _ (range_toGraphClosure_subset_preimage hUV) ?_ ?_
    · simp [hj, hh, graphClosureFst_comp]
    · rw [lift_graphClosureFst_restrict_assoc hUV, IsOpenImmersion.lift_fac_assoc,
        toGraphClosure_graphClosureSnd_assoc, hgj]
  intro x hx
  have := congrArg (fun φ ↦ φ ⟨x, hx⟩) key
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
  exact ⟨_, this.trans rfl⟩

include hh hj hgj in
/-- Where the projection of the graph closure to `P'` lands in the image of `V`, the projection
to `X` is determined by the projection to `P`: it is the composite of the projection to `P`, the
map `h` and the inverse of `j`. -/
theorem graphClosureSnd_restrict_comp [IsSeparated f] :
    (graphClosureSnd f q U g hg ∣_ h ⁻¹ᵁ j.opensRange) ≫ (h ∣_ j.opensRange) ≫
        j.isoOpensRange.inv ≫ V.ι =
      (graphClosureSnd f q U g hg ⁻¹ᵁ h ⁻¹ᵁ j.opensRange).ι ≫ graphClosureFst f q U g hg := by
  have hO : Set.range (toGraphClosure f q U g hg) ⊆
      graphClosureSnd f q U g hg ⁻¹ᵁ h ⁻¹ᵁ j.opensRange := by
    rintro _ ⟨x, rfl⟩
    have : (toGraphClosure f q U g hg ≫ graphClosureSnd f q U g hg ≫ h) x =
        j (X.homOfLE hUV x) := by
      rw [toGraphClosure_graphClosureSnd_assoc, hgj, Scheme.Hom.comp_apply]
    simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    exact ⟨_, by simpa only [Scheme.Hom.comp_apply] using this.symm⟩
  have hlift : IsOpenImmersion.lift (graphClosureSnd f q U g hg ⁻¹ᵁ h ⁻¹ᵁ j.opensRange).ι
      (toGraphClosure f q U g hg) (by simpa using hO) ≫
      (graphClosureSnd f q U g hg ∣_ h ⁻¹ᵁ j.opensRange) ≫ (h ∣_ j.opensRange) =
      X.homOfLE hUV ≫ j.isoOpensRange.hom := by
    simp [← cancel_mono j.opensRange.ι, ← hgj]
  refine graphClosure_ext f _ hO ?_ ?_
  · simp only [Category.assoc, ← hj, Scheme.Hom.isoOpensRange_inv_comp_assoc,
      morphismRestrict_ι_assoc, hh, graphClosureFst_comp]
  · rw [reassoc_of% hlift]
    simp

include hh hj hgj in
/-- Over the preimage under `h` of the image of `V`, the projection of the graph closure to `P`
is an immersion. -/
theorem isImmersion_graphClosureSnd_restrict [IsSeparated f] :
    IsImmersion (graphClosureSnd f q U g hg ∣_ h ⁻¹ᵁ j.opensRange) := by
  let σ : (h ⁻¹ᵁ j.opensRange).toScheme ⟶ pullback f q :=
    pullback.lift ((h ∣_ j.opensRange) ≫ j.isoOpensRange.inv ≫ V.ι) (h ⁻¹ᵁ j.opensRange).ι
      (by rw [Category.assoc, Category.assoc, ← hj, Scheme.Hom.isoOpensRange_inv_comp_assoc,
        morphismRestrict_ι_assoc, hh])
  have hσ : (graphClosureSnd f q U g hg ∣_ h ⁻¹ᵁ j.opensRange) ≫ σ =
      (graphClosureSnd f q U g hg ⁻¹ᵁ h ⁻¹ᵁ j.opensRange).ι ≫
        (relativeGraph f q U g hg).imageι := by
    refine pullback.hom_ext ?_ ?_
    · simpa [σ, graphClosureFst] using graphClosureSnd_restrict_comp hUV hh hj hgj
    · simp only [σ, Category.assoc, pullback.lift_snd, morphismRestrict_ι]
      rfl
  have : IsImmersion ((graphClosureSnd f q U g hg ∣_ h ⁻¹ᵁ j.opensRange) ≫ σ) := by
    rw [hσ]
    infer_instance
  exact IsImmersion.of_comp _ σ

end Immersion

/-- **The graph closure embeds into `P`.** Suppose that `X` is covered by opens `V i` containing
`U`, each embedded by an open immersion `j i : V i ⟶ P' i` over `S` into a separated `S`-scheme
`P' i`, and that `h i : P ⟶ P' i` are morphisms over `S` with `g ≫ h i` the restriction of `j i`
to `U`. Then the projection of the graph closure to `P` is an immersion. -/
theorem isImmersion_graphClosureSnd [IsSeparated f] {ι : Type*} {V : ι → X.Opens}
    (hV : iSup V = ⊤) (hUV : ∀ i, U ≤ V i) {P' : ι → Scheme.{u}} {q' : ∀ i, P' i ⟶ S}
    [∀ i, IsSeparated (q' i)] {h : ∀ i, P ⟶ P' i} (hh : ∀ i, h i ≫ q' i = q)
    {j : ∀ i, (V i).toScheme ⟶ P' i} [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ i, j i ≫ q' i = (V i).ι ≫ f) (hgj : ∀ i, g ≫ h i = X.homOfLE (hUV i) ≫ j i) :
    IsImmersion (graphClosureSnd f q U g hg) := by
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun _ hi _ hf ↦ by have := hi; have := hf; infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun i ↦ h i ⁻¹ᵁ (j i).opensRange) ?_
    fun i ↦ isImmersion_graphClosureSnd_restrict (hUV i) (hh i) (hj i) (hgj i)
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hV.symm ▸ trivial : graphClosureFst f q U g hg x ∈ iSup V)
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨i, graphClosureFst_preimage_le (hUV i) (hh i) (hj i) (hgj i) hi⟩

end TauCeti.AlgebraicGeometry
