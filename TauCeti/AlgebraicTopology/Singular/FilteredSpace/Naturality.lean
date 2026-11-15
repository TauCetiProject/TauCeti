/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic

/-!
# Naturality of the spectral sequence of a filtered space

Let `X : ℤ → Set Y` and `X' : ℤ → Set Y'` be increasing families of subsets of topological spaces,
and let `φ : Y ⟶ Y'` be a continuous map carrying each `X q` into `X' q`. The map of singular chains
induced by `φ` respects the filtrations of the singular chains by the singular chains of the
`X q` and of the `X' q`, so it induces a morphism of the spectral sequences of the filtered spaces
(`TauCeti.filteredSpaceSpectralSequenceMap`), compatibly with identities and composition. For the
sublevels `X q = {f ≤ a q}` and `X' q = {g ≤ a q}` of functions with `g ∘ φ ≤ f`, this is the
naturality of the spectral sequence of a critical-band filtration.

On the first page, whose object at `(p, q)` is the relative singular homology
`Hₙ(X (q + 1), X q)` with `p + q = -n` (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`), the
morphism is the map on relative singular homology induced by the map of pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` restricting `φ`.

Since the spectral sequences of finite filtrations converge to the singular homology of the
spaces, this gives the **comparison theorem for filtered spaces**: if both filtrations are empty at
a stage `a` and everything at a stage `b`, and `φ` induces isomorphisms
`Hₙ(X (q + 1), X q) ≅ Hₙ(X' (q + 1), X' q)` for every `a ≤ q < b` and every `n`, then `φ` induces
isomorphisms `Hₙ(Y) ≅ Hₙ(Y')` in every degree.

## Main definitions

* `TauCeti.singularChainFiltrationFunctorMap`: the morphism of the functors of the filtrations of
  singular chains induced by `φ`.
* `TauCeti.filteredSpaceSpectralSequenceMap`: the induced morphism of spectral sequences.

## Main results

* `TauCeti.filteredSpaceSpectralSequenceMap_id`, `TauCeti.filteredSpaceSpectralSequenceMap_comp`:
  functoriality.
* `TauCeti.filteredSpaceSpectralSequenceMap_page_two_f_comp_firstPageXIso_hom`: on the first page
  the morphism is the map on the relative singular homology of consecutive stages.
* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap`: the comparison
  theorem.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, Theorem 2.6, the spectral sequence of a
  filtered complex and its naturality.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Comparison Theorem 5.2.12.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y Y' Y'' : TopCat.{w}} {X : ℤ → Set Y} {X' : ℤ → Set Y'} {X'' : ℤ → Set Y''}

/-- The map of singular chains induced by a continuous map `φ` carries the singular chains of a
subset `X q` into those of a subset `X' q`: if `g : X q ⟶ X' q` lifts `φ`, the inclusion of the
singular chains of `X q` followed by `φ` is the map induced by `g`, followed by the inclusion of the
singular chains of `X' q`. -/
@[reassoc]
lemma singularChainFiltrationι_comp_extendMap (φ : Y ⟶ Y') {q : ℤ}
    (g : TopCat.of (X q) ⟶ TopCat.of (X' q)) (hg : ∀ x, (g x : Y') = φ x) :
    singularChainFiltrationι R X q ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat =
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat ≫
        singularChainFiltrationι R X' q := by
  have sq : (TopPair.ofSubset (X q)).map ≫ φ = g ≫ (TopPair.ofSubset (X' q)).map := by
    ext x
    exact (hg x).symm
  rw [singularChainFiltrationι_def, singularChainFiltrationι_def]
  -- The ambient space of the pair `TopPair.ofSubset (X q)` is `Y` only up to unfolding, so the
  -- composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _) <|
    (Functor.map_comp _ _ _).symm.trans <| (congrArg _ <| (Functor.map_comp _ _ _).symm.trans <|
      (congrArg _ sq).trans (Functor.map_comp _ _ _)).trans (Functor.map_comp _ _ _)).trans
    (extendMap_comp _ _ _)

/-- The map of singular chains induced by a continuous map carrying each `X q` into `X' q` sends
each stage of the filtration of the singular chains of `Y` by those of the `X q` into the
corresponding stage of the filtration of the singular chains of `Y'`. -/
lemma singularChainFiltration_factors_comp_extendMap (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (q : ℤ) :
    (singularChainFiltration R X' q).Factors ((singularChainFiltration R X q).arrow ≫
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat) := by
  have hι : singularChainFiltrationι R X' q =
      (singularChainFiltrationIso R X' q).inv ≫ (singularChainFiltration R X' q).arrow := by
    rw [← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Iso.inv_hom_id_assoc]
  rw [← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Category.assoc,
    singularChainFiltrationι_comp_extendMap R φ
      (TopCat.ofHom ⟨(hφ q).restrict, φ.hom.continuous.restrict (hφ q)⟩) fun _ ↦ rfl, hι]
  exact Subobject.factors_of_factors_right _
    (Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _))

variable (hX : Monotone X) (hX' : Monotone X') (hX'' : Monotone X'')

/-- **The morphism of filtrations of singular chains induced by a map of filtered spaces.** A
continuous map `φ : Y ⟶ Y'` carrying each `X q` into `X' q` induces a morphism from the functor of
the filtration of the singular chains of `Y` by those of the `X q` to that of `Y'` by those of the
`X' q`, whose components are restrictions of the map of singular chains induced by `φ`. -/
def singularChainFiltrationFunctorMap (φ : Y ⟶ Y') (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) :
    CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX') :=
  CochainComplex.filtrationFunctorMap _ _
    (extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat)
    (singularChainFiltration_factors_comp_extendMap R φ hφ)

/-- The components of `TauCeti.singularChainFiltrationFunctorMap` are restrictions of the map of
singular chains induced by `φ`. -/
@[reassoc]
lemma singularChainFiltrationFunctorMap_app_comp_filtrationFunctorArrow (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (a : EInt) :
    (singularChainFiltrationFunctorMap R hX hX' φ hφ).app a ≫
        CochainComplex.filtrationFunctorArrow _ (monotone_singularChainFiltration R hX') a =
      CochainComplex.filtrationFunctorArrow _ (monotone_singularChainFiltration R hX) a ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R)
          ComplexShape.embeddingDownNat := by
  rw [singularChainFiltrationFunctorMap]
  exact (CochainComplex.filtrationFunctorMap_app_comp
    (hF := monotone_singularChainFiltration R hX) (hG := monotone_singularChainFiltration R hX')
    _ (singularChainFiltration_factors_comp_extendMap R φ hφ) a).trans (Category.assoc _ _ _).symm

/-- The identity of a filtered space induces the identity of the functor of its filtration of
singular chains. -/
@[simp]
lemma singularChainFiltrationFunctorMap_id (hφ : ∀ q, Set.MapsTo (𝟙 Y) (X q) (X q)) :
    singularChainFiltrationFunctorMap R hX hX (𝟙 Y) hφ = 𝟙 _ := by
  rw [singularChainFiltrationFunctorMap, CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _)
      (by simp),
    CochainComplex.filtrationFunctorMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of functors of
filtrations of singular chains. -/
lemma singularChainFiltrationFunctorMap_comp (φ : Y ⟶ Y') (ψ : Y' ⟶ Y'')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (hψ : ∀ q, Set.MapsTo ψ (X' q) (X'' q))
    (hφψ : ∀ q, Set.MapsTo (φ ≫ ψ) (X q) (X'' q)) :
    singularChainFiltrationFunctorMap R hX hX'' (φ ≫ ψ) hφψ =
      singularChainFiltrationFunctorMap R hX hX' φ hφ ≫
        singularChainFiltrationFunctorMap R hX' hX'' ψ hψ := by
  rw [singularChainFiltrationFunctorMap, singularChainFiltrationFunctorMap,
    singularChainFiltrationFunctorMap, CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R) _ ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map ψ) R) _)
      (by simp),
    CochainComplex.filtrationFunctorMap_comp _ _
      (singularChainFiltration_factors_comp_extendMap R φ hφ)
      (singularChainFiltration_factors_comp_extendMap R ψ hψ)]

/-- **The morphism of spectral sequences of filtered spaces** induced by a continuous map
`φ : Y ⟶ Y'` carrying each `X q` into `X' q`: the morphism from the spectral sequence of the
filtration of `Y` by the `X q` to that of `Y'` by the `X' q` induced by the morphism of filtered
singular chain complexes `TauCeti.singularChainFiltrationFunctorMap`. -/
def filteredSpaceSpectralSequenceMap (φ : Y ⟶ Y') (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R hX' :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (singularChainFiltrationFunctorMap R hX hX' φ hφ))

/-- `TauCeti.filteredSpaceSpectralSequenceMap` is the morphism of spectral sequences of the
morphism of filtered singular chain complexes `TauCeti.singularChainFiltrationFunctorMap`. -/
lemma filteredSpaceSpectralSequenceMap_def (φ : Y ⟶ Y') (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) :
    filteredSpaceSpectralSequenceMap R hX hX' φ hφ =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (singularChainFiltrationFunctorMap R hX hX' φ hφ)) :=
  (rfl)

/-- The identity of a filtered space induces the identity of its spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceMap_id (hφ : ∀ q, Set.MapsTo (𝟙 Y) (X q) (X q)) :
    filteredSpaceSpectralSequenceMap R hX hX (𝟙 Y) hφ = 𝟙 _ := by
  rw [filteredSpaceSpectralSequenceMap_def, singularChainFiltrationFunctorMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of their
spectral sequences. -/
lemma filteredSpaceSpectralSequenceMap_comp (φ : Y ⟶ Y') (ψ : Y' ⟶ Y'')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (hψ : ∀ q, Set.MapsTo ψ (X' q) (X'' q))
    (hφψ : ∀ q, Set.MapsTo (φ ≫ ψ) (X q) (X'' q)) :
    filteredSpaceSpectralSequenceMap R hX hX'' (φ ≫ ψ) hφψ =
      filteredSpaceSpectralSequenceMap R hX hX' φ hφ ≫
        filteredSpaceSpectralSequenceMap R hX' hX'' ψ hψ := by
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceSpectralSequenceMap_def,
    filteredSpaceSpectralSequenceMap_def,
    singularChainFiltrationFunctorMap_comp R hX hX' hX'' φ ψ hφ hψ hφψ,
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]

/-- At an integer stage `b`, the component of `TauCeti.singularChainFiltrationFunctorMap`, read on
the singular chains of `X b` and `X' b`, is the map induced by any map `g : X b ⟶ X' b` lifting
`φ`. -/
private lemma app_comp_singularChainFiltrationIso_hom (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (b : ℤ) (g : TopCat.of (X b) ⟶ TopCat.of (X' b))
    (hg : ∀ x, (g x : Y') = φ x) :
    (singularChainFiltrationFunctorMap R hX hX' φ hφ).app b ≫
        (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (singularChainFiltrationIso R X' b).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫
            extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R)
              ComplexShape.embeddingDownNat := by
  -- The source of the inclusion of the singular chains of `X b` is the singular chain complex of
  -- the subspace `X b` only up to unfolding, so the composite with it is rearranged by `exact`.
  have hR : ((CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
      Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
        (singularChainFiltrationIso R X b).hom ≫
          extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R)
            ComplexShape.embeddingDownNat) ≫ singularChainFiltrationι R X' b =
      (CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) b).hom ≫
        (CochainComplex.filtrationEInt _ b).arrow ≫
          extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R)
            ComplexShape.embeddingDownNat :=
    (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
      ((Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (singularChainFiltrationι_comp_extendMap R φ g hg).symm).trans
            (singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc R X b _)).trans
        (Subobject.ofLE_arrow_assoc _ _)
  refine (cancel_mono (singularChainFiltrationι R X' b)).1 (Eq.trans ?_ hR.symm)
  simp only [Category.assoc, singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
    Subobject.ofLE_arrow]
  simpa only [Category.assoc] using
    singularChainFiltrationFunctorMap_app_comp_filtrationFunctorArrow R hX hX' φ hφ b

/-- The identification `TauCeti.singularChainFiltrationFunctorCokernelIso` of the graded pieces
of the filtration of singular chains with relative singular chains is natural: the morphism of
graded pieces induced by `TauCeti.singularChainFiltrationFunctorMap` is the map of relative
singular chains induced by the map of pairs `(X b, X a) ⟶ (X' b, X' a)` restricting `φ`. -/
@[reassoc]
lemma cokernel_map_comp_singularChainFiltrationFunctorCokernelIso_hom
    (φ : Y ⟶ Y') (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ ((singularChainFiltrationFunctorMap R hX hX' φ hφ).app a)
        ((singularChainFiltrationFunctorMap R hX hX' φ hφ).app b)
        ((singularChainFiltrationFunctorMap R hX hX' φ hφ).naturality f) ≫
        (singularChainFiltrationFunctorCokernelIso R hX' f).hom =
      (singularChainFiltrationFunctorCokernelIso R hX f).hom ≫
        extendMap (TopPair.singularChainComplexMap
          (TopPair.ofInclusionMap (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))
            (hX' (WithBotTop.coe_le_coe.mp (leOfHom f)))
            ⟨(hφ b).restrict, φ.hom.continuous.restrict (hφ b)⟩ fun _ hx ↦ hφ a hx) R)
          ComplexShape.embeddingDownNat := by
  -- `pm` is the map of pairs `(X b, X a) ⟶ (X' b, X' a)` restricting `φ`.
  let pm := TopPair.ofInclusionMap (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))
    (hX' (WithBotTop.coe_le_coe.mp (leOfHom f)))
    ⟨(hφ b).restrict, φ.hom.continuous.restrict (hφ b)⟩ fun _ hx ↦ hφ a hx
  have key := app_comp_singularChainFiltrationIso_hom R hX hX' φ hφ b (TopPair.Hom.fst pm)
    fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply
      (hst := hX (WithBotTop.coe_le_coe.mp (leOfHom f)))
      (hst' := hX' (WithBotTop.coe_le_coe.mp (leOfHom f))) _ (fun _ hx ↦ hφ a hx) x)
  have hπ : extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst pm)) R)
        ComplexShape.embeddingDownNat ≫
        extendMap ((TopPair.ofInclusion
          (hX' (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
          ComplexShape.embeddingDownNat =
      extendMap ((TopPair.ofInclusion
          (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
          ComplexShape.embeddingDownNat ≫
        extendMap (TopPair.singularChainComplexMap pm R) ComplexShape.embeddingDownNat :=
    (extendMap_comp _ _ _).symm.trans ((congrArg (extendMap · _)
      (TopPair.singularChainComplexπ_pair_naturality pm R)).trans (extendMap_comp _ _ _))
  rw [← cancel_epi (cokernel.π _), cokernel.π_desc_assoc, Category.assoc,
    π_singularChainFiltrationFunctorCokernelIso_hom,
    π_singularChainFiltrationFunctorCokernelIso_hom_assoc]
  -- The composites below change the presentation of the singular chain complex of `X b`, so they
  -- are reassociated by explicit terms rather than `rw`.
  exact ((reassoc_of% key) _).trans <| (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
    (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hπ).trans (Category.assoc _ _ _).symm

open CochainComplex in
/-- **The morphism of spectral sequences of filtered spaces on the first page.** Under the
identifications `TauCeti.filteredSpaceSpectralSequenceFirstPageXIso` of the objects at `(p, q)` of
the first pages with the relative singular homology `Hₙ(X (q + 1), X q)` and
`Hₙ(X' (q + 1), X' q)`, where `p + q = -n`, the morphism induced by `φ` is the map on relative
singular homology induced by the map of pairs restricting `φ`. -/
@[reassoc]
theorem filteredSpaceSpectralSequenceMap_page_two_f_comp_firstPageXIso_hom (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceSpectralSequenceMap R hX hX' φ hφ).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX' pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        TopPair.singularHomologyMap (TopPair.ofInclusionMap (hX (by lia : a ≤ b))
          (hX' (by lia : a ≤ b)) ⟨(hφ b).restrict, φ.hom.continuous.restrict (hφ b)⟩
          fun _ hx ↦ hφ a hx) R n := by
  rw [filteredSpaceSpectralSequenceFirstPageXIso_hom,
    filteredSpaceSpectralSequenceFirstPageXIso_hom, filteredSpaceSpectralSequenceMap_def,
    spectralSequenceMap_page_two_f_comp_spectralSequenceFirstPageXIsoCokernel_hom_assoc,
    ← homologyMap_comp_assoc,
    cokernel_map_comp_singularChainFiltrationFunctorCokernelIso_hom,
    homologyMap_comp_assoc, Category.assoc, Category.assoc]
  -- The pairs `(X' b, X' a)` in the two sides differ by the proof of `X' a ⊆ X' b`, so the
  -- naturality of the reindexing of homology is applied up to proof irrelevance by `exact`.
  exact congrArg (_ ≫ _ ≫ ·) (extendHomologyIso_hom_naturality _ _ hn.symm)

/-- Outside the stages `a ≤ q < b` of a filtration that is empty at `a` and everything at `b`,
consecutive stages agree. -/
private lemma succ_subset_of_not_le_and_lt {Z : Type*} {W : ℤ → Set Z} (hW : Monotone W) {a b q : ℤ}
    (ha : W a = ∅) (hb : W b = Set.univ) (hq : ¬(a ≤ q ∧ q < b)) : W (q + 1) ⊆ W q := by
  rcases lt_or_ge q a with hqa | hbq
  · exact (hW (by lia : q + 1 ≤ a)).trans (ha ▸ Set.empty_subset _)
  · exact fun _ _ ↦ hW (not_lt.mp fun h ↦ hq ⟨hbq, h⟩) (hb ▸ Set.mem_univ _)

/-- The map of singular chains induced by a map of filtered spaces is a quasi-isomorphism in
degree `n` as soon as its restriction to the top stages of the filtrations is a
quasi-isomorphism in degree `-n` of the reindexed complexes. -/
private lemma isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (n : ℕ)
    (h : IsIso (homologyMap ((singularChainFiltrationFunctorMap R hX hX' φ hφ).app ⊤) (-n))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map φ) := by
  have : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X') ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  -- The top stages of the filtrations are the whole complexes, so the identity
  -- `α_⊤ ≫ ι' = ι ≫ φ_*` of `singularChainFiltrationFunctorMap_app_comp_filtrationFunctorArrow`
  -- has isomorphisms `ι` and `ι'`.
  have hC : IsIso (homologyMap (CochainComplex.filtrationFunctorArrow _
      (monotone_singularChainFiltration R hX) ⊤ ≫ extendMap
        (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat) (-n)) := by
    rw [← singularChainFiltrationFunctorMap_app_comp_filtrationFunctorArrow R hX hX' φ hφ ⊤,
      homologyMap_comp]
    infer_instance
  rw [homologyMap_comp] at hC
  have := IsIso.of_isIso_comp_left (homologyMap (CochainComplex.filtrationFunctorArrow _
    (monotone_singularChainFiltration R hX) ⊤) (-n)) (homologyMap (extendMap
      (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat) (-n))
  rw [singularHomologyFunctor_obj_map]
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIsoAt_extendMap_iff _ _ rfl).1
    ((quasiIsoAt_iff_isIso_homologyMap _ _).2 this))

/-- **The comparison theorem for filtered spaces.** Let `X` and `X'` be finite increasing
filtrations of spaces `Y` and `Y'`, empty at a stage `a` and everything at a stage `b`, and let
`φ : Y ⟶ Y'` carry each `X q` into `X' q`. If for every `a ≤ q < b` the map of pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` restricting `φ` induces isomorphisms on relative singular
homology in every degree, then `φ` induces isomorphisms on singular homology in every degree. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) {a b : ℤ} (ha : X a = ∅) (ha' : X' a = ∅)
    (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n, IsIso (TopPair.singularHomologyMap
      (TopPair.ofInclusionMap (hX (Int.le_add_one le_rfl)) (hX' (Int.le_add_one le_rfl))
        ⟨(hφ (q + 1)).restrict, φ.hom.continuous.restrict (hφ (q + 1))⟩ fun _ hx ↦ hφ q hx) R n))
    (n : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map φ) := by
  refine isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top R hX hX' φ hφ n ?_
  refine CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page _
    (monotone_singularChainFiltration R hX) _ (monotone_singularChainFiltration R hX')
    (singularChainFiltrationFunctorMap R hX hX' φ hφ) (singularChainFiltration_eq_bot R ha)
    (singularChainFiltration_eq_bot R ha') (singularChainFiltration_eq_top R hb)
    (singularChainFiltration_eq_top R hb') 2 le_rfl (fun pq ↦ ?_) (-n)
  rw [← filteredSpaceSpectralSequenceMap_def]
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isIso_of_source_target_iso_zero _
      (isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos).isoZero
      (isZero_filteredSpaceSpectralSequence_page_two_X R hX' pq hpos).isoZero
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hle
  rw [(Iso.eq_comp_inv _).2 (filteredSpaceSpectralSequenceMap_page_two_f_comp_firstPageXIso_hom
    R hX hX' φ hφ pq pq.2 (pq.2 + 1) rfl rfl _ rfl k hk)]
  have : IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (hX (Int.le_add_one le_rfl))
      (hX' (Int.le_add_one le_rfl)) ⟨(hφ (pq.2 + 1)).restrict,
        φ.hom.continuous.restrict (hφ (pq.2 + 1))⟩ fun _ hx ↦ hφ pq.2 hx) R k) := by
    by_cases hq : a ≤ pq.2 ∧ pq.2 < b
    · exact h pq.2 hq.1 hq.2 k
    · exact isIso_of_source_target_iso_zero _
        (TopPair.isZero_singularHomology_of_surjective_map
          (TopPair.ofInclusion (hX (Int.le_add_one le_rfl))) R (fun (y : X (pq.2 + 1)) ↦
            ⟨(⟨y.1, succ_subset_of_not_le_and_lt hX ha hb hq y.2⟩ : X pq.2), rfl⟩) k).isoZero
        (TopPair.isZero_singularHomology_of_surjective_map
          (TopPair.ofInclusion (hX' (Int.le_add_one le_rfl))) R (fun (y : X' (pq.2 + 1)) ↦
            ⟨(⟨y.1, succ_subset_of_not_le_and_lt hX' ha' hb' hq y.2⟩ : X' pq.2), rfl⟩) k).isoZero
  infer_instance

end TauCeti
