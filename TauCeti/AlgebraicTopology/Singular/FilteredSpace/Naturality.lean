/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Order.Sublevel

/-!
# Naturality of the spectral sequence of a filtered space

Let `X : ℤ → Set Y` and `X' : ℤ → Set Y'` be increasing families of subsets of topological spaces,
and let `g : Y ⟶ Y'` be a continuous map carrying each `X q` into `X' q`. Then `g` induces a
morphism from the spectral sequence of the filtered space `(Y, X)` to that of `(Y', X')`
(`TauCeti.filteredSpaceSpectralSequenceMap`), functorially in `g`. It is the morphism of
spectral sequences of filtered complexes induced by the singular chain map of `g`, which sends the
singular chains of `X q` into those of `X' q`.

On the first page, whose object at `(p, q)` is the relative singular homology
`Hₙ(X (q + 1), X q)` with `p + q = -n` (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`),
this morphism is the map induced in relative homology by the map of pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` that `g` restricts to (`TauCeti.filteredSpacePairMap`).

The comparison theorem follows: if both filtrations are finite, empty at an index `a` and the
whole space at an index `b`, and `g` induces isomorphisms on the relative singular homology of the
pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` for `a ≤ q < b`, then `g` induces isomorphisms on
the singular homology of `Y` and `Y'`
(`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_filteredSpacePairMap`).

For the sublevel filtration `X q = {f ≤ v q}` of a function `f : Y → ℝ` cut at increasing values
`v q`, such as the critical-band filtration of a Morse or Morse–Bott function, a map `g` with
`f' ∘ g ≤ f` carries each sublevel of `f` into the sublevel of `f'` at the same value. So the
spectral sequence of the critical-band filtration is natural for such maps, and when both
functions take their values in `(v a, v b]`, a map which is an isomorphism on the relative
homology of every band is an isomorphism in homology
(`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_sublevelPair`).

## Main definitions

* `TauCeti.filteredSpaceSpectralSequenceMap`: the morphism of spectral sequences induced by a map
  of filtered spaces.
* `TauCeti.filteredSpacePairMap`: the map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by a map
  of filtered spaces.

## Main results

* `TauCeti.filteredSpaceSpectralSequenceMap_id`, `TauCeti.filteredSpaceSpectralSequenceMap_comp`:
  functoriality.
* `TauCeti.filteredSpaceSpectralSequenceMap_hom_two_f_comp_firstPageXIso_hom`: on the first page
  the morphism is the map in relative singular homology of the pairs of the filtrations.
* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_filteredSpacePairMap`: the comparison
  theorem for finite filtrations of spaces.
* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_sublevelPair`: its form for sublevel
  filtrations.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 3.4, the morphism of spectral sequences induced by a morphism of
  filtered complexes and the comparison theorem.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorems 15.6–15.7, the spectral sequence of the critical-band filtration.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y Y' Y'' : TopCat.{w}} {X : ℤ → Set Y} {X' : ℤ → Set Y'} {X'' : ℤ → Set Y''}

section Chains

/-- The singular chain map of `g`, reindexed as a map of cochain complexes in nonpositive
degrees along `n ↦ -n`. -/
private abbrev chainMap (g : Y ⟶ Y') :
    ((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat ⟶
      ((TopCat.toSSet.obj Y').chainComplex R).extend ComplexShape.embeddingDownNat :=
  extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat

/-- The singular chain map of `g` sends the chains of `X q` into those of `X' q`. -/
private lemma extendMap_restrict_comp_singularChainFiltrationι (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (q : ℤ) :
    extendMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)))) R)
        ComplexShape.embeddingDownNat ≫ singularChainFiltrationι R X' q =
      singularChainFiltrationι R X q ≫ chainMap R g := by
  have hw : TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)) ≫ (TopPair.ofSubset (X' q)).map =
      (TopPair.ofSubset (X q)).map ≫ g := by
    rw [TopPair.Hom.w, TopPair.ofSubsetMap_fst]
    -- both sides are `(TopPair.ofSubset (X q)).map ≫ g`, composed through `Y` written two ways
    rfl
  -- the subspace inclusions land in `Y` and `Y'` only up to unfolding `TopPair.ofSubset`, so the
  -- composites are formed in term mode rather than by rewriting
  have h : SSet.chainComplexMap
        (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)))) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X' q)).map) R =
      SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map g) R :=
    ((TopCat.toSSet ⋙ (SSet.chainComplexFunctor A).obj R).map_comp _ _).symm.trans <|
      ((TopCat.toSSet ⋙ (SSet.chainComplexFunctor A).obj R).congr_map hw).trans
        ((TopCat.toSSet ⋙ (SSet.chainComplexFunctor A).obj R).map_comp
          (TopPair.ofSubset (X q)).map g)
  rw [singularChainFiltrationι_def, singularChainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _) h).trans
    (extendMap_comp _ _ _)

private lemma arrow_comp_chainMap (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (q : ℤ) :
    (singularChainFiltration R X q).arrow ≫ chainMap R g =
      ((singularChainFiltrationIso R X q).hom ≫ extendMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)))) R)
        ComplexShape.embeddingDownNat ≫ (singularChainFiltrationIso R X' q).inv) ≫
        (singularChainFiltration R X' q).arrow := by
  rw [← singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
    ← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Category.assoc,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    extendMap_restrict_comp_singularChainFiltrationι]

private lemma factors_singularChainFiltration (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q))
    (q : ℤ) :
    (singularChainFiltration R X' q).Factors
      ((singularChainFiltration R X q).arrow ≫ chainMap R g) := by
  rw [arrow_comp_chainMap R g hg q]
  exact Subobject.factors_comp_arrow _

/-- The morphism of filtration functors of singular chains induced by `g`. -/
private abbrev filtrationFunctorMap (hX : Monotone X) (hX' : Monotone X') (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) :
    CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX') :=
  CochainComplex.filtrationFunctorMap _ _ (chainMap R g) (factors_singularChainFiltration R g hg)

/-- **Naturality of the spectral sequence of a filtered space.** A continuous map `g : Y ⟶ Y'`
carrying each `X q` into `X' q` induces a morphism from the spectral sequence of the filtration
`X` of `Y` to that of the filtration `X'` of `Y'`: the morphism of spectral sequences of filtered
complexes induced by the singular chain map of `g`. -/
def filteredSpaceSpectralSequenceMap (hX : Monotone X) (hX' : Monotone X') (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R hX' :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (filtrationFunctorMap R hX hX' g hg))

/-- The identity of a filtered space induces the identity of its spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceMap_id (hX : Monotone X)
    (hg : ∀ q, Set.MapsTo (𝟙 Y) (X q) (X q)) :
    filteredSpaceSpectralSequenceMap R hX hX (𝟙 Y) hg = 𝟙 _ := by
  have e : chainMap R (𝟙 Y) = 𝟙 _ := by
    simp only [chainMap, CategoryTheory.Functor.map_id, extendMap_id]
  rw [filteredSpaceSpectralSequenceMap, filtrationFunctorMap,
    CochainComplex.filtrationFunctorMap_congr e, CochainComplex.filtrationFunctorMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of spectral
sequences. Not `@[simp]`: the intermediate filtration cannot be inferred from the left-hand
side. -/
lemma filteredSpaceSpectralSequenceMap_comp (hX : Monotone X) (hX' : Monotone X')
    (hX'' : Monotone X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') (hg : ∀ q, Set.MapsTo g (X q) (X' q))
    (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q)) (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceSpectralSequenceMap R hX hX'' (g ≫ g') hgg' =
      filteredSpaceSpectralSequenceMap R hX hX' g hg ≫
        filteredSpaceSpectralSequenceMap R hX' hX'' g' hg' := by
  have e : chainMap R (g ≫ g') = chainMap R g ≫ chainMap R g' := by
    simp only [chainMap, CategoryTheory.Functor.map_comp, extendMap_comp]
  rw [filteredSpaceSpectralSequenceMap, filteredSpaceSpectralSequenceMap,
    filteredSpaceSpectralSequenceMap, filtrationFunctorMap, filtrationFunctorMap,
    filtrationFunctorMap, CochainComplex.filtrationFunctorMap_congr e,
    CochainComplex.filtrationFunctorMap_comp _ _ (factors_singularChainFiltration R g hg)
      (factors_singularChainFiltration R g' hg'),
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]

/-- The map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by a map `g` carrying each `X q` into
`X' q`. -/
def filteredSpacePairMap (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q)) {a b : ℤ}
    (hab : X a ⊆ X b) (hab' : X' a ⊆ X' b) :
    TopPair.ofInclusion hab ⟶ TopPair.ofInclusion hab' :=
  TopPair.ofInclusionMap hab hab' ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩
    fun _ hx ↦ hg a hx

/-- On the ambient spaces, the map of pairs `filteredSpacePairMap g hg` is `g`. -/
@[simp]
lemma filteredSpacePairMap_fst_apply (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q))
    {a b : ℤ} (hab : X a ⊆ X b) (hab' : X' a ⊆ X' b) (x : X b) :
    TopPair.Hom.fst (filteredSpacePairMap g hg hab hab') x = ⟨g x, hg b x.2⟩ :=
  TopPair.ofInclusionMap_fst_apply _ _ x

/-- The map of pairs `filteredSpacePairMap g hg` is the restriction of `g` to the ambient spaces
`X b ⟶ X' b`. -/
lemma filteredSpacePairMap_fst (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q)) {a b : ℤ}
    (hab : X a ⊆ X b) (hab' : X' a ⊆ X' b) :
    TopPair.Hom.fst (filteredSpacePairMap g hg hab hab') =
      TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)) := by
  ext x : 2
  exact (filteredSpacePairMap_fst_apply g hg hab hab' x).trans
    (Subtype.ext (TopPair.ofSubsetMap_snd_apply g (hg b) x).symm)

end Chains

section FirstPage

variable (hX : Monotone X) (hX' : Monotone X') (g : Y ⟶ Y')
  (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- Under the identifications of the stages `F_b` of the filtrations with the singular chains of
`X b` and `X' b`, the morphism of filtration functors induced by `g` is the singular chain map of
the restriction `X b ⟶ X' b` of `g`. -/
private lemma app_comp_singularChainFiltrationIso_hom (b : ℤ) :
    (filtrationFunctorMap R hX hX' g hg).app (b : EInt) ≫
        (CochainComplex.filtrationFunctorObjIso _ _ (b : EInt)).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (singularChainFiltrationIso R X' b).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ (b : EInt)).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫
            extendMap (SSet.chainComplexMap
              (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) R)
              ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (singularChainFiltrationι R X' b)]
  simp only [Category.assoc, singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
    Subobject.ofLE_arrow, extendMap_restrict_comp_singularChainFiltrationι,
    singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc,
    Subobject.ofLE_arrow_assoc]
  exact CochainComplex.filtrationFunctorMap_app_comp _ _ _

/-- Under the identifications of the graded pieces `F_b / F_a` with relative singular chains, the
morphism of cokernels induced by `g` is the relative singular chain map of the map of pairs
`(X b, X a) ⟶ (X' b, X' a)`. -/
private lemma cokernel_map_comp_singularChainFiltrationFunctorCokernelIso_hom {a b : ℤ}
    (hab : a ≤ b) :
    cokernel.map _ _ ((filtrationFunctorMap R hX hX' g hg).app a)
        ((filtrationFunctorMap R hX hX' g hg).app b)
        ((filtrationFunctorMap R hX hX' g hg).naturality (eIntHomOfLE hab)) ≫
        (singularChainFiltrationFunctorCokernelIso R hX' (eIntHomOfLE hab)).hom =
      (singularChainFiltrationFunctorCokernelIso R hX (eIntHomOfLE hab)).hom ≫
        extendMap (TopPair.singularChainComplexMap
          (filteredSpacePairMap g hg (hX hab) (hX' hab)) R) ComplexShape.embeddingDownNat := by
  have hπ := TopPair.singularChainComplexπ_pair_naturality
    (filteredSpacePairMap g hg (hX hab) (hX' hab)) R
  rw [filteredSpacePairMap_fst] at hπ
  have hπ' := (congrArg ((singularChainFiltrationIso R X b).hom ≫ ·)
    ((extendMap_comp _ _ _).symm.trans ((congrArg (extendMap · ComplexShape.embeddingDownNat)
      hπ).trans (extendMap_comp _ _ _)))).trans (Category.assoc _ _ _).symm
  rw [← cancel_epi (cokernel.π _), cokernel.π_desc_assoc, Category.assoc,
    π_singularChainFiltrationFunctorCokernelIso_hom,
    π_singularChainFiltrationFunctorCokernelIso_hom_assoc]
  -- the pairs of the filtrations carry proofs of `X a ⊆ X b` which only agree up to proof
  -- irrelevance, so the composites are compared in term mode rather than by rewriting
  exact ((reassoc_of% (app_comp_singularChainFiltrationIso_hom R hX hX' g hg b)) _).trans <|
    (congrArg ((CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX)
      (b : EInt)).hom ≫
      Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫ ·) hπ')

/-- **The first page of the morphism of spectral sequences of filtered spaces.** Under the
identifications of the first pages with relative singular homology, the morphism induced by a map
`g` carrying each `X q` into `X' q` is, at `(p, q)`, the map in relative singular homology of the
map of pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` induced by `g`, where `p + q = -n`. -/
theorem filteredSpaceSpectralSequenceMap_hom_two_f_comp_firstPageXIso_hom (pq : ℤ × ℤ)
    (a b : ℤ) (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ)
    (hn : m = -n) :
    ((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX' pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        TopPair.singularHomologyMap
          (filteredSpacePairMap g hg (hX (by lia : a ≤ b)) (hX' (by lia : a ≤ b))) R n := by
  rw [filteredSpaceSpectralSequenceFirstPageXIso_hom,
    filteredSpaceSpectralSequenceFirstPageXIso_hom, filteredSpaceSpectralSequenceMap,
    CochainComplex.spectralSequenceMap_hom_two_f_comp_firstPageXIsoCokernel_hom_assoc,
    Category.assoc, Category.assoc, ← HomologicalComplex.homologyMap_comp_assoc,
    cokernel_map_comp_singularChainFiltrationFunctorCokernelIso_hom R hX hX' g hg
      (by lia : a ≤ b),
    HomologicalComplex.homologyMap_comp_assoc]
  -- the relative chains of the pair `(X' b, X' a)` appear with two proofs of `X' a ⊆ X' b`, so the
  -- naturality of `extendHomologyIso` is applied with `exact` rather than `rw`
  exact congrArg (fun φ ↦ _ ≫ _ ≫ φ) (extendHomologyIso_hom_naturality _ _ _)

end FirstPage

section Comparison

variable (hX : Monotone X) (hX' : Monotone X') (g : Y ⟶ Y')
  (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- If `g` induces isomorphisms on the relative singular homology of the pairs of the filtrations,
the morphism of spectral sequences it induces is an isomorphism on the first page. -/
private lemma isIso_filteredSpaceSpectralSequenceMap_hom_two_f
    (h : ∀ (q : ℤ) (n : ℕ), IsIso (TopPair.singularHomologyMap
      (filteredSpacePairMap g hg (hX (by lia : q ≤ q + 1)) (hX' (by lia : q ≤ q + 1))) R n))
    (pq : ℤ × ℤ) :
    IsIso (((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq) := by
  by_cases hpos : 0 < pq.1 + pq.2
  · exact isIso_of_source_target_iso_zero _
      (isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos).isoZero
      (isZero_filteredSpaceSpectralSequence_page_two_X R hX' pq hpos).isoZero
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, pq.1 + pq.2 = -n := ⟨(-(pq.1 + pq.2)).toNat, by lia⟩
    have e := filteredSpaceSpectralSequenceMap_hom_two_f_comp_firstPageXIso_hom R hX hX' g hg pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl n hn
    rw [← Iso.eq_comp_inv] at e
    have := h pq.2 n
    rw [e]
    infer_instance

/-- Outside the indices `a ≤ q < b` of a filtration which is empty at `a` and everything at `b`,
consecutive stages agree. -/
private lemma eq_of_lt_or_le {X : ℤ → Set Y} (hX : Monotone X) {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) {q : ℤ} (hq : ¬(a ≤ q ∧ q < b)) : X (q + 1) = X q := by
  rcases lt_or_ge q a with hqa | hqa
  · rw [Set.eq_empty_of_subset_empty ((hX (by lia : q + 1 ≤ a)).trans ha.le),
      Set.eq_empty_of_subset_empty ((hX hqa.le).trans ha.le)]
  · rw [Set.eq_univ_of_univ_subset (hb.symm.subset.trans (hX (by lia : b ≤ q + 1))),
      Set.eq_univ_of_univ_subset (hb.symm.subset.trans (hX (by lia : b ≤ q)))]

/-- A pair `(X (q + 1), X q)` of equal consecutive stages has no relative homology. -/
private lemma isZero_singularHomology_ofInclusion_of_eq {q : ℤ} (hq : X (q + 1) = X q) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (hX (by lia : q ≤ q + 1))).singularHomology R n) :=
  (TopPair.isZero_singularHomology_ofInclusion_congr R _ (subset_refl (X q)) hq rfl n).2
    (TopPair.isZero_singularHomology_ofInclusion_self R _ n)

/-- The top stages of the filtrations are the whole singular chain complexes, on which the
morphism of filtration functors induced by `g` is the singular chain map of `g`. So an isomorphism
in cohomology there is an isomorphism in singular homology. -/
private lemma isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top (n : ℕ)
    (hα : IsIso (HomologicalComplex.homologyMap ((filtrationFunctorMap R hX hX' g hg).app ⊤)
      (-n : ℤ))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  have hX₀ : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have hX₀' : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X') ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have hcomm := congrArg (HomologicalComplex.homologyMap · (-n : ℤ))
    (CochainComplex.filtrationFunctorMap_app_comp (hF := monotone_singularChainFiltration R hX)
      (hG := monotone_singularChainFiltration R hX') _ (factors_singularChainFiltration R g hg) ⊤)
  simp only [HomologicalComplex.homologyMap_comp] at hcomm
  have : IsIso (HomologicalComplex.homologyMap
      ((CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) ⊤).hom ≫
        (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow) (-n : ℤ) ≫
      HomologicalComplex.homologyMap (chainMap R g) (-n : ℤ)) := by
    rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← hcomm]
    infer_instance
  have hg' : IsIso (HomologicalComplex.homologyMap (chainMap R g) (-n : ℤ)) :=
    IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
      ((CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) ⊤).hom ≫
        (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow) (-n : ℤ)) _
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 <|
    (quasiIsoAt_extendMap_iff (SSet.chainComplexMap (TopCat.toSSet.map g) R)
      ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)).1
        ((quasiIsoAt_iff_isIso_homologyMap _ _).2 hg')

/-- **The comparison theorem for filtered spaces.** Let `X` and `X'` be finite filtrations of `Y`
and `Y'`, empty at the index `a` and everything at the index `b`, and let `g : Y ⟶ Y'` carry each
`X q` into `X' q`. If `g` induces isomorphisms on the relative singular homology of the pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` for `a ≤ q < b` in every degree, then it induces
isomorphisms on the singular homology of `Y` and `Y'`. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_filteredSpacePairMap {a b : ℤ}
    (ha : X a = ∅) (ha' : X' a = ∅) (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ, IsIso (TopPair.singularHomologyMap
      (filteredSpacePairMap g hg (hX (by lia : q ≤ q + 1)) (hX' (by lia : q ≤ q + 1))) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  have h' (q : ℤ) (n : ℕ) : IsIso (TopPair.singularHomologyMap
      (filteredSpacePairMap g hg (hX (by lia : q ≤ q + 1)) (hX' (by lia : q ≤ q + 1))) R n) := by
    by_cases hq : a ≤ q ∧ q < b
    · exact h q hq.1 hq.2 n
    · exact isIso_of_source_target_iso_zero _
        (isZero_singularHomology_ofInclusion_of_eq R hX (eq_of_lt_or_le hX ha hb hq) n).isoZero
        (isZero_singularHomology_ofInclusion_of_eq R hX' (eq_of_lt_or_le hX' ha' hb' hq) n).isoZero
  have hα := CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page _
    (monotone_singularChainFiltration R hX) _ (monotone_singularChainFiltration R hX')
    (filtrationFunctorMap R hX hX' g hg) (singularChainFiltration_eq_bot R ha)
    (singularChainFiltration_eq_bot R ha') (singularChainFiltration_eq_top R hb)
    (singularChainFiltration_eq_top R hb') 2 le_rfl
    (isIso_filteredSpaceSpectralSequenceMap_hom_two_f R hX hX' g hg h') (-n)
  exact isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top R hX hX' g hg n hα

end Comparison

section Sublevel

variable (g : Y ⟶ Y') {f : Y → ℝ} {f' : Y' → ℝ} (hgf : ∀ y, f' (g y) ≤ f y)

/-- **Comparison of sublevel filtrations.** Let `f : Y → ℝ` and `f' : Y' → ℝ`, and let
`g : Y ⟶ Y'` satisfy `f' ∘ g ≤ f`, so that `g` carries each sublevel `{f ≤ c}` into
`{f' ≤ c}`. Cut both functions at the values of a monotone `v : ℤ → ℝ`, with all values of `f`
and `f'` in `(v a, v b]`. If `g` induces isomorphisms on the relative singular homology of the
sublevel pairs `({f ≤ v (q + 1)}, {f ≤ v q}) ⟶ ({f' ≤ v (q + 1)}, {f' ≤ v q})` for `a ≤ q < b` in
every degree,
for instance of the critical bands of two Morse–Bott functions, then it induces isomorphisms on
singular homology. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_sublevelPair {v : ℤ → ℝ} (hv : Monotone v)
    {a b : ℤ} (ha : ∀ y, v a < f y) (ha' : ∀ y, v a < f' y) (hb : ∀ y, f y ≤ v b)
    (hb' : ∀ y, f' y ≤ v b)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ, IsIso (TopPair.singularHomologyMap
      (filteredSpacePairMap (X := fun q ↦ {y | f y ≤ v q}) (X' := fun q ↦ {y | f' y ≤ v q}) g
        (fun _ _ hy ↦ (hgf _).trans hy) (sublevel_mono f (hv (by lia : q ≤ q + 1)))
        (sublevel_mono f' (hv (by lia : q ≤ q + 1)))) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) :=
  isIso_singularHomologyFunctor_map_of_isIso_filteredSpacePairMap R ((sublevel_mono f).comp hv)
    ((sublevel_mono f').comp hv) g (fun _ _ hy ↦ (hgf _).trans hy)
    (Set.eq_empty_of_forall_notMem fun y hy ↦ (ha y).not_ge hy)
    (Set.eq_empty_of_forall_notMem fun y hy ↦ (ha' y).not_ge hy)
    (Set.eq_univ_of_forall hb) (Set.eq_univ_of_forall hb') h n

end Sublevel

end TauCeti
