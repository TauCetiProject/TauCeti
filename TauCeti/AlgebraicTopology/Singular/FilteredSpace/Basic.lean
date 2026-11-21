/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor
public import TauCeti.AlgebraicTopology.Singular.Triple
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular chains of the `X q`
form an increasing filtration of the singular chains of `Y`
(`TauCeti.chainFiltration`), and this file studies the spectral sequence of that filtered
complex (`TauCeti.filteredSpaceSpectralSequence`). It is the spectral sequence of a filtered
complex from `TauCeti.Algebra.Homology.SpectralSequence.Filtered`, which uses cochain complexes
indexed by `ℤ`, so singular chains in degree `n` are placed in degree `-n` along
`ComplexShape.embeddingDownNat`.

The filtration itself (`TauCeti.chainFiltration`), the identification of its stages with the
chains of the `X q` (`TauCeti.chainFiltrationIso`), its extreme stages, its graded pieces, its
first page and the abutment (`TauCeti.chainFiltrationAbutmentIso`) are built in
`TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor` for any functor `F` from spaces to
chain complexes sending subspace inclusions to monomorphisms, so that they apply to singular and
to cubical chains alike. So is the morphism of filtrations induced by a natural transformation
`F ⟶ G` together with a map of filtered spaces (`TauCeti.chainFiltrationMap`), which is a
quasi-isomorphism on every stage when the natural transformation is a quasi-isomorphism on every
space (`TauCeti.quasiIso_chainFiltrationMap_app`). This file is the instance for simplicial
singular chains.

* **Graded pieces.** The quotient `F_b / F_a` of two stages of the filtration is the relative
  singular chain complex of the pair `(X b, X a)` (`TauCeti.singularChainFiltrationCokernelIso`),
  because the singular chain sequence of a pair is short exact.
* **First page.** The object at `(p, q)` on the first page (numbered `2` in the indexing of
  `CochainComplex.spectralSequence`) is the relative singular homology `Hₙ(X (q + 1), X q)` with
  `p + q = -n` (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`); it vanishes when
  `p + q > 0`.
* **First differential.** The differential from `(p, q)` to `(p + 2, q - 1)` is the connecting
  map `Hₙ₊₁(X (q + 1), X q) ⟶ Hₙ(X q, X (q - 1))` of the triple `(X (q + 1), X q, X (q - 1))`
  (`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`). This holds because the sequence of
  graded pieces `F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q`, whose connecting map is the
  first differential (`CochainComplex.spectralSequence_first_page_d_eq`), is isomorphic to the
  relative singular chain sequence of the triple.
* **Convergence.** The abutment in degree `-n` is `Hₙ(Y)` (`TauCeti.chainFiltrationAbutmentIso`),
  and the `q`th piece of its filtration is the image of `Hₙ(X q) ⟶ Hₙ(Y)`
  (`TauCeti.range_filteredSpaceAbutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom`).
  When `X a = ∅` and `X b = Y`, the filtration is finite and the spectral sequence converges
  strongly (`TauCeti.filteredSpaceSpectralSequencePageXIsoGradedOfFinite`). Filtrations that
  absorb every compact subset without reaching `Y`, such as the skeletal filtration over an
  infinite-dimensional CW complex, are treated in
  `TauCeti.AlgebraicTopology.Singular.FilteredSpace.Exhaustive`; the vanishing of the graded
  pieces `Hₙ(X b, X a)` they need there is transported to the quotients `F_b / F_a` by
  `TauCeti.isZero_homology_cokernel_singularChainFiltration`.
* **Naturality.** A continuous map `g : Y ⟶ Y'` carrying each `X q` into a member `X' q` of a
  filtration of `Y'` induces a morphism of filtered complexes and hence of spectral sequences
  (`TauCeti.filteredSpaceSpectralSequenceMap`), functorial in `g`. On the first page it is the map
  `Hₙ(X (q + 1), X q) ⟶ Hₙ(X' (q + 1), X' q)` induced by `g`
  (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`), so if these maps are
  isomorphisms, the morphism of spectral sequences is an isomorphism on every page
  (`TauCeti.isIso_filteredSpaceSpectralSequenceMap_hom_f`). On the abutment, the underlying
  morphism of spectral objects is the map `Hₙ(g)` in singular homology
  (`TauCeti.chainFiltrationAbutmentIso_hom_naturality`). For finite filtrations this gives the
  comparison theorem: if `g` induces isomorphisms on the relative homology of the pairs
  `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)`, it induces isomorphisms in singular homology
  (`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap`).
* **Naturality in the coefficients.** A morphism `φ : R ⟶ R'` of coefficient objects induces a
  morphism of filtered complexes and hence of spectral sequences
  (`TauCeti.filteredSpaceSpectralSequenceCoefficientMap`), functorial in `φ`. On the first page it
  is the map `Hₙ(X (q + 1), X q; R) ⟶ Hₙ(X (q + 1), X q; R')` induced by `φ` on relative singular
  chains (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_coefficient_naturality`), so if
  these maps are isomorphisms, the morphism of spectral sequences is an isomorphism on every page
  (`TauCeti.isIso_filteredSpaceSpectralSequenceCoefficientMap_hom_f`). It commutes with the
  morphisms induced by maps of filtered spaces
  (`TauCeti.filteredSpaceSpectralSequenceMap_comp_filteredSpaceSpectralSequenceCoefficientMap`),
  so the spectral sequence is functorial in the pair of the filtered space and the coefficients.

For the skeletal filtration of a CW complex the first page consists of the groups
`Hₙ(Xⁿ, Xⁿ⁻¹)`, and its differential is the connecting map of three consecutive skeleta, which is
the differential of `TauCeti.cellularChainComplex` by
`TauCeti.cellularDifferential_eq_singularHomologyδ`. Filtering the total space of
a fibration by the preimages of the skeleta of the base gives the Serre spectral sequence.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, Chapter 3, the comparison of spectral
  sequences, and Chapter 5, its application to the filtration of a total space by the preimages of
  the skeleta of the base.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex AlgebraicTopology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [Abelian A] {Y : TopCat.{w}}

variable [HasCoproducts.{w} A] (R : A) {X : ℤ → Set Y}

/-- The stage of the filtration of singular chains at an empty subset is zero. -/
@[simp]
lemma singularChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    chainFiltration ((singularChainComplexFunctor A).obj R) X a = ⊥ :=
  chainFiltration_eq_bot _ (fun Z _ ↦
    -- An empty space has no singular simplices.
    have : (TopCat.toSSet.obj Z).HasDimensionLT 0 :=
      (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun ⟨σ⟩ ↦
        isEmptyElim (TopCat.toSSetObj₀Equiv σ)
    SSet.isZero_chainComplex _ R) ha

/-- The reindexed quotient map onto the cokernel of the map of singular chains of a pair, followed
by the identification of that cokernel with relative singular chains, is the reindexed quotient
map onto relative singular chains. -/
private lemma extendMap_π_comp_cokernelSingularChainComplexIso_hom (P : TopPair.{w}) :
    extendMap (cokernel.π (((singularChainComplexFunctor A).obj R).map P.map))
        ComplexShape.embeddingDownNat ≫
      (ComplexShape.embeddingDownNat.extendFunctor A).map
        (P.cokernelSingularChainComplexIso R).hom =
    extendMap (P.singularChainComplexπ R) ComplexShape.embeddingDownNat :=
  (extendMap_comp _ _ _).symm.trans
    (congrArg (extendMap · _) (TopPair.π_cokernelSingularChainComplexIso_hom P R))

/-- The quotient `F_b / F_a` of two stages of the filtration of the singular chains of `Y` by
the singular chains of the `X q` is the relative singular chain complex of the pair `(X b, X a)`,
reindexed along `n ↦ -n`. The isomorphism is induced by the quotient map from the singular chains
of `X b` (`TauCeti.π_singularChainFiltrationCokernelIso_hom`). -/
def singularChainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _
        (chainFiltration_mono ((singularChainComplexFunctor A).obj R) hab)) ≅
      ((TopPair.ofInclusion hab).singularChainComplex R).extend ComplexShape.embeddingDownNat :=
  chainFiltrationCokernelIso _ hab ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor A).mapIso
      ((TopPair.ofInclusion hab).cokernelSingularChainComplexIso R)

/-- The identification of `F_b / F_a` with relative singular chains is induced by the quotient
map from the singular chains of `X b` to those of the pair `(X b, X a)`. -/
@[reassoc (attr := simp)]
lemma π_singularChainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (singularChainFiltrationCokernelIso R hab).hom =
      (chainFiltrationIso ((singularChainComplexFunctor A).obj R) X b).hom ≫
        extendMap ((TopPair.ofInclusion hab).singularChainComplexπ R)
          ComplexShape.embeddingDownNat :=
  (π_chainFiltrationCokernelIso_hom_assoc _ hab _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (extendMap_π_comp_cokernelSingularChainComplexIso_hom R _)

/-- The quotient `F_b / F_a` of two stages of the filtration of singular chains has vanishing
cohomology in degree `m` when the relative singular homology `Hₙ(X b, X a)` vanishes for
`m = -n`. In positive degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_singularChainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (h : ∀ n : ℕ, m = -n → IsZero ((TopPair.ofInclusion hab).singularHomology R n)) :
    IsZero ((cokernel (Subobject.ofLE _ _
      (chainFiltration_mono ((singularChainComplexFunctor A).obj R) hab))).homology m) :=
  isZero_homology_cokernel_chainFiltration _ hab m fun n hn ↦
    (h n hn).of_iso ((homologyFunctor A _ n).mapIso
      ((TopPair.ofInclusion hab).cokernelSingularChainComplexIso R))

variable (hX : Monotone X)

/-- The quotient of two stages of the filtration of singular chains, as the cokernel of a
transition map of the functor `CochainComplex.filtrationFunctor` of the filtration, is the
reindexed relative singular chain complex of the corresponding pair. -/
private def cokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _
      (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX)).map f) ≅
      ((TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplex
        R).extend ComplexShape.embeddingDownNat :=
  chainFiltrationCokernelFiltrationFunctorMapIso _ hX f ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor A).mapIso
      ((TopPair.ofInclusion _).cokernelSingularChainComplexIso R)

@[reassoc]
private lemma π_cokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIso R hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (chainFiltrationIso ((singularChainComplexFunctor A).obj R) X b).hom ≫
            extendMap ((TopPair.ofInclusion
              (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
              ComplexShape.embeddingDownNat :=
  (π_chainFiltrationCokernelFiltrationFunctorMapIso_hom_assoc _ hX f _).trans <|
    congrArg (_ ≫ _ ≫ ·) <| (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (extendMap_π_comp_cokernelSingularChainComplexIso_hom R _)

/-- **The spectral object of a filtered space.** For an increasing family `X : ℤ → Set Y` of
subsets of a space `Y`, this is the spectral object of the filtration of the singular chains of
`Y` by the singular chains of the `X q`. Its spectral sequence is
`TauCeti.filteredSpaceSpectralSequence`. -/
abbrev filteredSpaceSpectralObject :=
  CochainComplex.spectralObject
    (CochainComplex.filtrationFunctor _
      (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX))

/-- **The spectral sequence of a filtered space.** For an increasing family `X : ℤ → Set Y` of
subsets of a space `Y`, this is the spectral sequence of the filtration of the singular chains of
`Y` by the singular chains of the `X q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: singular chains in degree `n` sit in degree `-n`. -/
abbrev filteredSpaceSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _
      (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX))

/-- **The first page of the spectral sequence of a filtered space.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the relative singular
homology `Hₙ(X (q + 1), X q)`, where `p + q = -n`. The indices `q`, `q + 1` and `p + q` are given
as `a`, `b` and `m` together with equations, for flexibility. -/
def filteredSpaceSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceSpectralSequence R hX).page 2).X pq ≅
      (TopPair.ofInclusion (hX (by lia : a ≤ b))).singularHomology R n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
    (homologyFunctor A _ _).mapIso (cokernelFiltrationFunctorMapIso R hX _) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- The identification of the first page with relative singular homology is the identification
`TauCeti.chainFiltrationSpectralSequenceFirstPageXIso` of the first page with the homology of the
cokernel of the map of singular chains of the pair, followed by the identification of that
cokernel with the relative singular chain complex. -/
lemma filteredSpaceSpectralSequenceFirstPageXIso_hom (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom =
      (chainFiltrationSpectralSequenceFirstPageXIso _ hX pq a b ha hb m hm n hn).hom ≫
        homologyMap ((TopPair.ofInclusion (hX (by lia : a ≤ b))).cokernelSingularChainComplexIso
          R).hom n := by
  rw [chainFiltrationSpectralSequenceFirstPageXIso_eq]
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, cokernelFiltrationFunctorMapIso,
    Iso.trans_hom, Category.assoc]
  -- The identifications are composites of isomorphisms whose types mention the pair
  -- `(X b, X a)` through `hX`, so they are composed with terms rather than `rw`.
  exact congrArg (_ ≫ ·) <|
    ((congrArg (· ≫ _) ((homologyFunctor A _ m).map_comp _ _)).trans
      (Category.assoc _ _ _)).trans <|
      congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _)

/-- The first page of the spectral sequence of a filtered space vanishes in positive total
degree `p + q`, since singular chains are concentrated in nonpositive cohomological degrees. -/
lemma isZero_filteredSpaceSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 < pq.1 + pq.2) :
    IsZero (((filteredSpaceSpectralSequence R hX).page 2).X pq) :=
  isZero_chainFiltrationSpectralSequence_page_two_X _ hX pq h

/-- A morphism between spectral sequences of filtered spaces is an isomorphism on every object of
every page `r ≥ 2` as soon as it is one on the first page in nonpositive total degree, since the
first pages vanish in positive total degree. -/
private lemma isIso_hom_f_of_isIso_page_two {R' : A} {Y' : TopCat.{w}} {X' : ℤ → Set Y'}
    {hX' : Monotone X'}
    (f : filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R' hX')
    (h : ∀ (pq : ℤ × ℤ) (n : ℕ), pq.1 + pq.2 = -n → IsIso ((f.hom 2 le_rfl).f pq))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso ((f.hom r hr).f pq) := by
  refine SpectralSequence.Hom.isIso_hom_f_of_le _ 2 le_rfl (fun pq ↦ ?_) r hr pq
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact (isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos).isIso
      (isZero_filteredSpaceSpectralSequence_page_two_X R' hX' pq hpos) _
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  exact h pq n hn

/-- **Strong convergence of the spectral sequence of a finite filtration of a space.** If
`X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 2` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the filtration of
the abutment in degree `p + q`, which is `H_{-(p+q)}(Y)` by `TauCeti.chainFiltrationAbutmentIso`. -/
def filteredSpaceSpectralSequencePageXIsoGradedOfFinite {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((filteredSpaceSpectralSequence R hX).page r).X pq ≅
      cokernel ((filteredSpaceSpectralObject R hX).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (singularChainFiltration_eq_bot R ha) (chainFiltration_eq_top _ hb) r hr pq hra hrb

section ImageFiltration

variable {k : Type w} [Ring k]

/-- **The filtration of the abutment of a filtered space is the image filtration.** Under the
identification `TauCeti.chainFiltrationAbutmentIso` of the abutment in degree `-n` with `Hₙ(Y; M)`,
the `q`th piece of its filtration is the image of the map `Hₙ(X q; M) ⟶ Hₙ(Y; M)` induced by the
inclusion of `X q`. -/
theorem range_filteredSpaceAbutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom
    (M : ModuleCat.{w} k) (hX : Monotone X) (q : ℤ) (n : ℕ) :
    LinearMap.range ((filteredSpaceSpectralObject M hX).abutmentFiltrationι q (-n) ≫
        (chainFiltrationAbutmentIso ((singularChainComplexFunctor _).obj M) hX n).hom).hom =
      LinearMap.range
        (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) M n).hom := by
  have h := congrArg (fun f ↦ LinearMap.range (ModuleCat.Hom.hom f))
    (chainFiltrationToAbutmentFiltration_comp_chainFiltrationAbutmentIso_hom
      ((singularChainComplexFunctor _).obj M) hX q n)
  simp only [ModuleCat.hom_comp] at h
  rw [LinearMap.range_comp_of_range_eq_top _
    ((ModuleCat.epi_iff_range_eq_top _).1 inferInstance)] at h
  -- `SSet.homologyMap` is by definition the map in homology of the singular chains, whose codomain
  -- is `Y` up to unfolding `TopPair.ofSubset`; `exact` performs both unfoldings.
  exact h

end ImageFiltration

section FirstDifferential

variable (q : ℤ)

/-- The triple `(X (q + 1), X q, X (q - 1))` of three consecutive stages of a filtration. -/
private abbrev filtrationTriple : TopTriple.{w} :=
  TopTriple.ofInclusions (hX (by lia : q - 1 ≤ q)) (hX (by lia : q ≤ q + 1))

/-- The transition map `F_a ⟶ F_b` of the functor of the filtration of singular chains. -/
private abbrev fMap {a b : ℤ} (h : (a : EInt) ≤ b) :=
  (CochainComplex.filtrationFunctor _
    (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX)).map (homOfLE h)

/-- The sequence `F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q` of graded pieces: the last row of
`kernelCokernelCompSequence.snakeInput` for the transition maps `F_{q-1} ⟶ F_q ⟶ F_{q+1}`. -/
private abbrev gradedShortComplex : ShortComplex (CochainComplex A ℤ) :=
  (kernelCokernelCompSequence.snakeInput (fMap R hX (by simp : ((q - 1 : ℤ) : EInt) ≤ q))
    (fMap R hX (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))).L₃

/-- The reindexed relative singular chain sequence of the triple `(X (q + 1), X q, X (q - 1))`,
written with the pairs of the filtration. -/
private abbrev tripleShortComplex : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (X₁ := ((TopPair.ofInclusion (hX (by lia : q - 1 ≤ q))).singularChainComplex R).extend
      ComplexShape.embeddingDownNat)
    (X₂ := ((TopPair.ofInclusion (hX (by lia : q - 1 ≤ q + 1))).singularChainComplex R).extend
      ComplexShape.embeddingDownNat)
    (X₃ := ((TopPair.ofInclusion (hX (by lia : q ≤ q + 1))).singularChainComplex R).extend
      ComplexShape.embeddingDownNat)
    (extendMap (TopPair.singularChainComplexMap
      (TopTriple.innerToTotal.app (filtrationTriple hX q)) R) ComplexShape.embeddingDownNat)
    (extendMap (TopPair.singularChainComplexMap
      (TopTriple.totalToOuter.app (filtrationTriple hX q)) R) ComplexShape.embeddingDownNat)
    (((filtrationTriple hX q).singularChainComplexShortComplex R).map
      (ComplexShape.embeddingDownNat.extendFunctor A)).zero

private lemma tripleShortComplex_shortExact : (tripleShortComplex R hX q).ShortExact :=
  ((filtrationTriple hX q).shortExact_singularChainComplexShortComplex R).extend _

/-- The quotient maps from the chains of `X q` modulo those of `X (q - 1)` and of `X (q + 1)`
modulo those of `X (q - 1)`, compared through the triple `(X (q + 1), X q, X (q - 1))`. -/
private lemma extendMap_π_comp_innerToTotal :
    extendMap ((TopPair.ofInclusion (hX (by lia : q - 1 ≤ q))).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
      extendMap (TopPair.singularChainComplexMap
        (TopTriple.innerToTotal.app (filtrationTriple hX q)) R) ComplexShape.embeddingDownNat =
    extendMap (SSet.chainComplexMap (TopCat.toSSet.map
        (TopPair.ofInclusion (hX (by lia : q ≤ q + 1))).map) R) ComplexShape.embeddingDownNat ≫
      extendMap ((TopPair.ofInclusion (hX (by lia : q - 1 ≤ q + 1))).singularChainComplexπ R)
        ComplexShape.embeddingDownNat :=
  (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _)
    ((filtrationTriple hX q).singularChainComplexπ_comp_innerToTotal R)).trans
      (extendMap_comp _ _ _)

private lemma extendMap_π_comp_totalToOuter :
    extendMap ((TopTriple.totalPair.obj (filtrationTriple hX q)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
      extendMap (TopPair.singularChainComplexMap
        (TopTriple.totalToOuter.app (filtrationTriple hX q)) R) ComplexShape.embeddingDownNat =
    extendMap ((TopTriple.outerPair.obj (filtrationTriple hX q)).singularChainComplexπ R)
      ComplexShape.embeddingDownNat := by
  rw [← extendMap_comp]
  exact congrArg (fun f ↦ extendMap f ComplexShape.embeddingDownNat)
    ((filtrationTriple hX q).singularChainComplexπ_comp_totalToOuter R)

/-- The identification of the sequence of graded pieces with the reindexed relative singular
chain sequence of the triple `(X (q + 1), X q, X (q - 1))`. -/
private def gradedShortComplexHom : gradedShortComplex R hX q ⟶ tripleShortComplex R hX q where
  τ₁ := (cokernelFiltrationFunctorMapIso R hX _).hom
  τ₂ := (cokernelIsoOfEq (Functor.map_comp _ _ _).symm ≪≫
    cokernelFiltrationFunctorMapIso R hX _).hom
  τ₃ := (cokernelFiltrationFunctorMapIso R hX _).hom
  comm₁₂ := by
    unfold gradedShortComplex kernelCokernelCompSequence.snakeInput
    refine (cancel_epi (cokernel.π _)).1 ?_
    simp only [homOfLE_leOfHom, TopTriple.innerPair_obj_ofInclusions,
      TopTriple.totalPair_obj_ofInclusions, π_cokernelFiltrationFunctorMapIso_hom_assoc,
      TopPair.toSSetPair_obj_right, homOfLE_comp, Iso.trans_hom, cokernel.π_desc_assoc,
      coequalizer_as_cokernel, Category.assoc, π_comp_cokernelIsoOfEq_hom_assoc,
      π_cokernelFiltrationFunctorMapIso_hom,
      reassoc_of% CochainComplex.filtrationFunctor_map_comp_objIso_hom,
      Subobject.ofLE_comp_ofLE_assoc, Iso.cancel_iso_hom_left]
    rw [← Subobject.ofLE_comp_ofLE_assoc _
      (chainFiltration ((singularChainComplexFunctor A).obj R) X q) _
      (CochainComplex.filtrationEInt_coe _ q).le
      (chainFiltration_mono ((singularChainComplexFunctor A).obj R) (hX (by lia : q ≤ q + 1)))]
    -- The identification of `F_{q+1}` with the chains of `X (q + 1)` lands in the chains of the
    -- subspace `X (q + 1)` of `Y`, which are those of the ambient space of the pair
    -- `(X (q + 1), X (q - 1))` only up to unfolding `MorphismProperty.Arrow.mk`; `erw` matches
    -- the composite up to that unfolding.
    erw [ofLE_comp_chainFiltrationIso_hom_assoc ((singularChainComplexFunctor A).obj R)
      (hX (by lia : q ≤ q + 1))]
    exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (extendMap_π_comp_innerToTotal R hX q)).trans (Category.assoc _ _ _).symm)
  comm₂₃ := by
    unfold gradedShortComplex kernelCokernelCompSequence.snakeInput
    refine (cancel_epi (cokernel.π _)).1 ?_
    simp only [homOfLE_leOfHom, homOfLE_comp, Iso.trans_hom,
      TopTriple.totalPair_obj_ofInclusions, TopTriple.outerPair_obj_ofInclusions, Category.assoc,
      π_comp_cokernelIsoOfEq_hom_assoc, π_cokernelFiltrationFunctorMapIso_hom_assoc,
      TopPair.toSSetPair_obj_right, cokernel.π_desc_assoc, coequalizer_as_cokernel,
      Category.id_comp, π_cokernelFiltrationFunctorMapIso_hom, Iso.cancel_iso_hom_left]
    exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (extendMap_π_comp_totalToOuter R hX q))

/-- The connecting maps of the sequence of graded pieces and of the triple
`(X (q + 1), X q, X (q - 1))` agree under the identifications of the graded pieces with relative
singular chains. -/
private lemma δ_comp_extendHomologyIso_hom (n : ℕ) (m₀ m₁ : ℤ) (h₀ : m₀ = -(n + 1 : ℕ))
    (h₁ : m₁ = -n) (h : (ComplexShape.up ℤ).Rel m₀ m₁) :
    (kernelCokernelCompSequence_snakeInput_L₃_shortExact _ _).δ m₀ m₁ h ≫
        HomologicalComplex.homologyMap (gradedShortComplexHom R hX q).τ₁ m₁ ≫
          (extendHomologyIso _ ComplexShape.embeddingDownNat h₁.symm).hom =
      HomologicalComplex.homologyMap (gradedShortComplexHom R hX q).τ₃ m₀ ≫
        (extendHomologyIso _ ComplexShape.embeddingDownNat h₀.symm).hom ≫
          (filtrationTriple hX q).singularHomologyδ R (n + 1) n := by
  rw [← Category.assoc, HomologicalComplex.HomologySequence.δ_naturality _ _
    (tripleShortComplex_shortExact R hX q), Category.assoc,
    TopTriple.singularHomologyδ_def _ R (n + 1) n rfl]
  exact congrArg (_ ≫ ·) (ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom
    ((filtrationTriple hX q).shortExact_singularChainComplexShortComplex R)
    ComplexShape.embeddingDownNat (by simp) h₀.symm h₁.symm h)

/-- **The first differential of the spectral sequence of a filtered space.** Under the
identifications of the first page with relative singular homology, the differential from `(p, q)`
to `(p + 2, q - 1)` is the connecting map `Hₙ₊₁(X (q + 1), X q) ⟶ Hₙ(X q, X (q - 1))` of the triple
`(X (q + 1), X q, X (q - 1))`, where `p + q = -(n + 1)`. -/
theorem filteredSpaceSpectralSequence_first_page_d_eq (p : ℤ) (n : ℕ)
    (hn : p + q = -(n + 1 : ℕ)) :
    ((filteredSpaceSpectralSequence R hX).page 2).d (p, q) (p + 2, q - 1) =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX (p, q) q (q + 1) rfl rfl (p + q) rfl
          (n + 1) hn).hom ≫
        (TopTriple.ofInclusions (hX (by lia : q - 1 ≤ q))
          (hX (by lia : q ≤ q + 1))).singularHomologyδ R (n + 1) n ≫
          (filteredSpaceSpectralSequenceFirstPageXIso R hX (p + 2, q - 1) (q - 1) q rfl (by lia)
            (p + q + 1) (by lia) n (by lia)).inv := by
  rw [CochainComplex.spectralSequence_first_page_d_eq]
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, Iso.trans_hom, Iso.trans_inv,
    Category.assoc]
  congr 1
  rw [(Iso.eq_comp_inv ((homologyFunctor A _ (p + q + 1)).mapIso
      (cokernelFiltrationFunctorMapIso R hX _) ≪≫ extendHomologyIso _ _ _)).2
    ((δ_comp_extendHomologyIso_hom R hX q n _ _ hn (by lia) rfl).trans
      (Category.assoc _ _ _).symm)]
  -- The remaining chain only reassociates the composite. It closes by `exact` because
  -- `((homologyFunctor A _ (p + q)).mapIso (cokernelFiltrationFunctorMapIso R hX _)).hom` is
  -- definitionally `homologyMap (gradedShortComplexHom R hX q).τ₃ (p + q)`, and the inverse of the
  -- `Iso.trans` above agrees with the composite of inverses only up to unfolding.
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.assoc _ _ _)))

end FirstDifferential

section Naturality

variable {Y' Y'' : TopCat.{w}} {X' : ℤ → Set Y'} (hX' : Monotone X') {X'' : ℤ → Set Y''}
  (hX'' : Monotone X'') (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q))

include g hg in
/-- **The morphism of spectral sequences induced by a map of filtered spaces.** A continuous map
`g : Y ⟶ Y'` carrying each `X q` into `X' q` induces a morphism from the spectral sequence of the
filtration of `Y` by the `X q` to that of the filtration of `Y'` by the `X' q`. On the first page
it is the map induced by `g` on the relative singular homology of the steps
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`). -/
def filteredSpaceSpectralSequenceMap :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R hX' :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (chainFiltrationMap (𝟙 _) hX hX' g hg))

include g hg in
/-- `TauCeti.filteredSpaceSpectralSequenceMap` is the morphism of spectral sequences of the
morphism of spectral objects of `TauCeti.chainFiltrationMap` for the identity of singular
chains. -/
lemma filteredSpaceSpectralSequenceMap_def :
    filteredSpaceSpectralSequenceMap R hX hX' g hg =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (chainFiltrationMap (𝟙 _) hX hX' g hg)) :=
  (rfl)

/-- The identity of a filtered space induces the identity of its spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceMap_id
    (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) :
    filteredSpaceSpectralSequenceMap R hX hX (𝟙 Y) h = 𝟙 _ := by
  rw [filteredSpaceSpectralSequenceMap_def, chainFiltrationMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of spectral
sequences. -/
@[reassoc]
lemma filteredSpaceSpectralSequenceMap_comp (g' : Y' ⟶ Y'')
    (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q)) (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceSpectralSequenceMap R hX hX'' (g ≫ g') hgg' =
      filteredSpaceSpectralSequenceMap R hX hX' g hg ≫
        filteredSpaceSpectralSequenceMap R hX' hX'' g' hg' := by
  -- `TauCeti.chainFiltrationMap_comp` also composes the natural transformations, here two
  -- identities of singular chains.
  have h := chainFiltrationMap_comp (𝟙 ((singularChainComplexFunctor A).obj R)) hX hX' hX'' g hg
    (𝟙 _) g' hg' hgg'
  rw [Category.comp_id] at h
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceSpectralSequenceMap_def,
    filteredSpaceSpectralSequenceMap_def, h, CochainComplex.spectralObjectMap_comp,
    Abelian.SpectralObject.spectralSequenceMap_comp]

include g hg in
/-- The map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by a map `g` carrying each `X q` into
`X' q`, for `a ≤ b`. -/
def filteredSpaceStepMap {a b : ℤ} (hab : a ≤ b) :
    TopPair.ofInclusion (hX hab) ⟶ TopPair.ofInclusion (hX' hab) :=
  TopPair.ofInclusionMap _ _ ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩
    fun _ hx ↦ hg a hx

/-- The ambient component of the map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by `g` sends
`x` to `g x`. -/
@[simp]
lemma filteredSpaceStepMap_fst_apply {a b : ℤ} (hab : a ≤ b)
    (x : (TopPair.ofInclusion (hX hab)).fst) :
    (TopPair.Hom.fst (filteredSpaceStepMap hX hX' g hg hab) x).val = g x.val :=
  congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)

/-- The subspace component of the map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by `g` sends
`x` to `g x`. -/
@[simp]
lemma filteredSpaceStepMap_snd_apply {a b : ℤ} (hab : a ≤ b)
    (x : (TopPair.ofInclusion (hX hab)).snd) :
    (TopPair.Hom.snd (filteredSpaceStepMap hX hX' g hg hab) x).val = g x.val :=
  TopPair.ofInclusionMap_snd_apply _ _ x

/-- The identity of a filtered space induces the identity of each pair `(X b, X a)`. -/
@[simp]
lemma filteredSpaceStepMap_id (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) {a b : ℤ}
    (hab : a ≤ b) : filteredSpaceStepMap hX hX (𝟙 Y) h hab = 𝟙 _ := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext x
  exact Subtype.ext (filteredSpaceStepMap_fst_apply hX hX _ h hab x)

/-- A composite of maps of filtered spaces induces the composite of the maps of pairs
`(X b, X a) ⟶ (X' b, X' a) ⟶ (X'' b, X'' a)`. -/
@[reassoc]
lemma filteredSpaceStepMap_comp (g' : Y' ⟶ Y'') (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q))
    (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) {a b : ℤ} (hab : a ≤ b) :
    filteredSpaceStepMap hX hX'' (g ≫ g') hgg' hab =
      filteredSpaceStepMap hX hX' g hg hab ≫ filteredSpaceStepMap hX' hX'' g' hg' hab := by
  refine TopPair.hom_ext_of_fst _ ?_
  rw [TopPair.Hom.fst_comp]
  ext x
  exact Subtype.ext (by simp)

/-- The ambient component of the map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by `g` is the
subspace component of the map of pairs `(Y, X b) ⟶ (Y', X' b)` induced by `g`. -/
private lemma fst_filteredSpaceStepMap {a b : ℤ} (hab : a ≤ b) :
    TopPair.Hom.fst (filteredSpaceStepMap hX hX' g hg hab) =
      TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)) := by
  ext x
  exact Subtype.ext <| (filteredSpaceStepMap_fst_apply hX hX' g hg hab x).trans
    (TopPair.ofSubsetMap_snd_apply g (hg b) x).symm

/-- On the stage `F_b`, identified with the singular chains of `X b`, the morphism of filtrations
induced by `g` is the chain map induced by the restriction of `g`. -/
@[reassoc]
private lemma chainFiltrationMap_app_comp_singularChainFiltrationIso_hom (b : ℤ) :
    (chainFiltrationMap (𝟙 _) hX hX' g hg).app b ≫
        (CochainComplex.filtrationFunctorObjIso _
            (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX') b).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (chainFiltrationIso ((singularChainComplexFunctor A).obj R) X' b).hom =
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX) b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (chainFiltrationIso ((singularChainComplexFunctor A).obj R) X b).hom ≫
            extendMap (((singularChainComplexFunctor A).obj R).map
              (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) ComplexShape.embeddingDownNat := by
  -- These identifications of the stages are `CochainComplex.filtrationFunctorObjIsoOfEqMk`, so this
  -- is the generic statement for the identity of singular chains.
  have e {Z : TopCat.{w}} {Xz : ℤ → Set Z} (hXz : Monotone Xz) :
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hXz) b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (chainFiltrationIso ((singularChainComplexFunctor A).obj R) Xz b).hom =
        (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (chainFiltrationι _ Xz)
          (chainFiltration_def _ Xz) b).hom :=
    (cancel_mono (chainFiltrationι _ Xz b)).1 (by simp)
  simpa only [reassoc_of% (e hX), e hX', NatTrans.id_app, Category.comp_id] using
    chainFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom (𝟙 _) hX hX' g hg b

/-- On the graded pieces `F_b / F_a`, identified with relative singular chains, the morphism of
filtrations induced by `g` is the chain map induced by `g` on the pairs `(X b, X a)`. -/
private lemma cokernelMap_comp_cokernelFiltrationFunctorMapIso_hom {a b : ℤ}
    (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((chainFiltrationMap (𝟙 _) hX hX' g hg).naturality f).symm ≫
        (cokernelFiltrationFunctorMapIso R hX' f).hom =
      (cokernelFiltrationFunctorMapIso R hX f).hom ≫
        extendMap (TopPair.singularChainComplexMap
          (filteredSpaceStepMap hX hX' g hg (WithBotTop.coe_le_coe.mp (leOfHom f))) R)
          ComplexShape.embeddingDownNat := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  simp only [cokernel.map, cokernel.π_desc_assoc, Category.assoc,
    π_cokernelFiltrationFunctorMapIso_hom, π_cokernelFiltrationFunctorMapIso_hom_assoc]
  have hab := WithBotTop.coe_le_coe.mp (leOfHom f)
  -- The quotient maps to relative chains are natural in the map of pairs.
  have h : extendMap ((TopPair.ofInclusion (hX hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
      extendMap (TopPair.singularChainComplexMap (filteredSpaceStepMap hX hX' g hg hab) R)
        ComplexShape.embeddingDownNat =
      extendMap (((singularChainComplexFunctor A).obj R).map
          (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) ComplexShape.embeddingDownNat ≫
      extendMap ((TopPair.ofInclusion (hX' hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat := by
    rw [← extendMap_comp, ← TopPair.singularChainComplexπ_pair_naturality,
      fst_filteredSpaceStepMap]
    exact extendMap_comp _ _ _
  refine (chainFiltrationMap_app_comp_singularChainFiltrationIso_hom_assoc R hX hX' g hg b
    _).trans ?_
  rw [← h]
  exact congrArg (_ ≫ ·) <| congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

/-- **The morphism of spectral sequences of a map of filtered spaces on the first page.** Let
`g : Y ⟶ Y'` carry each `X q` into `X' q`. Under the identifications of the first pages with
relative singular homology (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`), the morphism of
spectral sequences induced by `g` is, at `(p, q)`, the map
`Hₙ(X (q + 1), X q) ⟶ Hₙ(X' (q + 1), X' q)` induced by `g`, where `p + q = -n`. -/
@[reassoc]
theorem filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX' pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        TopPair.singularHomologyMap (filteredSpaceStepMap hX hX' g hg (by lia)) R n := by
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, Iso.trans_hom,
    filteredSpaceSpectralSequenceMap_def]
  -- Compare the graded pieces at the chain level, then pass to homology.
  rw [CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality_assoc]
  refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  -- The complexes involved are indexed through the proofs `hX hab` and `hX' hab`, so this goal is
  -- not type-correct at reducible transparency and `rw` or `simp` cannot rewrite inside it; the
  -- steps are composed explicitly.
  exact (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans <|
    (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ m ≫ _)
      (cokernelMap_comp_cokernelFiltrationFunctorMapIso_hom R hX hX' g hg _)).trans <|
      (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).trans <|
        (congrArg
          (HomologicalComplex.homologyMap (cokernelFiltrationFunctorMapIso R hX _).hom m ≫ ·)
          (extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

/-- **The comparison theorem for maps of filtered spaces.** If a map `g : Y ⟶ Y'` carrying each
`X q` into `X' q` induces isomorphisms `Hₙ(X (q + 1), X q) ≅ Hₙ(X' (q + 1), X' q)` for every `q`
and `n`, then the induced morphism of spectral sequences is an isomorphism on every object of every
page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_filteredSpaceSpectralSequenceMap_hom_f
    (h : ∀ (q : ℤ) (n : ℕ), IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap hX hX' g hg (Int.le_add_one le_rfl : q ≤ q + 1)) R n))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom r hr).f pq) := by
  refine isIso_hom_f_of_isIso_page_two R hX _ (fun pq n hn ↦ ?_) r hr pq
  have e := filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality R hX hX' g hg pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn
  rw [← Iso.eq_comp_inv] at e
  have := h pq.2 n
  rw [e]
  infer_instance

/-- Outside `[a, b)`, the relative singular homology `Hₙ(X (q + 1), X q)` of a filtration with
`X a = ∅` and `X b = Y` vanishes: both subspaces are empty, or both are everything. -/
private lemma isZero_singularHomology_ofInclusion_of_notMem_Ico {a b q : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (hq : q ∉ Set.Ico a b) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl : q ≤ q + 1))).singularHomology R n) :=
  TopPair.isZero_singularHomology_of_surjective_map _ R (fun y ↦ by
    rcases not_and_or.1 hq with hq | hq
    · exact absurd (hX (by lia : q + 1 ≤ a) y.property) (by simp [ha])
    · exact ⟨⟨y.val, hX (not_lt.1 hq) (hb ▸ Set.mem_univ y.val)⟩, rfl⟩) n

/-- **The comparison theorem for maps of finite filtrations of spaces.** Let `g : Y ⟶ Y'` carry
each `X q` into `X' q`, for finite filtrations: `X a` and `X' a` are empty, and `X b` and `X' b`
are everything. If for every `a ≤ q < b` the map of pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)`
induced by `g` gives isomorphisms in relative singular homology, then `g` induces isomorphisms
`Hₙ(Y) ⟶ Hₙ(Y')` in singular homology. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap {a b : ℤ} (ha : X a = ∅)
    (ha' : X' a = ∅) (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ, IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap hX hX' g hg (Int.le_add_one le_rfl : q ≤ q + 1)) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  -- The morphism of spectral sequences is an isomorphism from the first page on: outside the
  -- bands `a ≤ q < b` both relative homologies vanish.
  have hpage := isIso_filteredSpaceSpectralSequenceMap_hom_f R hX hX' g hg (fun q m ↦ by
    by_cases hq : q ∈ Set.Ico a b
    · exact h q hq.1 hq.2 m
    · exact (isZero_singularHomology_ofInclusion_of_notMem_Ico R hX ha hb hq m).isIso
        (isZero_singularHomology_ofInclusion_of_notMem_Ico R hX' ha' hb' hq m) _) 2 le_rfl
  -- Both filtrations are finite, so it is an isomorphism on the abutments.
  have habut :=
    CochainComplex.isIso_spectralObjectMap_hom_app_abutment_of_isIso_spectralSequence_page _ _ _ _
      (chainFiltrationMap (𝟙 _) hX hX' g hg) (singularChainFiltration_eq_bot R ha)
      (singularChainFiltration_eq_bot R ha') (chainFiltration_eq_top _ hb)
      (chainFiltration_eq_top _ hb') 2 le_rfl hpage (-n)
  have e := chainFiltrationAbutmentIso_hom_naturality (𝟙 ((singularChainComplexFunctor A).obj R))
    hX hX' g hg n
  rw [NatTrans.id_app, Category.comp_id, ← Iso.inv_comp_eq] at e
  rw [singularHomologyFunctor_obj_map]
  -- `SSet.homologyMap` is by definition the map in homology of the singular chains.
  change IsIso (HomologicalComplex.homologyMap
    (((singularChainComplexFunctor A).obj R).map g) n)
  rw [← e]
  infer_instance

end Naturality

section CoefficientNaturality

variable {R} {R' R'' : A} (φ : R ⟶ R') (ψ : R' ⟶ R'')

/-- A morphism of coefficients `φ : R ⟶ R'` carries the singular chains of `X q` with coefficients
in `R` into those with coefficients in `R'`, compatibly with the inclusions into the chains of
`Y`. -/
@[reassoc]
private lemma chainFiltrationι_coefficient_naturality (q : ℤ) :
    extendMap (((singularChainComplexFunctor A).map φ).app (TopPair.ofSubset (X q)).snd)
        ComplexShape.embeddingDownNat ≫
        chainFiltrationι ((singularChainComplexFunctor A).obj R') X q =
      chainFiltrationι ((singularChainComplexFunctor A).obj R) X q ≫
        extendMap (((singularChainComplexFunctor A).map φ).app Y)
          ComplexShape.embeddingDownNat := by
  rw [chainFiltrationι_def, chainFiltrationι_def]
  -- The ambient space of `TopPair.ofSubset (X q)` is `Y` only up to unfolding, so the composites
  -- are formed with `exact` rather than `rw`, as in `extendMap_comp_chainFiltrationι`.
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · ComplexShape.embeddingDownNat)
      (((singularChainComplexFunctor A).map φ).naturality
        (TopPair.ofSubset (X q)).map).symm).trans (extendMap_comp _ _ _)

/-- **The morphism of filtered complexes induced by a morphism of coefficients.** A morphism
`φ : R ⟶ R'` in the coefficient category induces, on the singular chains of `Y`, a morphism from
the filtration by the singular chains of the `X q` with coefficients in `R` to the same filtration
with coefficients in `R'`. It is `TauCeti.chainFiltrationMap` for the natural transformation of
singular chain functors induced by `φ` and the identity of `Y`. -/
def filteredSpaceCoefficientFiltrationMap :
    CochainComplex.filtrationFunctor _
        (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX) ⟶
      CochainComplex.filtrationFunctor _
        (monotone_chainFiltration ((singularChainComplexFunctor A).obj R') hX) :=
  chainFiltrationMap ((singularChainComplexFunctor A).map φ) hX hX (𝟙 Y) fun q ↦ by
    simpa using Set.mapsTo_id (X q)

/-- The components of `TauCeti.filteredSpaceCoefficientFiltrationMap` are the restrictions of the
chain map induced by the morphism of coefficients. -/
@[reassoc (attr := simp)]
lemma filteredSpaceCoefficientFiltrationMap_app_comp (a : EInt) :
    (filteredSpaceCoefficientFiltrationMap hX φ).app a ≫
        CochainComplex.filtrationFunctorArrow _
          (monotone_chainFiltration ((singularChainComplexFunctor A).obj R') hX) a =
      CochainComplex.filtrationFunctorArrow _
          (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX) a ≫
        extendMap (((singularChainComplexFunctor A).map φ).app Y)
          ComplexShape.embeddingDownNat := by
  rw [filteredSpaceCoefficientFiltrationMap, chainFiltrationMap_app_comp,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The identity of the coefficients induces the identity of the filtered singular chains. -/
@[simp]
lemma filteredSpaceCoefficientFiltrationMap_id :
    filteredSpaceCoefficientFiltrationMap hX (𝟙 R) = 𝟙 _ := by
  rw [filteredSpaceCoefficientFiltrationMap, CategoryTheory.Functor.map_id, chainFiltrationMap_id]

/-- A composite of morphisms of coefficients induces the composite of the morphisms of filtered
singular chains. -/
@[reassoc]
lemma filteredSpaceCoefficientFiltrationMap_comp :
    filteredSpaceCoefficientFiltrationMap hX (φ ≫ ψ) =
      filteredSpaceCoefficientFiltrationMap hX φ ≫ filteredSpaceCoefficientFiltrationMap hX ψ := by
  ext a : 2
  rw [← cancel_mono (CochainComplex.filtrationFunctorArrow _
    (monotone_chainFiltration ((singularChainComplexFunctor A).obj R'') hX) a)]
  simp only [NatTrans.comp_app, Category.assoc, filteredSpaceCoefficientFiltrationMap_app_comp,
    filteredSpaceCoefficientFiltrationMap_app_comp_assoc, ← extendMap_comp,
    CategoryTheory.Functor.map_comp]

/-- **The morphism of spectral sequences induced by a morphism of coefficients.** A morphism
`φ : R ⟶ R'` induces a morphism from the spectral sequence of the filtration of `Y` by the `X q`
with coefficients in `R` to the one with coefficients in `R'`. On the first page it is the map
induced by `φ` on the relative singular homology of the steps
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_coefficient_naturality`). -/
def filteredSpaceSpectralSequenceCoefficientMap :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R' hX :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (filteredSpaceCoefficientFiltrationMap hX φ))

/-- `TauCeti.filteredSpaceSpectralSequenceCoefficientMap` is the morphism of spectral sequences of
the morphism of spectral objects of `TauCeti.filteredSpaceCoefficientFiltrationMap`. -/
lemma filteredSpaceSpectralSequenceCoefficientMap_def :
    filteredSpaceSpectralSequenceCoefficientMap hX φ =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (filteredSpaceCoefficientFiltrationMap hX φ)) :=
  (rfl)

/-- The identity of the coefficients induces the identity of the spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceCoefficientMap_id :
    filteredSpaceSpectralSequenceCoefficientMap hX (𝟙 R) = 𝟙 _ := by
  rw [filteredSpaceSpectralSequenceCoefficientMap_def, filteredSpaceCoefficientFiltrationMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of morphisms of coefficients induces the composite of the morphisms of spectral
sequences. -/
@[reassoc]
lemma filteredSpaceSpectralSequenceCoefficientMap_comp :
    filteredSpaceSpectralSequenceCoefficientMap hX (φ ≫ ψ) =
      filteredSpaceSpectralSequenceCoefficientMap hX φ ≫
        filteredSpaceSpectralSequenceCoefficientMap hX ψ := by
  rw [filteredSpaceSpectralSequenceCoefficientMap_def,
    filteredSpaceSpectralSequenceCoefficientMap_def,
    filteredSpaceSpectralSequenceCoefficientMap_def, filteredSpaceCoefficientFiltrationMap_comp,
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]

/-- On the stage `F_b`, identified with the singular chains of `X b`, the morphism of filtrations
induced by `φ` is the chain map induced by `φ` on the singular chains of `X b`. -/
@[reassoc]
private lemma filteredSpaceCoefficientFiltrationMap_app_comp_chainFiltrationIso_hom
    (b : ℤ) :
    (filteredSpaceCoefficientFiltrationMap hX φ).app b ≫
        (CochainComplex.filtrationFunctorObjIso _
            (monotone_chainFiltration ((singularChainComplexFunctor A).obj R') hX) b).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (chainFiltrationIso ((singularChainComplexFunctor A).obj R') X b).hom =
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_chainFiltration ((singularChainComplexFunctor A).obj R) hX) b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (chainFiltrationIso ((singularChainComplexFunctor A).obj R) X b).hom ≫
            extendMap (((singularChainComplexFunctor A).map φ).app (TopPair.ofSubset (X b)).snd)
              ComplexShape.embeddingDownNat := by
  refine (cancel_mono (chainFiltrationι ((singularChainComplexFunctor A).obj R') X b)).1 ?_
  simp only [Category.assoc, chainFiltrationIso_hom_comp_chainFiltrationι,
    chainFiltrationι_coefficient_naturality, chainFiltrationIso_hom_comp_chainFiltrationι_assoc,
    Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]
  exact (filteredSpaceCoefficientFiltrationMap_app_comp hX φ (b : EInt)).trans
    (Category.assoc _ _ _)

/-- On the graded pieces `F_b / F_a`, identified with relative singular chains, the morphism of
filtrations induced by `φ` is the chain map induced by `φ` on the relative singular chains of the
pair `(X b, X a)`. -/
private lemma cokernelMap_comp_cokernelFiltrationFunctorMapIso_hom_coefficient {a b : ℤ}
    (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((filteredSpaceCoefficientFiltrationMap hX φ).naturality f).symm ≫
        (cokernelFiltrationFunctorMapIso R' hX f).hom =
      (cokernelFiltrationFunctorMapIso R hX f).hom ≫
        extendMap (((SSetPair.chainComplexFunctor A).map φ).app (TopPair.toSSetPair.obj
          (TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f))))))
          ComplexShape.embeddingDownNat := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  simp only [cokernel.map, cokernel.π_desc_assoc, Category.assoc,
    π_cokernelFiltrationFunctorMapIso_hom, π_cokernelFiltrationFunctorMapIso_hom_assoc]
  have hab := WithBotTop.coe_le_coe.mp (leOfHom f)
  -- The quotient maps to relative chains are natural in the coefficients.
  have h : extendMap ((TopPair.ofInclusion (hX hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
      extendMap (((SSetPair.chainComplexFunctor A).map φ).app
        (TopPair.toSSetPair.obj (TopPair.ofInclusion (hX hab)))) ComplexShape.embeddingDownNat =
      extendMap (((singularChainComplexFunctor A).map φ).app (TopPair.ofSubset (X b)).snd)
          ComplexShape.embeddingDownNat ≫
      extendMap ((TopPair.ofInclusion (hX hab)).singularChainComplexπ R')
        ComplexShape.embeddingDownNat := by
    exact (extendMap_comp _ _ _).symm.trans <|
      (congrArg (extendMap · ComplexShape.embeddingDownNat) (congrArg (fun η ↦ η.app
        (TopPair.toSSetPair.obj (TopPair.ofInclusion (hX hab))))
          ((SSetPair.chainComplexFunctorπ A).naturality φ)).symm).trans (extendMap_comp _ _ _)
  refine (filteredSpaceCoefficientFiltrationMap_app_comp_chainFiltrationIso_hom_assoc hX φ b
    _).trans ?_
  rw [← h]
  exact congrArg (_ ≫ ·) <| congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

/-- **The morphism of spectral sequences of a morphism of coefficients on the first page.** Let
`φ : R ⟶ R'` be a morphism of coefficients. Under the identifications of the first pages with
relative singular homology (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`), the morphism of
spectral sequences induced by `φ` is, at `(p, q)`, the map
`Hₙ(X (q + 1), X q; R) ⟶ Hₙ(X (q + 1), X q; R')` induced by `φ` on relative singular chains,
where `p + q = -n`. -/
@[reassoc]
theorem filteredSpaceSpectralSequenceFirstPageXIso_hom_coefficient_naturality (pq : ℤ × ℤ)
    (a b : ℤ) (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ)
    (hn : m = -n) :
    ((filteredSpaceSpectralSequenceCoefficientMap hX φ).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R' hX pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor A).map φ).app
          (TopPair.toSSetPair.obj (TopPair.ofInclusion (hX (by lia : a ≤ b))))) n := by
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, Iso.trans_hom,
    filteredSpaceSpectralSequenceCoefficientMap_def]
  rw [CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality_assoc]
  refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  -- As for `TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`, the complexes are
  -- indexed through the proof `hX hab`, so the steps are composed explicitly.
  exact (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans <|
    (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ m ≫ _)
      (cokernelMap_comp_cokernelFiltrationFunctorMapIso_hom_coefficient hX φ _)).trans <|
      (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).trans <|
        (congrArg
          (HomologicalComplex.homologyMap (cokernelFiltrationFunctorMapIso R hX _).hom m ≫ ·)
          (extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

/-- **The comparison theorem for morphisms of coefficients.** If a morphism of coefficients
`φ : R ⟶ R'` induces isomorphisms `Hₙ(X (q + 1), X q; R) ≅ Hₙ(X (q + 1), X q; R')` for every `q`
and `n`, then the induced morphism of spectral sequences is an isomorphism on every object of every
page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_filteredSpaceSpectralSequenceCoefficientMap_hom_f
    (h : ∀ (q : ℤ) (n : ℕ), IsIso (HomologicalComplex.homologyMap
      (((SSetPair.chainComplexFunctor A).map φ).app (TopPair.toSSetPair.obj
        (TopPair.ofInclusion (hX (Int.le_add_one le_rfl : q ≤ q + 1))))) n))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((filteredSpaceSpectralSequenceCoefficientMap hX φ).hom r hr).f pq) := by
  refine isIso_hom_f_of_isIso_page_two R hX _ (fun pq n hn ↦ ?_) r hr pq
  have e := filteredSpaceSpectralSequenceFirstPageXIso_hom_coefficient_naturality hX φ pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn
  rw [← Iso.eq_comp_inv] at e
  have := h pq.2 n
  rw [e]
  infer_instance

section Bifunctoriality

variable {Y' : TopCat.{w}} {X' : ℤ → Set Y'} (hX' : Monotone X') (g : Y ⟶ Y')
  (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- The morphisms of filtered singular chains induced by a map of filtered spaces and by a
morphism of coefficients commute. -/
@[reassoc]
lemma chainFiltrationMap_comp_filteredSpaceCoefficientFiltrationMap :
    chainFiltrationMap (𝟙 _) hX hX' g hg ≫ filteredSpaceCoefficientFiltrationMap hX' φ =
      filteredSpaceCoefficientFiltrationMap hX φ ≫ chainFiltrationMap (𝟙 _) hX hX' g hg := by
  ext a : 2
  rw [← cancel_mono (CochainComplex.filtrationFunctorArrow _
    (monotone_chainFiltration ((singularChainComplexFunctor A).obj R') hX') a)]
  simp only [NatTrans.comp_app, Category.assoc, filteredSpaceCoefficientFiltrationMap_app_comp,
    chainFiltrationMap_app_comp, chainFiltrationMap_app_comp_assoc,
    filteredSpaceCoefficientFiltrationMap_app_comp_assoc, ← extendMap_comp, NatTrans.id_app,
    Category.comp_id]
  rw [((singularChainComplexFunctor A).map φ).naturality]

/-- **The spectral sequence of a filtered space is a bifunctor**: the morphisms of spectral
sequences induced by a map of filtered spaces and by a morphism of coefficients commute. -/
@[reassoc]
lemma filteredSpaceSpectralSequenceMap_comp_filteredSpaceSpectralSequenceCoefficientMap :
    filteredSpaceSpectralSequenceMap R hX hX' g hg ≫
        filteredSpaceSpectralSequenceCoefficientMap hX' φ =
      filteredSpaceSpectralSequenceCoefficientMap hX φ ≫
        filteredSpaceSpectralSequenceMap R' hX hX' g hg := by
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceSpectralSequenceMap_def,
    filteredSpaceSpectralSequenceCoefficientMap_def,
    filteredSpaceSpectralSequenceCoefficientMap_def,
    ← Abelian.SpectralObject.spectralSequenceMap_comp,
    ← Abelian.SpectralObject.spectralSequenceMap_comp, ← CochainComplex.spectralObjectMap_comp,
    ← CochainComplex.spectralObjectMap_comp,
    chainFiltrationMap_comp_filteredSpaceCoefficientFiltrationMap]

end Bifunctoriality

end CoefficientNaturality

end TauCeti
