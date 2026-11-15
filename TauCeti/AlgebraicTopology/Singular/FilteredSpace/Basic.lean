/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor
public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular chains of the `X q`
form an increasing filtration of the singular chains of `Y`
(`TauCeti.singularChainFiltration`), and this file studies the spectral sequence of that filtered
complex (`TauCeti.filteredSpaceSpectralSequence`). It is the instance for simplicial singular chains
of the spectral sequence `TauCeti.subspaceChainSpectralSequence` of a filtered space for a chain
functor, which uses cochain complexes indexed by `ℤ`, so singular chains in degree `n` are placed
in degree `-n` along `ComplexShape.embeddingDownNat`.

* **Graded pieces.** The quotient `F_b / F_a` of two stages of the filtration is the relative
  singular chain complex of the pair `(X b, X a)` (`TauCeti.singularChainFiltrationCokernelIso`),
  because the relative singular chain complex of a pair is the cokernel of the map of singular
  chains (`TopPair.cokernelSingularChainComplexIso`).
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
* **Convergence.** The abutment in degree `-n` is `Hₙ(Y)` (`TauCeti.filteredSpaceAbutmentIso`).
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
  (`TauCeti.isIso_filteredSpaceSpectralSequenceMap_hom_f`).

For the skeletal filtration of a CW complex the first page consists of the groups
`Hₙ(Xⁿ, Xⁿ⁻¹)`, and its differential is the connecting map of three consecutive skeleta, which is
the differential of `TauCeti.cellularChainComplex` by
`TauCeti.cellularDifferential_eq_singularHomologyδ`. Filtering the total space of
a fibration by the preimages of the skeleta of the base gives the Serre spectral sequence.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex AlgebraicTopology

universe w v u

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

namespace TauCeti

variable {Y : TopCat.{w}} (X : ℤ → Set Y)

/-- The filtration of the singular chains of `Y` by the singular chains of the subsets `X q`,
with the chain complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`:
the filtration `TauCeti.subspaceChainFiltration` of simplicial singular chains. -/
abbrev singularChainFiltration :
    ℤ → Subobject (((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat) :=
  subspaceChainFiltration ((singularChainComplexFunctor A).obj R) X

variable {X}

/-- An increasing family of subsets gives an increasing filtration of singular chains. -/
lemma monotone_singularChainFiltration (hX : Monotone X) :
    Monotone (singularChainFiltration R X) :=
  monotone_subspaceChainFiltration _ hX

/-- The stage of the filtration at an empty subset is zero. -/
@[simp]
lemma singularChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    singularChainFiltration R X a = ⊥ :=
  subspaceChainFiltration_eq_bot _ (fun Z _ ↦ SSet.isZero_chainComplex (TopCat.toSSet.obj Z) R) ha

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
    cokernel (Subobject.ofLE _ _ (subspaceChainFiltration_mono
      ((singularChainComplexFunctor A).obj R) hab)) ≅
      ((TopPair.ofInclusion hab).singularChainComplex R).extend ComplexShape.embeddingDownNat :=
  subspaceChainFiltrationCokernelIso _ hab ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor A).mapIso
      ((TopPair.ofInclusion hab).cokernelSingularChainComplexIso R)

/-- The identification of `F_b / F_a` with relative singular chains is induced by the quotient
map from the singular chains of `X b` to those of the pair `(X b, X a)`. -/
@[reassoc (attr := simp)]
lemma π_singularChainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (singularChainFiltrationCokernelIso R hab).hom =
      (subspaceChainFiltrationIso _ X b).hom ≫
        extendMap ((TopPair.ofInclusion hab).singularChainComplexπ R)
          ComplexShape.embeddingDownNat :=
  (π_subspaceChainFiltrationCokernelIso_hom_assoc _ hab _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (extendMap_π_comp_cokernelSingularChainComplexIso_hom R _)

/-- The quotient `F_b / F_a` of two stages of the filtration of singular chains has vanishing
cohomology in degree `m` when the relative singular homology `Hₙ(X b, X a)` vanishes for
`m = -n`. In positive degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_singularChainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (h : ∀ n : ℕ, m = -n → IsZero ((TopPair.ofInclusion hab).singularHomology R n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (subspaceChainFiltration_mono
      ((singularChainComplexFunctor A).obj R) hab))).homology m) :=
  isZero_homology_cokernel_subspaceChainFiltration _ hab m fun n hn ↦
    (h n hn).of_iso ((homologyFunctor A _ n).mapIso
      ((TopPair.ofInclusion hab).cokernelSingularChainComplexIso R))

variable (hX : Monotone X)

variable (X) in
/-- The `q`-th stage of the filtration of singular chains, with the singular chains of `X q` written
as the simplicial chains of its singular simplicial set. This is
`TauCeti.subspaceChainFiltrationIso` with its target restated, so that its composites with the
quotient maps onto relative singular chains are formed syntactically in the proofs below, where
`simp` cannot see through `singularChainComplexFunctor`. -/
private def singularChainFiltrationIso (q : ℤ) :
    (singularChainFiltration R X q : CochainComplex A ℤ) ≅
      ((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex R).extend
        ComplexShape.embeddingDownNat :=
  subspaceChainFiltrationIso _ X q

variable (X) in
/-- The inclusion of the singular chains of `X q` into those of `Y`. This is
`TauCeti.subspaceChainFiltrationι` with its source and map restated for simplicial singular
chains, like `singularChainFiltrationIso`. -/
private def singularChainFiltrationι (q : ℤ) :
    ((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex R).extend
        ComplexShape.embeddingDownNat ⟶
      ((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat :=
  subspaceChainFiltrationι ((singularChainComplexFunctor A).obj R) X q

/-- The singular chains of `X q` form a subcomplex of those of `Y`. Instance search does not
unfold `singularChainComplexFunctor` to match the restated source and target, so the instance for
`TauCeti.subspaceChainFiltrationι` is transferred explicitly. -/
private instance (q : ℤ) : Mono (singularChainFiltrationι R X q) :=
  inferInstanceAs (Mono (subspaceChainFiltrationι ((singularChainComplexFunctor A).obj R) X q))

variable (X) in
private lemma singularChainFiltrationι_def (q : ℤ) :
    singularChainFiltrationι R X q =
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R)
        ComplexShape.embeddingDownNat :=
  subspaceChainFiltrationι_def _ X q

variable (X) in
@[reassoc]
private lemma singularChainFiltrationIso_hom_comp_singularChainFiltrationι (q : ℤ) :
    (singularChainFiltrationIso R X q).hom ≫ singularChainFiltrationι R X q =
      (singularChainFiltration R X q).arrow :=
  subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι
    ((singularChainComplexFunctor A).obj R) X q

/-- The quotient of two stages of the filtration of singular chains, as the cokernel of a
transition map of the functor `CochainComplex.filtrationFunctor` of the filtration, is the
reindexed relative singular chain complex of the corresponding pair. -/
private def cokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX)).map f) ≅
      ((TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplex
        R).extend ComplexShape.embeddingDownNat :=
  subspaceChainCokernelFiltrationFunctorMapIso _ hX f ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor A).mapIso
      ((TopPair.ofInclusion _).cokernelSingularChainComplexIso R)

@[reassoc]
private lemma π_cokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIso R hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫
            extendMap ((TopPair.ofInclusion
              (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
              ComplexShape.embeddingDownNat :=
  (π_subspaceChainCokernelFiltrationFunctorMapIso_hom_assoc _ hX f _).trans <|
    congrArg (_ ≫ _ ≫ ·) <| (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (extendMap_π_comp_cokernelSingularChainComplexIso_hom R _)

/-- **The spectral sequence of a filtered space.** For an increasing family `X : ℤ → Set Y` of
subsets of a space `Y`, this is the spectral sequence of the filtration of the singular chains of
`Y` by the singular chains of the `X q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: singular chains in degree `n` sit in degree `-n`. -/
abbrev filteredSpaceSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX))

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
`TauCeti.subspaceChainSpectralSequenceFirstPageXIso` of the first page with the homology of the
cokernel of the map of singular chains of the pair, followed by the identification of that
cokernel with the relative singular chain complex. -/
lemma filteredSpaceSpectralSequenceFirstPageXIso_hom (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom =
      (subspaceChainSpectralSequenceFirstPageXIso _ hX pq a b ha hb m hm n hn).hom ≫
        homologyMap ((TopPair.ofInclusion (hX (by lia : a ≤ b))).cokernelSingularChainComplexIso
          R).hom n := by
  rw [subspaceChainSpectralSequenceFirstPageXIso_eq]
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, cokernelFiltrationFunctorMapIso,
    Iso.trans_hom, Category.assoc]
  -- The identifications are composites of isomorphisms whose types mention the pair
  -- `(X b, X a)` through `hX`, so they are composed with terms rather than `rw`.
  exact congrArg (_ ≫ ·) <|
    ((congrArg (· ≫ _) ((homologyFunctor A _ m).map_comp _ _)).trans
      (Category.assoc _ _ _)).trans <|
      (congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

/-- The first page of the spectral sequence of a filtered space vanishes in positive total
degree `p + q`, since singular chains are concentrated in nonpositive cohomological degrees. -/
lemma isZero_filteredSpaceSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 < pq.1 + pq.2) :
    IsZero (((filteredSpaceSpectralSequence R hX).page 2).X pq) :=
  isZero_subspaceChainSpectralSequence_page_two_X _ hX pq h

/-- **The abutment of the spectral sequence of a filtered space** in degree `-n` is the singular
homology `Hₙ(Y)`. -/
abbrev filteredSpaceAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX))).abutment
        (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj Y :=
  subspaceChainAbutmentIso _ hX n

/-- **Strong convergence of the spectral sequence of a finite filtration of a space.** If
`X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 2` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the filtration of
the abutment in degree `p + q`, which is `H_{-(p+q)}(Y)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def filteredSpaceSpectralSequencePageXIsoGradedOfFinite {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((filteredSpaceSpectralSequence R hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration R hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (singularChainFiltration_eq_bot R ha) (subspaceChainFiltration_eq_top _ hb) r hr pq hra hrb

section FirstDifferential

variable (q : ℤ)

/-- The triple `(X (q + 1), X q, X (q - 1))` of three consecutive stages of a filtration. -/
private abbrev filtrationTriple : TopTriple.{w} :=
  TopTriple.ofInclusions (hX (by lia : q - 1 ≤ q)) (hX (by lia : q ≤ q + 1))

/-- The transition map `F_a ⟶ F_b` of the functor of the filtration of singular chains. -/
private abbrev fMap {a b : ℤ} (h : (a : EInt) ≤ b) :=
  (CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX)).map (homOfLE h)

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
    rw [← Subobject.ofLE_comp_ofLE_assoc _ (singularChainFiltration R X q) _
      (CochainComplex.filtrationEInt_coe _ q).le
      (subspaceChainFiltration_mono _ (hX (by lia : q ≤ q + 1)))]
    -- The identification of `F_{q+1}` with the chains of `X (q + 1)` lands in the chains of the
    -- subspace `X (q + 1)` of `Y`, which are those of the ambient space of the pair
    -- `(X (q + 1), X (q - 1))` only up to unfolding `MorphismProperty.Arrow.mk`, and the stage
    -- identification is `singularChainFiltrationIso`; `erw` matches the composite up to unfolding.
    erw [ofLE_comp_subspaceChainFiltrationIso_hom_assoc ((singularChainComplexFunctor A).obj R)
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
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end FirstDifferential

section Naturality

variable {Y' Y'' : TopCat.{w}} {X' : ℤ → Set Y'} (hX' : Monotone X') {X'' : ℤ → Set Y''}
  (hX'' : Monotone X'') (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- A map carrying `X q` into `X' q` carries the singular chains of `X q` into those of `X' q`. -/
@[reassoc]
private lemma singularChainFiltrationι_naturality (q : ℤ) :
    extendMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)))) R)
        ComplexShape.embeddingDownNat ≫ singularChainFiltrationι R X' q =
      singularChainFiltrationι R X q ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat := by
  -- The map of pairs `(Y, X q) ⟶ (Y', X' q)` induced by `g` commutes with the inclusions; push
  -- this square through the singular chain functors.
  have h := congrArg (fun φ ↦ extendMap (SSet.chainComplexMap (TopCat.toSSet.map φ) R)
    ComplexShape.embeddingDownNat) (TopPair.Hom.w (TopPair.ofSubsetMap g (hg q)))
  simp only [Functor.map_comp, extendMap_comp] at h
  rw [TopPair.ofSubsetMap_fst] at h
  rw [singularChainFiltrationι_def, singularChainFiltrationι_def]
  exact h

include hg in
private lemma factors_singularChainFiltration (q : ℤ) :
    (singularChainFiltration R X' q).Factors ((singularChainFiltration R X q).arrow ≫
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat) :=
  (Subobject.factors_iff _ _).2 ⟨(singularChainFiltrationIso R X q).hom ≫ extendMap
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q)))) R)
        ComplexShape.embeddingDownNat ≫ (singularChainFiltrationIso R X' q).inv,
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (subspaceChainFiltrationIso_inv_comp_arrow
        ((singularChainComplexFunctor A).obj R) X' q)).trans
        (singularChainFiltrationι_naturality R g hg q))).trans
      (singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc R X q _)⟩

include g hg in
/-- **The morphism of filtered complexes induced by a map of filtered spaces.** A continuous map
`g : Y ⟶ Y'` carrying each `X q` into `X' q` induces, on singular chains, a morphism from the
filtration of the singular chains of `Y` by those of the `X q` to the filtration of the singular
chains of `Y'` by those of the `X' q`. -/
def filteredSpaceFiltrationMap :
    CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX') :=
  CochainComplex.filtrationFunctorMap _ _ _ (factors_singularChainFiltration R g hg)

/-- The components of `TauCeti.filteredSpaceFiltrationMap` are the restrictions of the chain map
induced by `g`. -/
@[reassoc (attr := simp)]
lemma filteredSpaceFiltrationMap_app_comp (a : EInt) :
    (filteredSpaceFiltrationMap R hX hX' g hg).app a ≫
        CochainComplex.filtrationFunctorArrow _ (monotone_singularChainFiltration R hX') a =
      CochainComplex.filtrationFunctorArrow _ (monotone_singularChainFiltration R hX) a ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat :=
  (CochainComplex.filtrationFunctorMap_app_comp _ _ a).trans (Category.assoc _ _ _).symm

/-- The identity of a filtered space induces the identity of its filtered singular chains. -/
@[simp]
lemma filteredSpaceFiltrationMap_id (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) :
    filteredSpaceFiltrationMap R hX hX (𝟙 Y) h = 𝟙 _ := by
  rw [filteredSpaceFiltrationMap,
    CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _) (by simp),
    CochainComplex.filtrationFunctorMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of filtered
singular chains. -/
@[reassoc]
lemma filteredSpaceFiltrationMap_comp (g' : Y' ⟶ Y'') (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q))
    (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceFiltrationMap R hX hX'' (g ≫ g') hgg' =
      filteredSpaceFiltrationMap R hX hX' g hg ≫ filteredSpaceFiltrationMap R hX' hX'' g' hg' := by
  rw [filteredSpaceFiltrationMap, filteredSpaceFiltrationMap, filteredSpaceFiltrationMap,
    CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) _ ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g') R) _) (by simp),
    CochainComplex.filtrationFunctorMap_comp _ _ (factors_singularChainFiltration R g hg)
      (factors_singularChainFiltration R g' hg')]

include g hg in
/-- **The morphism of spectral sequences induced by a map of filtered spaces.** A continuous map
`g : Y ⟶ Y'` carrying each `X q` into `X' q` induces a morphism from the spectral sequence of the
filtration of `Y` by the `X q` to that of the filtration of `Y'` by the `X' q`. On the first page
it is the map induced by `g` on the relative singular homology of the steps
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`). -/
def filteredSpaceSpectralSequenceMap :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R hX' :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (filteredSpaceFiltrationMap R hX hX' g hg))

include g hg in
/-- `TauCeti.filteredSpaceSpectralSequenceMap` is the morphism of spectral sequences of the
morphism of spectral objects of `TauCeti.filteredSpaceFiltrationMap`. -/
lemma filteredSpaceSpectralSequenceMap_def :
    filteredSpaceSpectralSequenceMap R hX hX' g hg =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (filteredSpaceFiltrationMap R hX hX' g hg)) :=
  (rfl)

/-- The identity of a filtered space induces the identity of its spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceMap_id
    (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) :
    filteredSpaceSpectralSequenceMap R hX hX (𝟙 Y) h = 𝟙 _ := by
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceFiltrationMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of spectral
sequences. -/
@[reassoc]
lemma filteredSpaceSpectralSequenceMap_comp (g' : Y' ⟶ Y'')
    (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q)) (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceSpectralSequenceMap R hX hX'' (g ≫ g') hgg' =
      filteredSpaceSpectralSequenceMap R hX hX' g hg ≫
        filteredSpaceSpectralSequenceMap R hX' hX'' g' hg' := by
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceSpectralSequenceMap_def,
    filteredSpaceSpectralSequenceMap_def, filteredSpaceFiltrationMap_comp R hX hX' hX'' g hg g' hg',
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]

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
    (TopPair.Hom.fst (filteredSpaceStepMap hX hX' g hg hab) x).1 = g x.1 :=
  congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)

/-- The subspace component of the map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by `g` sends
`x` to `g x`. -/
@[simp]
lemma filteredSpaceStepMap_snd_apply {a b : ℤ} (hab : a ≤ b)
    (x : (TopPair.ofInclusion (hX hab)).snd) :
    (TopPair.Hom.snd (filteredSpaceStepMap hX hX' g hg hab) x).1 = g x.1 :=
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
private lemma filteredSpaceFiltrationMap_app_comp_singularChainFiltrationIso_hom (b : ℤ) :
    (filteredSpaceFiltrationMap R hX hX' g hg).app b ≫
        (CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX') b).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (singularChainFiltrationIso R X' b).hom =
      (CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫ extendMap (SSet.chainComplexMap
            (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) R)
            ComplexShape.embeddingDownNat := by
  refine (cancel_mono (singularChainFiltrationι R X' b)).1 ?_
  simp only [Category.assoc, singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
    singularChainFiltrationι_naturality,
    singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc,
    Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]
  exact (filteredSpaceFiltrationMap_app_comp R hX hX' g hg (b : EInt)).trans (Category.assoc _ _ _)

/-- On the graded pieces `F_b / F_a`, identified with relative singular chains, the morphism of
filtrations induced by `g` is the chain map induced by `g` on the pairs `(X b, X a)`. -/
private lemma cokernelMap_comp_cokernelFiltrationFunctorMapIso_hom {a b : ℤ}
    (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((filteredSpaceFiltrationMap R hX hX' g hg).naturality f) ≫
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
      extendMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) R)
        ComplexShape.embeddingDownNat ≫
      extendMap ((TopPair.ofInclusion (hX' hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat := by
    rw [← extendMap_comp, ← TopPair.singularChainComplexπ_pair_naturality,
      fst_filteredSpaceStepMap]
    exact extendMap_comp _ _ _
  refine (filteredSpaceFiltrationMap_app_comp_singularChainFiltrationIso_hom_assoc R hX hX' g hg b
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
  refine SpectralSequence.Hom.isIso_hom_f_of_le _ 2 le_rfl (fun pq ↦ ?_) r hr pq
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact (isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos).isIso
      (isZero_filteredSpaceSpectralSequence_page_two_X R hX' pq hpos) _
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  have e := filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality R hX hX' g hg pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn
  rw [← Iso.eq_comp_inv] at e
  have := h pq.2 n
  rw [e]
  infer_instance

end Naturality

end TauCeti
