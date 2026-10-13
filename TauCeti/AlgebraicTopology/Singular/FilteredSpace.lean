/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Topology.Category.TopPair

/-!
# The spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular chains of the `X q`
form an increasing filtration of the singular chains of `Y`
(`TauCeti.singularChainFiltration`), and this file studies the spectral sequence of that filtered
complex (`TauCeti.filteredSpaceSpectralSequence`). It is the spectral sequence of a filtered
complex from `TauCeti.Algebra.Homology.SpectralSequence.Filtered`, which uses cochain complexes
indexed by `ℤ`, so singular chains in degree `n` are placed in degree `-n` along
`ComplexShape.embeddingDownNat`.

* **Graded pieces.** The quotient `F_b / F_a` of two stages of the filtration is the relative
  singular chain complex of the pair `(X b, X a)` (`TauCeti.singularChainFiltrationCokernelIso`),
  because the singular chain sequence of a pair is short exact.
* **First page.** The object at `(p, q)` on the first page (numbered `2` in the indexing of
  `CochainComplex.spectralSequence`) is the relative singular homology `Hₙ(X (q + 1), X q)` with
  `p + q = -n` (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`); it vanishes when
  `p + q > 0`.
* **First differential.** The differential from `(p, q)` to `(p + 2, q - 1)` is the connecting
  map `Hₙ₊₁(X (q + 1), X q) ⟶ Hₙ(X q, X (q - 1))` of the triple `(X (q + 1), X q, X (q - 1))`
  (`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`). The proof identifies the sequence
  of graded pieces `F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q`, whose connecting map is the
  first differential (`CochainComplex.spectralSequence_first_page_d_eq`), with the relative
  singular chain sequence of the triple.
* **Convergence.** The abutment in degree `-n` is `Hₙ(Y)` (`TauCeti.filteredSpaceAbutmentIso`).
  When `X a = ∅` and `X b = Y`, the filtration is finite and the spectral sequence converges
  strongly (`TauCeti.filteredSpaceSpectralSequencePageXIsoGradedOfFinite`).

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

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y : TopCat.{w}}

/-- The singular chains of the subspace of a pair form a subcomplex of those of the ambient
space, also after reindexing as cochain complexes along `n ↦ -n`. -/
private lemma mono_extendMap_singularChainComplexMap (P : TopPair.{w}) :
    Mono (extendMap (SSet.chainComplexMap (TopCat.toSSet.map P.map) R)
      ComplexShape.embeddingDownNat) :=
  ((P.shortExact_singularChainComplexShortComplex R).extend _).mono_f

variable (X : ℤ → Set Y)

/-- The inclusion of the singular chains of `X q` into those of `Y`, with both chain complexes
reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def singularChainFiltrationι (q : ℤ) :
    ((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex R).extend
        ComplexShape.embeddingDownNat ⟶
      ((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat :=
  extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R) _

instance (q : ℤ) : Mono (singularChainFiltrationι R X q) :=
  mono_extendMap_singularChainComplexMap R (TopPair.ofSubset (X q))

/-- The filtration of the singular chains of `Y` by the singular chains of the subsets `X q`,
with the chain complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def singularChainFiltration (q : ℤ) :
    Subobject (((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (singularChainFiltrationι R X q)

/-- The `q`-th stage of the filtration is the reindexed singular chain complex of `X q`. -/
def singularChainFiltrationIso (q : ℤ) :
    (singularChainFiltration R X q : CochainComplex A ℤ) ≅
      ((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex R).extend
        ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (singularChainFiltrationι R X q)

/-- The identification of the `q`-th stage of the filtration with the singular chains of `X q`
is compatible with the inclusions into the singular chains of `Y`. -/
@[reassoc (attr := simp)]
lemma singularChainFiltrationIso_hom_comp_singularChainFiltrationι (q : ℤ) :
    (singularChainFiltrationIso R X q).hom ≫ singularChainFiltrationι R X q =
      (singularChainFiltration R X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the singular chains of `X a` into those of `Y` factors
through the inclusion of the pair `(X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_singularChainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofInclusion hab).map) R)
        ComplexShape.embeddingDownNat ≫ singularChainFiltrationι R X b =
      singularChainFiltrationι R X a := by
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) <|
    (Functor.map_comp _ _ _).symm.trans <| congrArg _ (Functor.map_comp _ _ _).symm

/-- The filtration of singular chains is monotone in the subsets. -/
lemma singularChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    singularChainFiltration R X a ≤ singularChainFiltration R X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_singularChainFiltrationι R hab)

/-- Under the identifications of the stages of the filtration with singular chain complexes, the
inclusion `F_a ⟶ F_b` is induced by the inclusion `X a ⊆ X b`. -/
@[reassoc]
lemma ofLE_comp_singularChainFiltrationIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    Subobject.ofLE _ _ (singularChainFiltration_mono R hab) ≫
        (singularChainFiltrationIso R X b).hom =
      (singularChainFiltrationIso R X a).hom ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofInclusion hab).map) R)
          ComplexShape.embeddingDownNat := by
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to unfolding
  -- `MorphismProperty.Arrow.mk`, so the composites are compared by `Eq.trans` rather than `rw`.
  refine (cancel_mono (singularChainFiltrationι R X b)).1 ?_
  calc _ = (singularChainFiltration R X a).arrow :=
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
          (singularChainFiltrationIso_hom_comp_singularChainFiltrationι R X b)).trans
            (Subobject.ofLE_arrow _)
    _ = _ := ((Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
          (extendMap_comp_singularChainFiltrationι R hab)).trans
            (singularChainFiltrationIso_hom_comp_singularChainFiltrationι R X a)).symm

/-- An increasing family of subsets gives an increasing filtration of singular chains. -/
lemma monotone_singularChainFiltration (hX : Monotone X) :
    Monotone (singularChainFiltration R X) :=
  fun _ _ h ↦ singularChainFiltration_mono R (hX h)

/-- The stage of the filtration at an empty subset is zero. -/
lemma singularChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    singularChainFiltration R X a = ⊥ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  have hz : IsZero (((TopCat.toSSet.obj (TopPair.ofSubset (X a)).snd).chainComplex R).extend
      ComplexShape.embeddingDownNat) :=
    (ComplexShape.embeddingDownNat.extendFunctor A).map_isZero
      (SSet.isZero_chainComplex (X := (TopPair.toSSetPair.obj (TopPair.ofSubset (X a))).left) R)
  exact Subobject.mk_eq_bot_iff_zero.2 (hz.eq_of_src _ _)

/-- The stage of the filtration at the whole space is everything. -/
lemma singularChainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) :
    singularChainFiltration R X b = ⊤ := by
  have : IsIso (TopPair.ofSubset (X b)).map := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
      (hb ▸ isOpen_univ : IsOpen (X b)).isOpenEmbedding_subtypeVal.isOpenMap
    exact ⟨⟨y, hb ▸ Set.mem_univ y⟩, rfl⟩
  have : IsIso (singularChainFiltrationι R X b) := by
    rw [singularChainFiltrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor A) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The quotient `F_b / F_a` of two stages of the filtration of the singular chains of `Y` by
the singular chains of the `X q` is the relative singular chain complex of the pair `(X b, X a)`,
reindexed along `n ↦ -n`. The isomorphism is induced by the quotient map from the singular chains
of `X b` (`TauCeti.π_singularChainFiltrationCokernelIso_hom`). -/
def singularChainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _ (singularChainFiltration_mono R hab)) ≅
      ((TopPair.ofInclusion hab).singularChainComplex R).extend ComplexShape.embeddingDownNat :=
  have hS := ((TopPair.ofInclusion hab).shortExact_singularChainComplexShortComplex R).extend
    ComplexShape.embeddingDownNat
  cokernel.mapIso _
      (extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofInclusion hab).map) R)
        ComplexShape.embeddingDownNat)
      (singularChainFiltrationIso R X a) (singularChainFiltrationIso R X b)
      (ofLE_comp_singularChainFiltrationIso_hom R hab) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The identification of `F_b / F_a` with relative singular chains is induced by the quotient
map from the singular chains of `X b` to those of the pair `(X b, X a)`. -/
@[reassoc (attr := simp)]
lemma π_singularChainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (singularChainFiltrationCokernelIso R hab).hom =
      (singularChainFiltrationIso R X b).hom ≫
        extendMap ((TopPair.ofInclusion hab).singularChainComplexπ R)
          ComplexShape.embeddingDownNat := by
  -- The first factor is `cokernel.map`, which is `cokernel.desc` of the composite with the
  -- quotient map, and the second sends that quotient map to the cokernel cofork's map.
  refine (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

variable (hX : Monotone X)

/-- The quotient of two stages of the filtration of singular chains, as the cokernel of a
transition map of the functor `CochainComplex.filtrationFunctor` of the filtration, is the
reindexed relative singular chain complex of the corresponding pair. -/
private def cokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX)).map f) ≅
      ((TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplex
        R).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _ _ (CochainComplex.filtrationFunctorObjCoeIso _ _ a)
      (CochainComplex.filtrationFunctorObjCoeIso _ _ b)
      (CochainComplex.filtrationFunctor_map_comp_objCoeIso_hom _ _ f) ≪≫
    singularChainFiltrationCokernelIso R _

@[reassoc]
private lemma π_cokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIso R hX f).hom =
      (CochainComplex.filtrationFunctorObjCoeIso _ _ b).hom ≫
        (singularChainFiltrationIso R X b).hom ≫
          extendMap ((TopPair.ofInclusion
            (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
            ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (π_singularChainFiltrationCokernelIso_hom R _)

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

/-- The first page of the spectral sequence of a filtered space vanishes in positive total
degree `p + q`, since singular chains are concentrated in nonpositive cohomological degrees. -/
lemma isZero_filteredSpaceSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 < pq.1 + pq.2) :
    IsZero (((filteredSpaceSpectralSequence R hX).page 2).X pq) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingDownNat _ fun n hn ↦ by
      have : -(n : ℤ) = pq.1 + pq.2 := hn
      lia).isZero_homology)
    (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
      (homologyFunctor A _ _).mapIso (cokernelFiltrationFunctorMapIso R hX _))

/-- **The abutment of the spectral sequence of a filtered space** in degree `-n` is the singular
homology `Hₙ(Y)`. -/
def filteredSpaceAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX))).abutment
        (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj Y :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

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
    (singularChainFiltration_eq_bot R ha) (singularChainFiltration_eq_top R hb) r hr pq hra hrb

section FirstDifferential

variable (q : ℤ)

/-- The triple `(X (q + 1), X q, X (q - 1))` of three consecutive stages of a filtration. -/
private abbrev filtrationTriple : TopTriple.{w} :=
  TopTriple.ofInclusions (hX (by lia : q - 1 ≤ q)) (hX (by lia : q ≤ q + 1))

/-- The transition map `F_a ⟶ F_b` of the functor of the filtration of singular chains. -/
private abbrev fMap {a b : ℤ} (h : (a : EInt) ≤ b) :=
  (CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX)).map (homOfLE h)

/-- The sequence `F_q/F_{q-1} ⟶ F_{q+1}/F_{q-1} ⟶ F_{q+1}/F_q` of graded pieces, written with
explicit cokernels. It is the last row of `kernelCokernelCompSequence.snakeInput`. -/
private abbrev gradedShortComplex : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (cokernel.map (fMap R hX (by simp : ((q - 1 : ℤ) : EInt) ≤ q))
      (fMap R hX (by simp : ((q - 1 : ℤ) : EInt) ≤ q) ≫
        fMap R hX (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))) (𝟙 _)
      (fMap R hX (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))) (by simp))
    (cokernel.map (fMap R hX (by simp : ((q - 1 : ℤ) : EInt) ≤ q) ≫
        fMap R hX (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))
      (fMap R hX (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))
      (fMap R hX (by simp : ((q - 1 : ℤ) : EInt) ≤ q)) (𝟙 _) (by simp))
    (kernelCokernelCompSequence.snakeInput _ _).L₃.zero

private lemma gradedShortComplex_shortExact : (gradedShortComplex R hX q).ShortExact :=
  kernelCokernelCompSequence_snakeInput_L₃_shortExact _ _

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
    extendMap ((TopPair.ofInclusion (hX (by lia : q - 1 ≤ q + 1))).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
      extendMap (TopPair.singularChainComplexMap
        (TopTriple.totalToOuter.app (filtrationTriple hX q)) R) ComplexShape.embeddingDownNat =
    extendMap ((TopPair.ofInclusion (hX (by lia : q ≤ q + 1))).singularChainComplexπ R)
      ComplexShape.embeddingDownNat :=
  (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _)
    ((filtrationTriple hX q).singularChainComplexπ_comp_totalToOuter R)

/-- The identification of the sequence of graded pieces with the reindexed relative singular
chain sequence of the triple `(X (q + 1), X q, X (q - 1))`. -/
private def gradedShortComplexHom : gradedShortComplex R hX q ⟶ tripleShortComplex R hX q where
  τ₁ := (cokernelFiltrationFunctorMapIso R hX _).hom
  τ₂ := (cokernelIsoOfEq (Functor.map_comp _ _ _).symm ≪≫
    cokernelFiltrationFunctorMapIso R hX _).hom
  τ₃ := (cokernelFiltrationFunctorMapIso R hX _).hom
  comm₁₂ := by
    refine (cancel_epi (cokernel.π _)).1 ?_
    rw [π_cokernelFiltrationFunctorMapIso_hom_assoc, cokernel.π_desc_assoc, Category.assoc,
      Iso.trans_hom, π_comp_cokernelIsoOfEq_hom_assoc, π_cokernelFiltrationFunctorMapIso_hom,
      CochainComplex.filtrationFunctor_map_comp_objCoeIso_hom_assoc]
    -- The identification of `F_{q+1}` with the chains of `X (q + 1)` lands in the chains of the
    -- subspace `X (q + 1)` of `Y`, which are those of the ambient space of the pair
    -- `(X (q + 1), X (q - 1))` only up to unfolding `MorphismProperty.Arrow.mk`; `erw` matches
    -- the composite up to that unfolding.
    erw [ofLE_comp_singularChainFiltrationIso_hom_assoc R (hX (by lia : q ≤ q + 1))]
    exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (extendMap_π_comp_innerToTotal R hX q)).trans (Category.assoc _ _ _).symm)
  comm₂₃ := by
    refine (cancel_epi (cokernel.π _)).1 ?_
    rw [Iso.trans_hom, Category.assoc, π_comp_cokernelIsoOfEq_hom_assoc,
      π_cokernelFiltrationFunctorMapIso_hom_assoc, cokernel.π_desc_assoc, Category.id_comp,
      π_cokernelFiltrationFunctorMapIso_hom]
    exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (extendMap_π_comp_totalToOuter R hX q))

/-- The connecting maps of the sequence of graded pieces and of the triple
`(X (q + 1), X q, X (q - 1))` agree under the identifications of the graded pieces with relative
singular chains. -/
private lemma δ_comp_extendHomologyIso_hom (n : ℕ) (m₀ m₁ : ℤ) (h₀ : m₀ = -(n + 1 : ℕ))
    (h₁ : m₁ = -n) (h : (ComplexShape.up ℤ).Rel m₀ m₁) :
    (gradedShortComplex_shortExact R hX q).δ m₀ m₁ h ≫
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
  -- The row of graded pieces in the statement of `spectralSequence_first_page_d_eq` is
  -- `gradedShortComplex` up to unfolding `kernelCokernelCompSequence.snakeInput`, so the comparison
  -- of connecting maps is applied with `Eq.trans` rather than `rw`.
  refine (congrArg (· ≫ _) ((Iso.eq_comp_inv ((homologyFunctor A _ (p + q + 1)).mapIso
      (cokernelFiltrationFunctorMapIso R hX _) ≪≫ extendHomologyIso _ _ _)).2
    ((δ_comp_extendHomologyIso_hom R hX q n _ _ hn (by lia) rfl).trans
      (Category.assoc _ _ _).symm))).trans ?_
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end FirstDifferential

end TauCeti
