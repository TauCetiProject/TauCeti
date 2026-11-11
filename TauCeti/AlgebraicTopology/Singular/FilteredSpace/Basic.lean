/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

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

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y : TopCat.{w}}

variable (X : ℤ → Set Y)

/-- The inclusion of the singular chains of `X q` into those of `Y`, with both chain complexes
reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def singularChainFiltrationι (q : ℤ) :
    ((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex R).extend
        ComplexShape.embeddingDownNat ⟶
      ((TopCat.toSSet.obj Y).chainComplex R).extend ComplexShape.embeddingDownNat :=
  extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R) _

/-- The inclusion of the singular chains of `X q` into those of `Y` is induced by the inclusion
of the subspace `X q`. -/
lemma singularChainFiltrationι_def (q : ℤ) :
    singularChainFiltrationι R X q =
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R)
        ComplexShape.embeddingDownNat := by
  rw [singularChainFiltrationι]

/-- The singular chains of `X q` form a subcomplex of those of `Y`, also after reindexing. -/
instance (q : ℤ) : Mono (singularChainFiltrationι R X q) := by
  have : Mono (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R) :=
    ((TopPair.ofSubset (X q)).shortExact_singularChainComplexShortComplex R).mono_f
  rw [singularChainFiltrationι_def]
  exact HomologicalComplex.mono_extendMap _ _

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
          ComplexShape.embeddingDownNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := singularChainFiltrationι R X a) (f₂ := singularChainFiltrationι R X b) _
    (extendMap_comp_singularChainFiltrationι R hab)).trans (Category.assoc _ _ _).symm

/-- An increasing family of subsets gives an increasing filtration of singular chains. -/
lemma monotone_singularChainFiltration (hX : Monotone X) :
    Monotone (singularChainFiltration R X) :=
  fun _ _ h ↦ singularChainFiltration_mono R (hX h)

/-- The stage of the filtration at an empty subset is zero. -/
@[simp]
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
@[simp]
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

/-- The quotient `F_b / F_a` of two stages of the filtration of singular chains has vanishing
cohomology in degree `m` when the relative singular homology `Hₙ(X b, X a)` vanishes for
`m = -n`. In positive degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_singularChainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (h : ∀ n : ℕ, m = -n → IsZero ((TopPair.ofInclusion hab).singularHomology R n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (singularChainFiltration_mono R hab))).homology m) := by
  refine IsZero.of_iso ?_
    ((homologyFunctor A _ m).mapIso (singularChainFiltrationCokernelIso R hab))
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = m
  · obtain ⟨n, hn⟩ := hm
    exact (h n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm
    exact (extend_exactAt _ _ m hm).isZero_homology

variable (hX : Monotone X)

/-- The quotient of two stages of the filtration of singular chains, as the cokernel of a
transition map of the functor `CochainComplex.filtrationFunctor` of the filtration, is the
reindexed relative singular chain complex of the corresponding pair. -/
private def cokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX)).map f) ≅
      ((TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplex
        R).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _ _
      (CochainComplex.filtrationFunctorObjIso _ _ a ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ a))
      (CochainComplex.filtrationFunctorObjIso _ _ b ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ b))
      (by simp only [Iso.trans_hom, Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE,
        reassoc_of% CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc]) ≪≫
    singularChainFiltrationCokernelIso R _

@[reassoc]
private lemma π_cokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIso R hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫
            extendMap ((TopPair.ofInclusion
              (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).singularChainComplexπ R)
              ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ _ ≫ ·) (π_singularChainFiltrationCokernelIso_hom R _)

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
      (singularChainFiltration_mono R (hX (by lia : q ≤ q + 1)))]
    -- The identification of `F_{q+1}` with the chains of `X (q + 1)` lands in the chains of the
    -- subspace `X (q + 1)` of `Y`, which are those of the ambient space of the pair
    -- `(X (q + 1), X (q - 1))` only up to unfolding `MorphismProperty.Arrow.mk`; `erw` matches
    -- the composite up to that unfolding.
    erw [ofLE_comp_singularChainFiltrationIso_hom_assoc R (hX (by lia : q ≤ q + 1))]
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

/-- The restriction `X q ⟶ X' q` of a map `g` carrying `X q` into `X' q`. -/
private abbrev restrictMap (q : ℤ) :
    (TopPair.ofSubset (X q)).snd ⟶ (TopPair.ofSubset (X' q)).snd :=
  TopCat.ofHom ⟨(hg q).restrict, g.hom.continuous.restrict (hg q)⟩

/-- A map carrying `X q` into `X' q` carries the singular chains of `X q` into those of `X' q`. -/
@[reassoc]
private lemma singularChainFiltrationι_naturality (q : ℤ) :
    extendMap (SSet.chainComplexMap (TopCat.toSSet.map (restrictMap g hg q)) R)
        ComplexShape.embeddingDownNat ≫ singularChainFiltrationι R X' q =
      singularChainFiltrationι R X q ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat := by
  -- Both composites `X q ⟶ Y'` send a point `x` to `g x`.
  have h : restrictMap g hg q ≫ (TopPair.ofSubset (X' q)).map =
      (TopPair.ofSubset (X q)).map ≫ g := rfl
  rw [singularChainFiltrationι_def, singularChainFiltrationι_def]
  -- The ambient space of the pair `(Y', X' q)` is `Y'` only up to unfolding `TopPair.ofSubset`,
  -- so the composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _) <|
    (Functor.map_comp _ _ _).symm.trans <| (congrArg _ <|
      (Functor.map_comp _ _ _).symm.trans <| (congrArg _ h).trans
        (Functor.map_comp _ _ _)).trans (Functor.map_comp _ _ _)).trans (extendMap_comp _ _ _)

include hg in
private lemma factors_singularChainFiltration (q : ℤ) :
    (singularChainFiltration R X' q).Factors ((singularChainFiltration R X q).arrow ≫
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat) :=
  (Subobject.mk_factors_iff _ _).2 ⟨(singularChainFiltrationIso R X q).hom ≫ extendMap
      (SSet.chainComplexMap (TopCat.toSSet.map (restrictMap g hg q)) R)
        ComplexShape.embeddingDownNat,
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (singularChainFiltrationι_naturality R g hg q)).trans
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
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceFiltrationMap,
    CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _) (by simp),
    CochainComplex.filtrationFunctorMap_id,
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
    filteredSpaceSpectralSequenceMap_def, filteredSpaceFiltrationMap, filteredSpaceFiltrationMap,
    filteredSpaceFiltrationMap, CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) _ ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g') R) _) (by simp),
    CochainComplex.filtrationFunctorMap_comp _ _ (factors_singularChainFiltration R g hg)
      (factors_singularChainFiltration R g' hg'),
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]

include g hg in
/-- The map of pairs `(X b, X a) ⟶ (X' b, X' a)` induced by a map `g` carrying each `X q` into
`X' q`, for `a ≤ b`. -/
abbrev filteredSpaceStepMap {a b : ℤ} (hab : a ≤ b) :
    TopPair.ofInclusion (hX hab) ⟶ TopPair.ofInclusion (hX' hab) :=
  TopPair.ofInclusionMap _ _ ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩
    fun _ hx ↦ hg a hx

/-- The ambient part of the map of pairs `(X b, X a) ⟶ (X' b, X' a)` is the restriction of
`g`. -/
private lemma fst_filteredSpaceStepMap {a b : ℤ} (hab : a ≤ b) :
    TopPair.Hom.fst (filteredSpaceStepMap hX hX' g hg hab) = restrictMap g hg b :=
  TopCat.hom_ext (ContinuousMap.ext fun x ↦ TopPair.ofInclusionMap_fst_apply _ _ x)

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
          (singularChainFiltrationIso R X b).hom ≫ extendMap
            (SSet.chainComplexMap (TopCat.toSSet.map (restrictMap g hg b)) R)
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
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map (restrictMap g hg b)) R)
        ComplexShape.embeddingDownNat ≫
      extendMap ((TopPair.ofInclusion (hX' hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat :=
    (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _) <|
      (TopPair.singularChainComplexπ_pair_naturality _ R).symm.trans <|
        congrArg (fun φ ↦ SSet.chainComplexMap (TopCat.toSSet.map φ) R ≫ _)
          (fst_filteredSpaceStepMap hX hX' g hg hab)).trans (extendMap_comp _ _ _)
  exact (filteredSpaceFiltrationMap_app_comp_singularChainFiltrationIso_hom_assoc R hX hX' g hg b
    _).trans <| congrArg (_ ≫ ·) <| congrArg (_ ≫ ·) <|
      (congrArg (_ ≫ ·) h.symm).trans (Category.assoc _ _ _).symm

/-- **The morphism of spectral sequences of a map of filtered spaces on the first page.** Let
`g : Y ⟶ Y'` carry each `X q` into `X' q`. Under the identifications of the first pages with
relative singular homology (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`), the morphism of
spectral sequences induced by `g` is, at `(p, q)`, the map
`Hₙ(X (q + 1), X q) ⟶ Hₙ(X' (q + 1), X' q)` induced by `g`, where `p + q = -n`. -/
theorem filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX' pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        TopPair.singularHomologyMap (filteredSpaceStepMap hX hX' g hg (by lia)) R n := by
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, Iso.trans_hom,
    filteredSpaceSpectralSequenceMap_def]
  rw [CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality_assoc]
  refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  -- Compare the graded pieces at the chain level, then pass to homology.
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
