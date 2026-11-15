/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison

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
* **Naturality.** A continuous map `g : Y ⟶ Y'` carrying each `X q` into the stage `X' q` of a
  filtration of `Y'` induces a morphism of spectral sequences
  (`TauCeti.filteredSpaceSpectralSequenceMap`), compatibly with identities and composition. On the
  first page it is the map in relative singular homology induced by the restrictions of `g`
  (`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`), and on the abutment the
  map `Hₙ(g)` in singular homology (`TauCeti.filteredSpaceAbutmentIso_hom_naturality`). For finite
  filtrations this gives the comparison theorem: if `g` induces isomorphisms on the relative
  homology of all the pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)`, it induces isomorphisms in
  singular homology
  (`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap`).

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

variable {Y' Y'' : TopCat.{w}} {X' : ℤ → Set Y'} {X'' : ℤ → Set Y''}

/-- A continuous map `g : Y ⟶ Y'` carrying `X q` into `X' q` sends the singular chains of `X q`
into those of `X' q`: on singular chains, the inclusion of `X q` followed by `g` is the restriction
of `g` followed by the inclusion of `X' q`. -/
@[reassoc]
lemma singularChainFiltrationι_comp_extendMap (g : Y ⟶ Y') {q : ℤ}
    (hg : Set.MapsTo g (X q) (X' q)) :
    singularChainFiltrationι R X q ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat =
      extendMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g hg))) R)
          ComplexShape.embeddingDownNat ≫ singularChainFiltrationι R X' q := by
  have key : SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map g) R =
      SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g hg))) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X' q)).map) R := by
    have hsq : (TopPair.ofSubset (X q)).map ≫ g =
        TopPair.Hom.snd (TopPair.ofSubsetMap g hg) ≫ (TopPair.ofSubset (X' q)).map :=
      ((TopPair.Hom.w _).trans (congrArg _ (TopPair.ofSubsetMap_fst g hg))).symm
    exact (Functor.map_comp _ _ _).symm.trans <| (congrArg _ ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ hsq).trans (Functor.map_comp _ _ _)))).trans (Functor.map_comp _ _ _)
  rw [singularChainFiltrationι_def, singularChainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans ((congrArg (extendMap · _) key).trans
    (extendMap_comp _ _ _))

/-- A continuous map `g : Y ⟶ Y'` carrying each `X q` into `X' q` is a morphism of the filtered
singular chain complexes. -/
lemma singularChainFiltration_factors_arrow_comp_extendMap (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (q : ℤ) :
    (singularChainFiltration R X' q).Factors ((singularChainFiltration R X q).arrow ≫
      extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat) := by
  rw [← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Category.assoc,
    singularChainFiltrationι_comp_extendMap R g (hg q),
    ← (Iso.inv_comp_eq _).2
      (singularChainFiltrationIso_hom_comp_singularChainFiltrationι R X' q).symm]
  simpa only [Category.assoc] using Subobject.factors_comp_arrow (_ ≫ _ ≫ _)

variable (hX' : Monotone X') (hX'' : Monotone X'')

/-- **The morphism of filtered singular chain complexes induced by a map of filtered spaces.** A
continuous map `g : Y ⟶ Y'` carrying each `X q` into `X' q` induces, on singular chains, a
morphism of the functors of the filtrations of singular chains by the `X q` and by the `X' q`. -/
noncomputable abbrev singularChainFiltrationFunctorMap (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) :
    CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration R hX') :=
  CochainComplex.filtrationFunctorMap _ _
    (extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat)
    (singularChainFiltration_factors_arrow_comp_extendMap R g hg)

/-- **Naturality of the spectral sequence of a filtered space.** A continuous map `g : Y ⟶ Y'`
carrying each `X q` into `X' q` induces a morphism from the spectral sequence of the filtration of
`Y` by the `X q` to that of the filtration of `Y'` by the `X' q`. On the first page it is the map
in relative singular homology induced by `g`
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality`), and on the abutment the map
in singular homology induced by `g` (`TauCeti.filteredSpaceAbutmentIso_hom_naturality`). -/
noncomputable abbrev filteredSpaceSpectralSequenceMap (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) :
    filteredSpaceSpectralSequence R hX ⟶ filteredSpaceSpectralSequence R hX' :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (singularChainFiltrationFunctorMap R hX hX' g hg))

/-- The identity of a filtered space induces the identity of its spectral sequence. -/
@[simp]
lemma filteredSpaceSpectralSequenceMap_id (hg : ∀ q, Set.MapsTo (𝟙 Y) (X q) (X q)) :
    filteredSpaceSpectralSequenceMap R hX hX (𝟙 Y) hg = 𝟙 _ := by
  rw [filteredSpaceSpectralSequenceMap, singularChainFiltrationFunctorMap,
    CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _) (by simp),
    CochainComplex.filtrationFunctorMap_id,
    CochainComplex.spectralObjectMap_id, Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of spectral
sequences. Not `@[simp]`: the intermediate filtration cannot be inferred from the left-hand
side. -/
lemma filteredSpaceSpectralSequenceMap_comp (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q))
    (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceSpectralSequenceMap R hX hX'' (g ≫ g') hgg' =
      filteredSpaceSpectralSequenceMap R hX hX' g hg ≫
        filteredSpaceSpectralSequenceMap R hX' hX'' g' hg' := by
  rw [filteredSpaceSpectralSequenceMap, filteredSpaceSpectralSequenceMap,
    filteredSpaceSpectralSequenceMap, singularChainFiltrationFunctorMap,
    singularChainFiltrationFunctorMap, singularChainFiltrationFunctorMap,
    CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) _ ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g') R) _) (by simp [extendMap_comp]),
    CochainComplex.filtrationFunctorMap_comp, CochainComplex.spectralObjectMap_comp,
    Abelian.SpectralObject.spectralSequenceMap_comp]

/-- On the stage `b` of the filtrations, identified with the singular chains of `X b` and `X' b`,
the morphism of filtrations induced by `g` is induced by the restriction of `g`. -/
@[reassoc]
private lemma singularChainFiltrationFunctorMap_app_comp_singularChainFiltrationIso_hom
    (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (b : ℤ) :
    (singularChainFiltrationFunctorMap R hX hX' g hg).app b ≫
        (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
            (singularChainFiltrationIso R X' b).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso R X b).hom ≫
            extendMap (SSet.chainComplexMap
              (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) R)
              ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (singularChainFiltrationι R X' b)]
  simp only [Category.assoc, singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
    Subobject.ofLE_arrow, ← singularChainFiltrationι_comp_extendMap,
    singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc,
    Subobject.ofLE_arrow_assoc]
  exact CochainComplex.filtrationFunctorMap_app_comp _ _ _

/-- On the quotient `F_b / F_a`, identified with the relative singular chains of `(X b, X a)`, the
morphism of filtrations induced by `g` is the chain map induced by the map of pairs
`(X b, X a) ⟶ (X' b, X' a)` restricting `g`. -/
private lemma cokernel_map_comp_cokernelFiltrationFunctorMapIso_hom (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ ((singularChainFiltrationFunctorMap R hX hX' g hg).app a)
        ((singularChainFiltrationFunctorMap R hX hX' g hg).app b) (NatTrans.naturality _ f) ≫
        (cokernelFiltrationFunctorMapIso R hX' f).hom =
      (cokernelFiltrationFunctorMapIso R hX f).hom ≫
        extendMap (TopPair.singularChainComplexMap (TopPair.ofInclusionMap _ _
          ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩ fun _ hx ↦ hg a hx) R)
          ComplexShape.embeddingDownNat := by
  have hab : a ≤ b := WithBotTop.coe_le_coe.mp (leOfHom f)
  let gab := TopPair.ofInclusionMap (hX hab) (hX' hab)
    ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩ fun _ hx ↦ hg a hx
  have hfst : TopPair.Hom.fst gab = TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)) := by
    ext x
    exact Subtype.ext ((congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
      (TopPair.ofSubsetMap_snd_apply g (hg b) x).symm)
  have hπ : extendMap ((TopPair.ofInclusion (hX hab)).singularChainComplexπ R)
        ComplexShape.embeddingDownNat ≫
        extendMap (TopPair.singularChainComplexMap gab R) ComplexShape.embeddingDownNat =
      extendMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg b)))) R)
        ComplexShape.embeddingDownNat ≫
        extendMap ((TopPair.ofInclusion (hX' hab)).singularChainComplexπ R)
          ComplexShape.embeddingDownNat :=
    (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · ComplexShape.embeddingDownNat)
      ((TopPair.singularChainComplexπ_pair_naturality gab R).symm.trans
        (congrArg (fun φ ↦ SSet.chainComplexMap (TopCat.toSSet.map φ) R ≫
          (TopPair.ofInclusion (hX' hab)).singularChainComplexπ R) hfst))).trans
      (extendMap_comp _ _ _)
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [cokernel.π_desc_assoc, Category.assoc, π_cokernelFiltrationFunctorMapIso_hom,
    π_cokernelFiltrationFunctorMapIso_hom_assoc]
  refine (singularChainFiltrationFunctorMap_app_comp_singularChainFiltrationIso_hom_assoc R hX hX'
    g hg b _).trans ?_
  -- The ambient space of `(X b, X a)` is the subspace `X b` of `Y` only up to unfolding, so the
  -- composite is rewritten with `erw`; the remaining goal unfolds the local definition `gab`.
  erw [← hπ, Category.assoc]
  rfl

/-- **The morphism of spectral sequences of filtered spaces on the first page.** Under the
identifications `TauCeti.filteredSpaceSpectralSequenceFirstPageXIso` of the objects at `(p, q)` on
the first pages with the relative singular homology `Hₙ(X (q + 1), X q)` and
`Hₙ(X' (q + 1), X' q)`, where `p + q = -n`, the morphism induced by `g` is the map in relative
singular homology induced by the map of pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` restricting
`g`. -/
@[reassoc]
theorem filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX' pq a b ha hb m hm n hn).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).hom ≫
        TopPair.singularHomologyMap (TopPair.ofInclusionMap (hX (by lia : a ≤ b))
          (hX' (by lia : a ≤ b)) ⟨(hg b).restrict, g.hom.continuous.restrict (hg b)⟩
          fun _ hx ↦ hg a hx) R n := by
  rw [Abelian.SpectralObject.spectralSequenceMap_hom,
    Abelian.SpectralObject.spectralSequencePageMap_f]
  simp only [filteredSpaceSpectralSequenceFirstPageXIso, Iso.trans_hom, Category.assoc]
  rw [CochainComplex.spectralSequencePageXMap_comp_spectralSequenceFirstPageXIsoCokernel_hom_assoc]
  congr 1
  -- The pairs `(X b, X a)` are built from `hX`, which `rw` does not unfold at reducible
  -- transparency, so the remaining square is assembled as a term: the morphism of graded pieces
  -- is the relative chain map of the restriction of `g`, compatibly with reindexing.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
    ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans <| (congrArg
      (HomologicalComplex.homologyMap · m)
      (cokernel_map_comp_cokernelFiltrationFunctorMapIso_hom R hX hX' g hg _)).trans
      (HomologicalComplex.homologyMap_comp _ _ _))).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)).trans
      (Category.assoc _ _ _).symm

/-- **The morphism of spectral objects of filtered spaces on the abutment.** Under the
identifications `TauCeti.filteredSpaceAbutmentIso` of the abutments in degree `-n` with the singular
homology `Hₙ(Y)` and `Hₙ(Y')`, the morphism of spectral objects induced by `g`, from which
`TauCeti.filteredSpaceSpectralSequenceMap` is built, is the map `Hₙ(g)` in singular homology. -/
@[reassoc]
theorem filteredSpaceAbutmentIso_hom_naturality (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) (n : ℕ) :
    ((CochainComplex.spectralObjectMap (singularChainFiltrationFunctorMap R hX hX' g hg)).hom
        (-n)).app (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (filteredSpaceAbutmentIso R hX' n).hom =
      (filteredSpaceAbutmentIso R hX n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g := by
  rw [filteredSpaceAbutmentIso, filteredSpaceAbutmentIso, singularHomologyFunctor_obj_map]
  -- The homology objects of the extended complexes carry `HasHomology` instances that `rw` does
  -- not identify, so the square is assembled as a term.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
    (CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom
      _ _ _)).trans <| (Category.assoc _ _ _).trans <| (congrArg
      ((CochainComplex.filtrationAbutmentIso _ (monotone_singularChainFiltration R hX) _).hom ≫ ·)
      (HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

/-- Outside `[a, b)`, the relative singular homology `Hₙ(X (q + 1), X q)` of a filtration with
`X a = ∅` and `X b = Y` vanishes: both subspaces are empty, or both are everything. -/
private lemma isZero_singularHomology_ofInclusion_of_notMem_Ico {a b q : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (hq : q ∉ Set.Ico a b) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl : q ≤ q + 1))).singularHomology R n) :=
  TopPair.isZero_singularHomology_of_surjective_map _ R (fun y ↦ by
    rcases not_and_or.1 hq with hq | hq
    · exact absurd (hX (by lia : q + 1 ≤ a) y.2) (by simp [ha])
    · exact ⟨⟨y.1, hX (not_lt.1 hq) (hb ▸ Set.mem_univ y.1)⟩, rfl⟩) n

/-- **The comparison theorem for filtered spaces.** Let `g : Y ⟶ Y'` carry each `X q` into
`X' q`, for finite filtrations: `X a` and `X' a` are empty, and `X b` and `X' b` are everything. If
for every `a ≤ q < b` the map of pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` restricting `g`
induces isomorphisms in relative singular homology, then `g` induces isomorphisms
`Hₙ(Y) ⟶ Hₙ(Y')` in singular homology. The proof compares the spectral sequences of the two
filtrations: `g` induces an isomorphism on their first pages, hence on their abutments. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap (g : Y ⟶ Y')
    (hg : ∀ q, Set.MapsTo g (X q) (X' q)) {a b : ℤ} (ha : X a = ∅) (ha' : X' a = ∅)
    (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ,
      IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap
        (hX (Int.le_add_one le_rfl : q ≤ q + 1)) (hX' (Int.le_add_one le_rfl : q ≤ q + 1))
        ⟨(hg (q + 1)).restrict, g.hom.continuous.restrict (hg (q + 1))⟩
        fun _ hx ↦ hg q hx) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  -- The morphism of spectral sequences is an isomorphism on the first page.
  have hpage (pq : ℤ × ℤ) :
      IsIso (((filteredSpaceSpectralSequenceMap R hX hX' g hg).hom 2 le_rfl).f pq) := by
    rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
    · exact ⟨0, (isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos).eq_of_src _ _,
        (isZero_filteredSpaceSpectralSequence_page_two_X R hX' pq hpos).eq_of_src _ _⟩
    obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hle
    have hk : IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap
        (hX (Int.le_add_one le_rfl : pq.2 ≤ pq.2 + 1))
        (hX' (Int.le_add_one le_rfl : pq.2 ≤ pq.2 + 1))
        ⟨(hg (pq.2 + 1)).restrict, g.hom.continuous.restrict (hg (pq.2 + 1))⟩
        fun _ hx ↦ hg pq.2 hx) R m) := by
      by_cases hq : pq.2 ∈ Set.Ico a b
      · exact h pq.2 hq.1 hq.2 m
      · exact ⟨0, (isZero_singularHomology_ofInclusion_of_notMem_Ico R hX ha hb hq m).eq_of_src _ _,
          (isZero_singularHomology_ofInclusion_of_notMem_Ico R hX' ha' hb' hq m).eq_of_src _ _⟩
    rw [(Iso.eq_comp_inv _).2 (filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality R hX hX'
      g hg pq pq.2 (pq.2 + 1) rfl rfl _ rfl m hm)]
    infer_instance
  -- Both filtrations are finite, so it is an isomorphism on the abutments.
  have habut :=
    CochainComplex.isIso_spectralObjectMap_hom_app_abutment_of_isIso_spectralSequence_page _ _ _ _
      (singularChainFiltrationFunctorMap R hX hX' g hg) (singularChainFiltration_eq_bot R ha)
      (singularChainFiltration_eq_bot R ha') (singularChainFiltration_eq_top R hb)
      (singularChainFiltration_eq_top R hb') 2 le_rfl hpage (-n)
  rw [← (Iso.inv_comp_eq _).2 (filteredSpaceAbutmentIso_hom_naturality R hX hX' g hg n)]
  infer_instance

end Naturality

end TauCeti
