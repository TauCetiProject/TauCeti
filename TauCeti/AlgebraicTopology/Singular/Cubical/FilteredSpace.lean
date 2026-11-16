/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison

/-!
# The spectral sequence of a filtered space on cubical chains

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`. The
normalized cubical chains of the `X q` form an increasing filtration of the normalized cubical
chains of `Y` (`TauCeti.cubicalChainFiltration`), and its spectral sequence
(`TauCeti.cubicalFilteredSpaceSpectralSequence`) is the cubical counterpart of the spectral
sequence `TauCeti.filteredSpaceSpectralSequence` of the filtration of the simplicial singular
chains. As there, chains in degree `n` sit in cohomological degree `-n`, and the abutment in
degree `-n` is the cubical homology `Hₙ(Y)` (`TauCeti.cubicalFilteredSpaceAbutmentIso`).

The natural comparison map `TauCeti.singularToCubical` from simplicial to normalized cubical
chains carries the singular chains of `X q` into the cubical chains of `X q`, so it is a morphism
of filtered complexes (`TauCeti.singularToCubicalFiltrationMap`). On the piece of the filtration
at `q` it is the comparison map of the space `X q`
(`TauCeti.singularToCubicalFiltrationMap_app_comp_cubicalChainFiltrationIso_hom`), a
quasi-isomorphism. By the comparison theorem for quasi-isomorphisms of filtrations
(`CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso`), the induced morphism of spectral
sequences (`TauCeti.singularToCubicalSpectralSequenceMap`) is an isomorphism on every object of
every page, from the first page on
(`TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`). So everything known about the
spectral sequence of a filtered space on simplicial chains, such as its first page or its
convergence, holds on cubical chains through this comparison. Over the skeletal filtration of a
Serre fibration this is the Serre spectral sequence on cubical chains.

## Main definitions

* `TauCeti.cubicalChainFiltration k X`: the filtration of the normalized cubical chains of `Y` by
  those of the `X q`, reindexed as cochain complexes along `n ↦ -n`.
* `TauCeti.cubicalFilteredSpaceSpectralSequence k hX`: its spectral sequence.
* `TauCeti.cubicalFilteredSpaceAbutmentIso k hX n`: the abutment in degree `-n` is `Hₙ(Y)`.
* `TauCeti.singularToCubicalFiltrationMap k hX`: the morphism of filtrations given by the
  comparison of simplicial and cubical chains.
* `TauCeti.singularToCubicalSpectralSequenceMap k hX`: the induced morphism of spectral
  sequences.

## Main results

* `TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`: the comparison is an isomorphism on
  every page `r ≥ 2`.
* `TauCeti.singularCubicalSpectralSequencePageXIso`: the resulting isomorphism of the objects
  of the two spectral sequences.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII (the comparison of
  cubical and simplicial chains).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II (the spectral sequence of a fibration on cubical chains).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace TauCeti

variable (k : Type u) [Ring k] {Y : TopCat.{u}} (X : ℤ → Set Y)

/-- The inclusion of the normalized cubical chains of `X q` into those of `Y`, with both chain
complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def cubicalChainFiltrationι (q : ℤ) :
    ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X q)).snd).extend
        ComplexShape.embeddingDownNat ⟶
      ((normalizedCubicalChainComplex k).obj Y).extend ComplexShape.embeddingDownNat :=
  extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (X q)).map) _

/-- The inclusion of the cubical chains of `X q` into those of `Y` is induced by the inclusion of
the subspace `X q`. -/
lemma cubicalChainFiltrationι_def (q : ℤ) :
    cubicalChainFiltrationι k X q =
      extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (X q)).map)
        ComplexShape.embeddingDownNat :=
  (rfl)

/-- The normalized cubical chains of `X q` form a subcomplex of those of `Y`, also after
reindexing. -/
instance (q : ℤ) : Mono (cubicalChainFiltrationι k X q) := by
  rw [cubicalChainFiltrationι_def]
  exact HomologicalComplex.mono_extendMap _ _

/-- The filtration of the normalized cubical chains of `Y` by the normalized cubical chains of the
subsets `X q`, with the chain complexes reindexed as cochain complexes in nonpositive degrees
along `n ↦ -n`. -/
def cubicalChainFiltration (q : ℤ) :
    Subobject (((normalizedCubicalChainComplex k).obj Y).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (cubicalChainFiltrationι k X q)

/-- The `q`-th stage of the cubical filtration is the reindexed normalized cubical chain complex of
`X q`. -/
def cubicalChainFiltrationIso (q : ℤ) :
    (cubicalChainFiltration k X q : CochainComplex (ModuleCat.{u} k) ℤ) ≅
      ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X q)).snd).extend
        ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (cubicalChainFiltrationι k X q)

/-- The identification of the `q`-th stage of the cubical filtration with the cubical chains of
`X q` is compatible with the inclusions into the cubical chains of `Y`. -/
@[reassoc (attr := simp)]
lemma cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι (q : ℤ) :
    (cubicalChainFiltrationIso k X q).hom ≫ cubicalChainFiltrationι k X q =
      (cubicalChainFiltration k X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the cubical chains of `X a` into those of `Y` factors
through the inclusion of the pair `(X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_cubicalChainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map)
        ComplexShape.embeddingDownNat ≫ cubicalChainFiltrationι k X b =
      cubicalChainFiltrationι k X a :=
  -- The composite of the inclusions `X a ⊆ X b ⊆ Y` is the inclusion of `X a` by definition.
  (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) (Functor.map_comp _ _ _).symm

/-- The cubical filtration is monotone in the subsets. -/
lemma cubicalChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    cubicalChainFiltration k X a ≤ cubicalChainFiltration k X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_cubicalChainFiltrationι k hab)

/-- An increasing family of subsets gives an increasing filtration of cubical chains. -/
lemma monotone_cubicalChainFiltration (hX : Monotone X) :
    Monotone (cubicalChainFiltration k X) :=
  fun _ _ h ↦ cubicalChainFiltration_mono k (hX h)

variable (hX : Monotone X)

/-- **The spectral sequence of a filtered space on cubical chains.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration of the
normalized cubical chains of `Y` by those of the `X q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. -/
abbrev cubicalFilteredSpaceSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX))

/-- **The abutment of the cubical spectral sequence of a filtered space** in degree `-n` is the
cubical homology `Hₙ(Y)`. -/
def cubicalFilteredSpaceAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX))).abutment
        (-n) ≅
      ((normalizedCubicalChainComplex k).obj Y).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-! ### The comparison with simplicial chains -/

variable (Z : TopCat.{u}) in
/-- The comparison map `TauCeti.singularToCubical` from the simplicial to the normalized cubical
chains of a space `Z`, with both chain complexes reindexed as cochain complexes in nonpositive
degrees along `n ↦ -n`, which is the form in which they carry the filtrations of a filtered
space. -/
def singularToCubicalExtend :
    ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of k k)).extend
        ComplexShape.embeddingDownNat ⟶
      ((normalizedCubicalChainComplex k).obj Z).extend ComplexShape.embeddingDownNat :=
  extendMap ((singularToCubical k).app Z) _

variable (Z : TopCat.{u}) in
/-- The reindexed comparison map is the extension of the comparison map of `Z`. -/
lemma singularToCubicalExtend_def :
    singularToCubicalExtend k Z = extendMap ((singularToCubical k).app Z) _ :=
  (rfl)

variable (Z : TopCat.{u}) in
/-- The reindexed comparison map is a quasi-isomorphism. -/
instance quasiIso_singularToCubicalExtend : QuasiIso (singularToCubicalExtend k Z) :=
  inferInstanceAs (QuasiIso (extendMap ((singularToCubical k).app Z) _))

/-- The comparison map to cubical chains carries the singular chains of `X q` into the cubical
chains of `X q`. -/
@[reassoc]
lemma singularChainFiltrationι_comp_singularToCubicalExtend (q : ℤ) :
    singularChainFiltrationι (ModuleCat.of k k) X q ≫ singularToCubicalExtend k Y =
      singularToCubicalExtend k (TopPair.ofSubset (X q)).snd ≫ cubicalChainFiltrationι k X q := by
  rw [singularChainFiltrationι_def, cubicalChainFiltrationι_def, singularToCubicalExtend_def,
    singularToCubicalExtend_def]
  -- The ambient space of the pair `(Y, X q)` is `Y` only up to definitional unfolding, and the
  -- singular chain map of the inclusion is the map of `singularChains k`, so the composites are
  -- formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) ((singularToCubical k).naturality (TopPair.ofSubset (X q)).map)).trans
      (extendMap_comp _ _ _)

private lemma factors_cubicalChainFiltration (q : ℤ) :
    (cubicalChainFiltration k X q).Factors
      ((singularChainFiltration (ModuleCat.of k k) X q).arrow ≫ singularToCubicalExtend k Y) :=
  (Subobject.mk_factors_iff _ _).2 ⟨(singularChainFiltrationIso (ModuleCat.of k k) X q).hom ≫
      singularToCubicalExtend k (TopPair.ofSubset (X q)).snd,
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (singularChainFiltrationι_comp_singularToCubicalExtend k q).symm).trans <|
        singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc _ X q _⟩

/-- **The comparison of the simplicial and cubical filtrations of a filtered space.** The natural
comparison map `TauCeti.singularToCubical` of the chains of `Y` carries the singular chains of
each `X q` into the cubical chains of `X q`, so it is a morphism from the filtration of the
singular chains of `Y` by those of the `X q` to the filtration of the cubical chains of `Y` by
those of the `X q`. -/
def singularToCubicalFiltrationMap :
    CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration (ModuleCat.of k k) hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX) :=
  CochainComplex.filtrationFunctorMap _ _ _ (factors_cubicalChainFiltration k)

/-- The components of `TauCeti.singularToCubicalFiltrationMap` are the restrictions of the
comparison map of the chains of `Y`. -/
@[reassoc (attr := simp)]
lemma singularToCubicalFiltrationMap_app_comp (a : EInt) :
    (singularToCubicalFiltrationMap k hX).app a ≫
        CochainComplex.filtrationFunctorArrow _ (monotone_cubicalChainFiltration k hX) a =
      CochainComplex.filtrationFunctorArrow _
          (monotone_singularChainFiltration (ModuleCat.of k k) hX) a ≫
        singularToCubicalExtend k Y :=
  (CochainComplex.filtrationFunctorMap_app_comp _ _ a).trans (Category.assoc _ _ _).symm

/-- On the stage `F_q`, identified with the chains of `X q`, the comparison of the simplicial and
cubical filtrations is the comparison map of the space `X q`. -/
@[reassoc]
lemma singularToCubicalFiltrationMap_app_comp_cubicalChainFiltrationIso_hom (q : ℤ) :
    (singularToCubicalFiltrationMap k hX).app q ≫
        (CochainComplex.filtrationFunctorObjIso _ (monotone_cubicalChainFiltration k hX) q).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ q).le ≫
            (cubicalChainFiltrationIso k X q).hom =
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_singularChainFiltration (ModuleCat.of k k) hX) q).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ q).le ≫
          (singularChainFiltrationIso (ModuleCat.of k k) X q).hom ≫
            singularToCubicalExtend k (TopPair.ofSubset (X q)).snd := by
  refine (cancel_mono (cubicalChainFiltrationι k X q)).1 ?_
  simp only [Category.assoc, cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι,
    ← singularChainFiltrationι_comp_singularToCubicalExtend,
    singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow_assoc]
  exact singularToCubicalFiltrationMap_app_comp k hX (q : EInt)

/-- On every stage of the filtrations, the comparison of the simplicial and cubical filtrations
is a quasi-isomorphism. -/
instance quasiIso_singularToCubicalFiltrationMap_app (q : ℤ) :
    QuasiIso ((singularToCubicalFiltrationMap k hX).app q) := by
  -- Both stages at `q` are identified with the chains of `X q`, through isomorphisms, and on
  -- these the comparison is the quasi-isomorphism of the space `X q`.
  have : QuasiIso ((singularToCubicalFiltrationMap k hX).app q ≫
      (CochainComplex.filtrationFunctorObjIso _ (monotone_cubicalChainFiltration k hX) q).hom ≫
        (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
          (cubicalChainFiltrationIso k X q).hom) := by
    rw [Subobject.isoOfEq_hom,
      singularToCubicalFiltrationMap_app_comp_cubicalChainFiltrationIso_hom,
      ← Subobject.isoOfEq_hom _ _ (CochainComplex.filtrationEInt_coe _ q)]
    infer_instance
  exact quasiIso_of_comp_right _
    ((CochainComplex.filtrationFunctorObjIso _ (monotone_cubicalChainFiltration k hX) q).hom ≫
      (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
        (cubicalChainFiltrationIso k X q).hom)

/-- **The comparison of the simplicial and cubical spectral sequences of a filtered space**:
the morphism of spectral sequences induced by the comparison of the simplicial and cubical
filtrations (`TauCeti.singularToCubicalFiltrationMap`). -/
def singularToCubicalSpectralSequenceMap :
    filteredSpaceSpectralSequence (ModuleCat.of k k) hX ⟶
      cubicalFilteredSpaceSpectralSequence k hX :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (singularToCubicalFiltrationMap k hX))

/-- `TauCeti.singularToCubicalSpectralSequenceMap` is the morphism of spectral sequences of the
morphism of spectral objects of `TauCeti.singularToCubicalFiltrationMap`. -/
lemma singularToCubicalSpectralSequenceMap_def :
    singularToCubicalSpectralSequenceMap k hX =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (singularToCubicalFiltrationMap k hX)) :=
  (rfl)

/-- **Cubical and simplicial chains give the same spectral sequence of a filtered space.** The
comparison of the simplicial and cubical spectral sequences of a filtered space is an isomorphism
on every object of every page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_singularToCubicalSpectralSequenceMap_hom_f (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq) :=
  CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso _
    (quasiIso_singularToCubicalFiltrationMap_app k hX) r hr pq

/-- The isomorphism between the objects of the simplicial and cubical spectral sequences of a
filtered space, on every page `r ≥ 2`, given by their comparison. -/
def singularCubicalSpectralSequencePageXIso (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (ModuleCat.of k k) hX).page r).X pq ≅
      ((cubicalFilteredSpaceSpectralSequence k hX).page r).X pq :=
  have := isIso_singularToCubicalSpectralSequenceMap_hom_f k hX r hr pq
  asIso (((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq)

/-- The isomorphism `TauCeti.singularCubicalSpectralSequencePageXIso` is the component of the
comparison of the simplicial and cubical spectral sequences. -/
@[simp]
lemma singularCubicalSpectralSequencePageXIso_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (singularCubicalSpectralSequencePageXIso k hX r hr pq).hom =
      ((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq :=
  (rfl)

end TauCeti
