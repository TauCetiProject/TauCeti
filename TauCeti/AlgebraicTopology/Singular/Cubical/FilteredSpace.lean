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
chains of `Y` (`TauCeti.chainFiltration` for `TauCeti.normalizedCubicalChainComplex`), and its
spectral sequence (`TauCeti.cubicalFilteredSpaceSpectralSequence`) is the cubical counterpart of
the spectral sequence `TauCeti.filteredSpaceSpectralSequence` of the filtration of the simplicial
singular chains. As there, chains in degree `n` sit in cohomological degree `-n`, and the abutment
in degree `-n` is the cubical homology `Hₙ(Y)` (`TauCeti.chainFiltrationAbutmentIso`). The stage
at an empty subset is zero (`TauCeti.cubicalChainFiltration_eq_bot`), and the stage at the whole
space is everything (`TauCeti.chainFiltration_eq_top`).

The natural comparison map `TauCeti.singularToCubical` from simplicial to normalized cubical
chains carries the singular chains of `X q` into the cubical chains of `X q`, so it is a morphism
of filtered complexes (`TauCeti.singularToCubicalFiltrationMap`). On the piece of the filtration
at `q` it is the comparison map of the space `X q`
(`TauCeti.singularToCubicalFiltrationMap_app_comp_chainFiltrationIso_hom`), a
quasi-isomorphism. By the comparison theorem for quasi-isomorphisms of filtrations
(`CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso`), the induced morphism of spectral
sequences (`TauCeti.singularToCubicalSpectralSequenceMap`) is an isomorphism on every object of
every page, from the first page on
(`TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`). So statements about the pages of
the spectral sequence of a filtered space on simplicial chains, such as the description of its
first page or its vanishing regions, transfer to cubical chains through these isomorphisms. The
abutment is identified with the cubical homology `Hₙ(Y)` separately, and its filtration is not
compared with the simplicial one here. Over the skeletal filtration of a Serre fibration this is
the Serre spectral sequence on cubical chains.

## Main definitions

* `TauCeti.cubicalFilteredSpaceSpectralSequence k hX`: the spectral sequence of the filtration of
  the normalized cubical chains of `Y` by those of the `X q`.
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

/-- The normalized cubical chains of an empty space vanish, as there are no singular cubes in
it. -/
lemma isZero_normalizedCubicalChainComplex_obj_of_isEmpty (Z : TopCat.{u}) [IsEmpty Z] :
    IsZero ((normalizedCubicalChainComplex k).obj Z) := by
  rw [IsZero.iff_id_eq_zero]
  ext n x
  have : IsEmpty (SingularCube Z n) := ⟨fun c ↦ isEmptyElim (c fun _ ↦ 0)⟩
  have : Subsingleton (NormalizedCubicalChain Z k n) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  exact this.elim _ _

variable {X}

/-- The stage of the filtration of normalized cubical chains at an empty subset is zero. -/
@[simp]
lemma cubicalChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    chainFiltration (normalizedCubicalChainComplex k) X a = ⊥ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  exact chainFiltration_eq_bot_of_isZero _ (isZero_normalizedCubicalChainComplex_obj_of_isEmpty k _)

variable (hX : Monotone X)

/-- **The spectral sequence of a filtered space on cubical chains.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration of the
normalized cubical chains of `Y` by those of the `X q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. Its abutment in degree
`-n` is the cubical homology `Hₙ(Y)` (`TauCeti.chainFiltrationAbutmentIso`). -/
abbrev cubicalFilteredSpaceSpectralSequence :=
  CochainComplex.spectralSequence (CochainComplex.filtrationFunctor _
    (monotone_chainFiltration (normalizedCubicalChainComplex k) hX))

/-! ### The comparison with simplicial chains -/

variable (Z : TopCat.{u}) in
/-- The comparison map `TauCeti.singularToCubical` from the simplicial to the normalized cubical
chains of a space `Z`, with both chain complexes reindexed as cochain complexes in nonpositive
degrees along `n ↦ -n`, which is the form in which they carry the filtrations of a filtered
space. -/
def singularToCubicalExtend :
    ((singularChains k).obj Z).extend ComplexShape.embeddingDownNat ⟶
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
lemma chainFiltrationι_comp_singularToCubicalExtend (q : ℤ) :
    chainFiltrationι (singularChains k) X q ≫ singularToCubicalExtend k Y =
      singularToCubicalExtend k (TopPair.ofSubset (X q)).snd ≫
        chainFiltrationι (normalizedCubicalChainComplex k) X q := by
  rw [chainFiltrationι_def, chainFiltrationι_def, singularToCubicalExtend_def,
    singularToCubicalExtend_def]
  -- The ambient space of the pair `(Y, X q)` is `Y` only up to definitional unfolding, and the
  -- singular chain map of the inclusion is the map of `singularChains k`, so the composites are
  -- formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) ((singularToCubical k).naturality (TopPair.ofSubset (X q)).map)).trans
      (extendMap_comp _ _ _)

private lemma factors_cubicalChainFiltration (q : ℤ) :
    (chainFiltration (normalizedCubicalChainComplex k) X q).Factors
      ((chainFiltration (singularChains k) X q).arrow ≫ singularToCubicalExtend k Y) := by
  have h : chainFiltrationι (normalizedCubicalChainComplex k) X q =
      (chainFiltrationIso _ X q).inv ≫ (chainFiltration _ X q).arrow :=
    ((Iso.inv_comp_eq _).2 (chainFiltrationIso_hom_comp_chainFiltrationι _ X q).symm).symm
  rw [← chainFiltrationIso_hom_comp_chainFiltrationι, Category.assoc,
    chainFiltrationι_comp_singularToCubicalExtend, h]
  exact Subobject.factors_of_factors_right _ <|
    Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)

/-- **The comparison of the simplicial and cubical filtrations of a filtered space.** The natural
comparison map `TauCeti.singularToCubical` of the chains of `Y` carries the singular chains of
each `X q` into the cubical chains of `X q`, so it is a morphism from the filtration of the
singular chains of `Y` by those of the `X q` to the filtration of the cubical chains of `Y` by
those of the `X q`. -/
def singularToCubicalFiltrationMap :
    CochainComplex.filtrationFunctor _
        (monotone_chainFiltration (singularChains k) hX) ⟶
      CochainComplex.filtrationFunctor _
        (monotone_chainFiltration (normalizedCubicalChainComplex k) hX) :=
  CochainComplex.filtrationFunctorMap _ _ _ (factors_cubicalChainFiltration k)

/-- The components of `TauCeti.singularToCubicalFiltrationMap` are the restrictions of the
comparison map of the chains of `Y`. -/
@[reassoc (attr := simp)]
lemma singularToCubicalFiltrationMap_app_comp (a : EInt) :
    (singularToCubicalFiltrationMap k hX).app a ≫
        CochainComplex.filtrationFunctorArrow _
          (monotone_chainFiltration (normalizedCubicalChainComplex k) hX) a =
      CochainComplex.filtrationFunctorArrow _
          (monotone_chainFiltration (singularChains k) hX) a ≫
        singularToCubicalExtend k Y :=
  (CochainComplex.filtrationFunctorMap_app_comp _ _ a).trans (Category.assoc _ _ _).symm

/-- On the stage `F_q`, identified with the chains of `X q`, the comparison of the simplicial and
cubical filtrations is the comparison map of the space `X q`. -/
@[reassoc]
lemma singularToCubicalFiltrationMap_app_comp_chainFiltrationIso_hom (q : ℤ) :
    (singularToCubicalFiltrationMap k hX).app q ≫
        (CochainComplex.filtrationFunctorObjIso _
            (monotone_chainFiltration (normalizedCubicalChainComplex k) hX) q).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ q).le ≫
            (chainFiltrationIso (normalizedCubicalChainComplex k) X q).hom =
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_chainFiltration (singularChains k) hX) q).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ q).le ≫
          (chainFiltrationIso (singularChains k) X q).hom ≫
            singularToCubicalExtend k (TopPair.ofSubset (X q)).snd := by
  refine (cancel_mono (chainFiltrationι (normalizedCubicalChainComplex k) X q)).1 ?_
  simp only [Category.assoc, chainFiltrationIso_hom_comp_chainFiltrationι,
    ← chainFiltrationι_comp_singularToCubicalExtend,
    chainFiltrationIso_hom_comp_chainFiltrationι_assoc, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow_assoc]
  exact singularToCubicalFiltrationMap_app_comp k hX (q : EInt)

/-- On every stage of the filtrations, the comparison of the simplicial and cubical filtrations
is a quasi-isomorphism. -/
instance quasiIso_singularToCubicalFiltrationMap_app (q : ℤ) :
    QuasiIso ((singularToCubicalFiltrationMap k hX).app q) := by
  -- Both stages at `q` are identified with the chains of `X q`, through isomorphisms, and on
  -- these the comparison is the quasi-isomorphism of the space `X q`.
  have : QuasiIso ((singularToCubicalFiltrationMap k hX).app q ≫
      (CochainComplex.filtrationFunctorObjIso _
          (monotone_chainFiltration (normalizedCubicalChainComplex k) hX) q).hom ≫
        (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
          (chainFiltrationIso (normalizedCubicalChainComplex k) X q).hom) := by
    rw [Subobject.isoOfEq_hom,
      singularToCubicalFiltrationMap_app_comp_chainFiltrationIso_hom,
      ← Subobject.isoOfEq_hom _ _ (CochainComplex.filtrationEInt_coe _ q)]
    infer_instance
  exact quasiIso_of_comp_right _
    ((CochainComplex.filtrationFunctorObjIso _
        (monotone_chainFiltration (normalizedCubicalChainComplex k) hX) q).hom ≫
      (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
        (chainFiltrationIso (normalizedCubicalChainComplex k) X q).hom)

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
