/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The spectral sequence of a filtered space in cubical singular chains

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`. The normalized
cubical singular chains of the `X q` form an increasing filtration of the normalized cubical
chains of `Y` (`TauCeti.cubicalChainFiltration`), just as their simplicial singular chains filter
the simplicial singular chains of `Y` (`TauCeti.singularChainFiltration`).

The comparison map `TauCeti.singularToCubical` from simplicial to cubical singular chains is
natural, so it sends the simplicial chains of `X q` into the cubical chains of `X q`: it is a
morphism of filtered complexes (`TauCeti.singularToCubicalFiltrationMap`). On every stage of the
filtration it is the comparison map of the subspace `X q`, a chain homotopy equivalence, so it
induces an isomorphism of the spectral objects of the two filtrations
(`TauCeti.singularToCubicalFiltrationSpectralObjectIso`), hence of everything built from them:
the spectral sequence of a filtered space (`TauCeti.filteredSpaceSpectralSequence`), its pages,
its abutment and the filtration of the abutment.

## Main definitions

* `TauCeti.cubicalChainFiltration`: the filtration of the normalized cubical chains of `Y` by the
  normalized cubical chains of the `X q`, reindexed as cochain complexes along `n ↦ -n`.
* `TauCeti.singularToCubicalFiltrationMap`: the comparison of simplicial and cubical singular
  chains, as a morphism of the functors of the two filtrations.
* `TauCeti.singularToCubicalFiltrationSpectralObjectIso`: the induced isomorphism of spectral
  objects.

## References

* W. S. Massey, *Singular Homology Theory*, Graduate Texts in Mathematics 70, Springer, 1980,
  Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 3.5 (the comparison theorem).
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

/-- The normalized cubical chains of `X q` form a subcomplex of those of `Y`, also after
reindexing. -/
instance (q : ℤ) : Mono (cubicalChainFiltrationι k X q) := by
  rw [cubicalChainFiltrationι]
  exact HomologicalComplex.mono_extendMap_of_mono_f _ _

/-- The filtration of the normalized cubical chains of `Y` by the normalized cubical chains of the
subsets `X q`, with the chain complexes reindexed as cochain complexes in nonpositive degrees
along `n ↦ -n`. -/
def cubicalChainFiltration (q : ℤ) :
    Subobject (((normalizedCubicalChainComplex k).obj Y).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (cubicalChainFiltrationι k X q)

/-- The `q`-th stage of the filtration is the reindexed normalized cubical chain complex of
`X q`. -/
def cubicalChainFiltrationIso (q : ℤ) :
    (cubicalChainFiltration k X q : CochainComplex (ModuleCat.{u} k) ℤ) ≅
      ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X q)).snd).extend
        ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (cubicalChainFiltrationι k X q)

/-- The identification of the `q`-th stage of the filtration with the normalized cubical chains
of `X q` is compatible with the inclusions into the normalized cubical chains of `Y`. -/
@[reassoc (attr := simp)]
lemma cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι (q : ℤ) :
    (cubicalChainFiltrationIso k X q).hom ≫ cubicalChainFiltrationι k X q =
      (cubicalChainFiltration k X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the normalized cubical chains of `X a` into those of `Y`
factors through the inclusion of the pair `(X b, X a)`. -/
@[reassoc]
lemma extendMap_comp_cubicalChainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map)
        ComplexShape.embeddingDownNat ≫ cubicalChainFiltrationι k X b =
      cubicalChainFiltrationι k X a :=
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with `exact` rather than `rw`.
  (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) (Functor.map_comp _ _ _).symm

/-- The filtration of normalized cubical chains is monotone in the subsets. -/
lemma cubicalChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    cubicalChainFiltration k X a ≤ cubicalChainFiltration k X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_cubicalChainFiltrationι k hab)

/-- An increasing family of subsets gives an increasing filtration of normalized cubical
chains. -/
lemma monotone_cubicalChainFiltration (hX : Monotone X) :
    Monotone (cubicalChainFiltration k X) :=
  fun _ _ h ↦ cubicalChainFiltration_mono k (hX h)

/-- The comparison of simplicial and cubical singular chains carries the simplicial chains of
`X q` into the cubical chains of `X q`, by naturality. -/
@[reassoc]
lemma singularChainFiltrationι_comp_extendMap_singularToCubical (q : ℤ) :
    singularChainFiltrationι (ModuleCat.of k k) X q ≫
        extendMap ((singularToCubical k).app Y) ComplexShape.embeddingDownNat =
      extendMap ((singularToCubical k).app (TopPair.ofSubset (X q)).snd)
          ComplexShape.embeddingDownNat ≫ cubicalChainFiltrationι k X q := by
  rw [singularChainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _)
    ((singularToCubical k).naturality (TopPair.ofSubset (X q)).map)).trans (extendMap_comp _ _ _)

/-- Each stage of the simplicial filtration is carried into the same stage of the cubical one by
the comparison of simplicial and cubical singular chains. -/
lemma factors_singularChainFiltration_arrow_comp_extendMap_singularToCubical (q : ℤ) :
    (cubicalChainFiltration k X q).Factors ((singularChainFiltration (ModuleCat.of k k) X q).arrow ≫
      extendMap ((singularToCubical k).app Y) ComplexShape.embeddingDownNat) :=
  (Subobject.mk_factors_iff _ _).2 ⟨(singularChainFiltrationIso _ X q).hom ≫
      extendMap ((singularToCubical k).app (TopPair.ofSubset (X q)).snd)
        ComplexShape.embeddingDownNat,
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (singularChainFiltrationι_comp_extendMap_singularToCubical k q).symm).trans <|
        singularChainFiltrationIso_hom_comp_singularChainFiltrationι_assoc _ _ _ _⟩

variable (hX : Monotone X)

/-- **The comparison of simplicial and cubical singular chains is a morphism of filtered
complexes**: the morphism of the functors of the filtrations of the simplicial and cubical chains
of `Y` by those of the `X q` induced by `TauCeti.singularToCubical`. -/
def singularToCubicalFiltrationMap :
    CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration (ModuleCat.of k k) hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX) :=
  CochainComplex.filtrationFunctorMap _ _
    (extendMap ((singularToCubical k).app Y) ComplexShape.embeddingDownNat)
    (factors_singularChainFiltration_arrow_comp_extendMap_singularToCubical k)

omit hX in
/-- A morphism isomorphic, as an arrow, to a quasi-isomorphism is a quasi-isomorphism. -/
private lemma quasiIso_of_comm {K L K' L' : CochainComplex (ModuleCat.{u} k) ℤ} (g : K ⟶ L)
    (g' : K' ⟶ L') [QuasiIso g'] (eK : K ≅ K') (eL : L ≅ L')
    (h : g ≫ eL.hom = eK.hom ≫ g') : QuasiIso g :=
  (quasiIso_iff_of_arrow_mk_iso g g' (Arrow.isoMk eK eL h.symm)).2 inferInstance

/-- Every component of the comparison of filtered complexes is a quasi-isomorphism: at `⊥` both
sides are zero, at `q` it is the comparison map of `X q`, and at `⊤` that of `Y`. -/
instance quasiIso_singularToCubicalFiltrationMap_app (a : EInt) :
    QuasiIso ((singularToCubicalFiltrationMap k hX).app a) := by
  have hcomp := CochainComplex.filtrationFunctorMap_app_comp
    (hF := monotone_singularChainFiltration (ModuleCat.of k k) hX)
    (hG := monotone_cubicalChainFiltration k hX)
    (extendMap ((singularToCubical k).app Y) ComplexShape.embeddingDownNat)
    (factors_singularChainFiltration_arrow_comp_extendMap_singularToCubical k)
  induction a using WithBotTop.rec with
  | bot =>
    have : IsIso ((singularToCubicalFiltrationMap k hX).app ⊥) :=
      isIso_of_source_target_iso_zero _
        (CochainComplex.filtrationFunctorObjIso _ _ ⊥ ≪≫
          Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_bot _) ≪≫ Subobject.botCoeIsoZero)
        (CochainComplex.filtrationFunctorObjIso _ _ ⊥ ≪≫
          Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_bot _) ≪≫ Subobject.botCoeIsoZero)
    infer_instance
  | coe q =>
    have : QuasiIso (extendMap ((singularToCubical k).app (TopPair.ofSubset (X q)).snd)
        ComplexShape.embeddingDownNat) :=
      (quasiIso_extendMap_iff _ _).2 inferInstance
    refine quasiIso_of_comm k _ (extendMap ((singularToCubical k).app (TopPair.ofSubset (X q)).snd)
        ComplexShape.embeddingDownNat)
      (CochainComplex.filtrationFunctorObjIso _ _ q ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q) ≪≫
          singularChainFiltrationIso _ X q)
      (CochainComplex.filtrationFunctorObjIso _ _ q ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q) ≪≫
          cubicalChainFiltrationIso k X q) ?_
    rw [← cancel_mono (cubicalChainFiltrationι k X q)]
    simp only [Iso.trans_hom, Subobject.isoOfEq, Category.assoc,
      cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι, Subobject.ofLE_arrow,
      ← singularChainFiltrationι_comp_extendMap_singularToCubical]
    -- The stages are the simplicial chain complexes of the `X q` only up to definitional
    -- unfolding, so the identification is assembled as a term rather than rewritten.
    exact (hcomp q).trans (congrArg (_ ≫ ·) ((congrArg (· ≫ _) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (singularChainFiltrationIso_hom_comp_singularChainFiltrationι _ X q)).trans
        (Subobject.ofLE_arrow _))).symm).trans (Category.assoc _ _ _)))
  | top =>
    have hf : QuasiIso (extendMap ((singularToCubical k).app Y) ComplexShape.embeddingDownNat) :=
      (quasiIso_extendMap_iff _ _).2 inferInstance
    have : IsIso (CochainComplex.filtrationEInt
        (singularChainFiltration (ModuleCat.of k k) X) ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (CochainComplex.filtrationEInt_top _)
    have : IsIso (CochainComplex.filtrationEInt (cubicalChainFiltration k X) ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (CochainComplex.filtrationEInt_top _)
    rw [← quasiIso_iff_comp_right _ ((CochainComplex.filtrationFunctorObjIso _ _ ⊤).hom ≫
      (CochainComplex.filtrationEInt (cubicalChainFiltration k X) ⊤).arrow)]
    have h₁ := quasiIso_of_isIso (CochainComplex.filtrationFunctorObjIso
      (singularChainFiltration (ModuleCat.of k k) X)
      (monotone_singularChainFiltration (ModuleCat.of k k) hX) ⊤).hom
    have h₂ := quasiIso_of_isIso (CochainComplex.filtrationEInt
      (singularChainFiltration (ModuleCat.of k k) X) ⊤).arrow
    exact (hcomp ⊤).symm ▸ quasiIso_comp _ _ (hφ := h₁) (hφ' := quasiIso_comp _ _ (hφ := h₂)
      (hφ' := hf))

/-- **The spectral objects of a filtered space in simplicial and in cubical singular chains are
isomorphic**, through the comparison of simplicial and cubical singular chains. -/
def singularToCubicalFiltrationSpectralObjectIso :
    CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _
          (monotone_singularChainFiltration (ModuleCat.of k k) hX)) ≅
      CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX)) :=
  have := CochainComplex.isIso_spectralObjectMap (singularToCubicalFiltrationMap k hX)
  asIso (CochainComplex.spectralObjectMap (singularToCubicalFiltrationMap k hX))

end TauCeti
