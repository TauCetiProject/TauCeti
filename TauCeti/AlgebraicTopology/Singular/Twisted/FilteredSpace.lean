/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
import TauCeti.Topology.Category.TopCat.Subspace

/-!
# The filtration of twisted chains by subspaces

Let `L` be a local coefficient system on a space `Y` and `X : ℤ → Set Y` an increasing family of
subsets. The singular chains of the `X q` with coefficients in the restrictions of `L` form an
increasing filtration of the singular chains of `Y` with coefficients in `L`
(`TauCeti.LocalCoefficientSystem.twistedChainFiltration`), with chains in degree `n` placed in
cohomological degree `-n`, as for the untwisted filtration `TauCeti.chainFiltration`. Its spectral
sequence is the spectral sequence of a filtered space with local coefficients; for the preimages of
the skeleta of the base of a fibration and a local system on the total space, it is the Serre
spectral sequence with local coefficients. Its abutment in degree `-n` is the twisted homology
`Hₙ(Y; L)` (`TauCeti.LocalCoefficientSystem.twistedChainFiltrationAbutmentIso`).

The cubical counterpart, and the comparison identifying the two spectral sequences, are in
`TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.FilteredSpace`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedChainFiltration L X`: the filtration of the twisted chains
  of `Y` by those of the `X q`.
* `TauCeti.LocalCoefficientSystem.twistedChainFiltrationAbutmentIso`: its abutment is the twisted
  homology of `Y`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, and Chapter 5, the Serre spectral sequence with local coefficients.
* A. Hatcher, *Algebraic Topology*, Section 3.H, singular chains with local coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {Y : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R Y)
  (X : ℤ → Set Y)

/-- The inclusion of the twisted chains of `X q`, with coefficients in the restriction of `L`, into
the twisted chains of `Y`, with both chain complexes reindexed as cochain complexes in nonpositive
degrees along `n ↦ -n`. -/
def twistedChainFiltrationι (q : ℤ) :
    (twistedChainComplex ((pullback (X := TopCat.of ↥(X q)) (ContinuousMap.subtypeVal (X q))).obj
        L)).extend ComplexShape.embeddingDownNat ⟶
      (twistedChainComplex L).extend ComplexShape.embeddingDownNat :=
  extendMap (twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (X q))) L) _

/-- The inclusion of the twisted chains of `X q` is induced by the inclusion of the subspace
`X q`. -/
lemma twistedChainFiltrationι_def (q : ℤ) :
    twistedChainFiltrationι L X q =
      extendMap (twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (X q))) L)
        ComplexShape.embeddingDownNat :=
  (rfl)

/-- The twisted chains of `X q` form a subcomplex of those of `Y`, also after reindexing. -/
instance (q : ℤ) : Mono (twistedChainFiltrationι L X q) := by
  rw [twistedChainFiltrationι]
  exact mono_extendMap _ _

/-- **The filtration of twisted chains by subspaces.** The twisted chains of `Y` are filtered by
the twisted chains of the subsets `X q`, with the coefficients restricted, and with the chain
complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def twistedChainFiltration (q : ℤ) :
    Subobject ((twistedChainComplex L).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (twistedChainFiltrationι L X q)

/-- The `q`-th stage of the filtration is the subobject given by the inclusion of the twisted
chains of `X q`. -/
lemma twistedChainFiltration_def (q : ℤ) :
    twistedChainFiltration L X q = Subobject.mk (twistedChainFiltrationι L X q) :=
  (rfl)

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the twisted chains of `X a` into those of `Y` factors
through the twisted chains of `X b`. -/
@[reassoc (attr := simp)]
lemma extendMap_subsetTwistedChainComplexMap_comp_twistedChainFiltrationι {a b : ℤ}
    (hab : X a ⊆ X b) :
    extendMap (subsetTwistedChainComplexMap L hab) ComplexShape.embeddingDownNat ≫
        twistedChainFiltrationι L X b =
      twistedChainFiltrationι L X a :=
  (extendMap_comp _ _ _).symm.trans <|
    congrArg (extendMap · _) (subsetTwistedChainComplexMap_twistedChainComplexMap L hab)

/-- The filtration of twisted chains is monotone in the subsets. -/
lemma twistedChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    twistedChainFiltration L X a ≤ twistedChainFiltration L X b :=
  Subobject.mk_le_mk_of_comm _
    (extendMap_subsetTwistedChainComplexMap_comp_twistedChainFiltrationι L hab)

/-- An increasing family of subsets gives an increasing filtration of twisted chains. -/
lemma monotone_twistedChainFiltration (hX : Monotone X) :
    Monotone (twistedChainFiltration L X) :=
  fun _ _ h ↦ twistedChainFiltration_mono L (hX h)

/-- The stage of the filtration of twisted chains at an empty subset is zero. -/
@[simp]
lemma twistedChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) : twistedChainFiltration L X a = ⊥ := by
  have : IsEmpty (X a) := by rw [ha]; exact Set.isEmpty_coe_sort.2 rfl
  -- An empty space has no singular simplices, so its twisted chains vanish in every degree.
  have hZ : IsZero (twistedChainComplex
      ((pullback (X := TopCat.of ↥(X a)) (ContinuousMap.subtypeVal (X a))).obj L)) :=
    (IsZero.iff_id_eq_zero _).2 <| HomologicalComplex.hom_ext _ _ fun _ ↦
      twistedChainComplex_hom_ext _ fun σ ↦ isEmptyElim (initialVertex σ).as
  exact Subobject.mk_eq_bot_iff_zero.2
    (((ComplexShape.embeddingDownNat.extendFunctor _).map_isZero hZ).eq_of_src _ _)

/-- The stage of the filtration of twisted chains at the whole space is everything. -/
@[simp]
lemma twistedChainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) :
    twistedChainFiltration L X b = ⊤ := by
  let s : Y ⟶ TopCat.of ↥(X b) :=
    TopCat.ofHom ⟨fun y ↦ ⟨y, Set.eq_univ_iff_forall.1 hb y⟩, by fun_prop⟩
  have hs : s ≫ TopCat.ofHom (ContinuousMap.subtypeVal (X b)) = 𝟙 Y := rfl
  -- Every singular simplex of `Y` lies in `X b`, so the inclusion of the twisted chains of `X b`
  -- is onto in every degree.
  have (k : ℕ) :
      Epi ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (X b))) L).f k) := by
    refine ⟨fun g h hgh ↦ twistedChainComplex_hom_ext _ fun τ ↦ ?_⟩
    obtain ⟨σ, rfl⟩ : ∃ σ, (TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.subtypeVal (X b)))).app _ σ = τ :=
      ⟨(TopCat.toSSet.map s).app _ τ, by rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← Functor.map_comp, hs, CategoryTheory.Functor.map_id, NatTrans.id_app,
        ConcreteCategory.id_apply]⟩
    exact (ιTwistedChainComplex_twistedChainComplexMap_f_assoc _ L k σ g).symm.trans <|
      (congrArg (_ ≫ ·) hgh).trans (ιTwistedChainComplex_twistedChainComplexMap_f_assoc _ L k σ h)
  have (k : ℕ) :
      IsIso ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (X b))) L).f k) :=
    isIso_of_mono_of_epi _
  have := HomologicalComplex.Hom.isIso_of_components
    (twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal (X b))) L)
  have : IsIso (twistedChainFiltrationι L X b) := by
    rw [twistedChainFiltrationι]
    infer_instance
  exact Subobject.mk_eq_top_of_isIso _

/-- **The abutment of the spectral sequence of a filtered space with local coefficients** in
degree `-n` is the twisted homology `Hₙ(Y; L)`. -/
def twistedChainFiltrationAbutmentIso (hX : Monotone X) (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_twistedChainFiltration L hX))).abutment
        (-n) ≅
      (twistedChainComplex L).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- The identification of the abutment is the identification
`CochainComplex.filtrationAbutmentIso` of the abutment of a filtered complex with its cohomology,
followed by the identification of the cohomology of the reindexed complex. -/
lemma twistedChainFiltrationAbutmentIso_eq (hX : Monotone X) (n : ℕ) :
    twistedChainFiltrationAbutmentIso L hX n =
      CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
        extendHomologyIso _ ComplexShape.embeddingDownNat rfl :=
  (rfl)

end LocalCoefficientSystem

end TauCeti
