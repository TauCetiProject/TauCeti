/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Category.TopPair

/-!
# The pair of a topological module and its nonzero vectors

A continuous linear equivalence `f : E ≃L[R] F` carries the nonzero vectors of `E` onto those of
`F`, so it induces an isomorphism of pairs `(E, E ∖ {0}) ≅ (F, F ∖ {0})`
(`ContinuousLinearEquiv.complZeroPairIso`). These pairs compute local homology and cohomology at
the origin, and they are the fibres of the Thom pair of a vector bundle.

## Main definitions

* `ContinuousLinearEquiv.complZeroPairIso`: the isomorphism of pairs
  `(E, E ∖ {0}) ≅ (F, F ∖ {0})` induced by a continuous linear equivalence.
-/

public section

open CategoryTheory

universe w

namespace ContinuousLinearEquiv

variable {R : Type*} [Semiring R] {E F G : Type w}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace G] [AddCommMonoid G] [Module R G]

/-- A continuous linear equivalence sends nonzero vectors to nonzero vectors. -/
theorem mapsTo_compl_zero (f : E ≃L[R] F) : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ := fun _ hx ↦ by
  rw [Set.mem_compl_singleton_iff] at hx ⊢
  exact f.map_ne_zero_iff.2 hx

/-- The isomorphism of pairs `(E, E ∖ {0}) ≅ (F, F ∖ {0})` induced by a continuous linear
equivalence `f : E ≃L[R] F`. -/
def complZeroPairIso (f : E ≃L[R] F) :
    TopPair.ofSubset (X := TopCat.of E) ({0}ᶜ : Set E) ≅
      TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetIso (X := TopCat.of E) (Y := TopCat.of F) f.toHomeomorph fun _ ↦ by
    rw [Set.mem_compl_singleton_iff, Set.mem_compl_singleton_iff, coe_toHomeomorph]
    exact f.map_ne_zero_iff.symm

@[simp]
theorem complZeroPairIso_hom_fst_apply (f : E ≃L[R] F) (x : E) :
    TopPair.Hom.fst f.complZeroPairIso.hom x = f x := by
  rw [complZeroPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

@[simp]
theorem complZeroPairIso_inv_fst_apply (f : E ≃L[R] F) (y : F) :
    TopPair.Hom.fst f.complZeroPairIso.inv y = f.symm y := by
  rw [complZeroPairIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The map of pairs underlying `ContinuousLinearEquiv.complZeroPairIso f` is the map induced by
`f` as a continuous linear map. -/
theorem complZeroPairIso_hom (f : E ≃L[R] F) :
    f.complZeroPairIso.hom =
      TopPair.ofSubsetMap (TopCat.ofHom ((f : E →L[R] F) : C(E, F))) f.mapsTo_compl_zero :=
  TopPair.hom_ext_of_fst _ (by
    ext x
    exact (f.complZeroPairIso_hom_fst_apply x).trans (TopPair.ofSubsetMap_fst_apply
      (TopCat.ofHom ((f : E →L[R] F) : C(E, F))) f.mapsTo_compl_zero x).symm)

/-- The inverse map of pairs underlying `ContinuousLinearEquiv.complZeroPairIso f` is the map
induced by `f.symm` as a continuous linear map. -/
theorem complZeroPairIso_inv (f : E ≃L[R] F) :
    f.complZeroPairIso.inv =
      TopPair.ofSubsetMap (TopCat.ofHom ((f.symm : F →L[R] E) : C(F, E)))
        f.symm.mapsTo_compl_zero :=
  TopPair.hom_ext_of_fst _ (by
    ext y
    exact (f.complZeroPairIso_inv_fst_apply y).trans (TopPair.ofSubsetMap_fst_apply
      (TopCat.ofHom ((f.symm : F →L[R] E) : C(F, E))) f.symm.mapsTo_compl_zero y).symm)

/-- The pair isomorphism of the identity is the identity. -/
@[simp]
theorem complZeroPairIso_refl :
    (ContinuousLinearEquiv.refl R E).complZeroPairIso = Iso.refl _ := by
  ext : 1
  rw [Iso.refl_hom, complZeroPairIso_hom]
  exact TopPair.ofSubsetMap_id _

/-- The pair isomorphism of a composite is the composite of the pair isomorphisms. -/
@[simp]
theorem complZeroPairIso_trans (f : E ≃L[R] F) (g : F ≃L[R] G) :
    (f.trans g).complZeroPairIso = f.complZeroPairIso ≪≫ g.complZeroPairIso := by
  ext : 1
  rw [Iso.trans_hom, complZeroPairIso_hom, complZeroPairIso_hom, complZeroPairIso_hom]
  exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; simp)).symm

/-- The pair isomorphism of the inverse is the inverse of the pair isomorphism. -/
@[simp]
theorem complZeroPairIso_symm (f : E ≃L[R] F) :
    f.symm.complZeroPairIso = f.complZeroPairIso.symm := by
  ext : 1
  rw [complZeroPairIso_hom, Iso.symm_hom, complZeroPairIso_inv]

end ContinuousLinearEquiv
