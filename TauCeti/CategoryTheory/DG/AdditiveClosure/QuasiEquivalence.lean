/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.AdditiveClosure.Basic
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# Quasi-isomorphisms of Hom complexes on additive closures

The embedding of a DG category into its additive closure is an isomorphism on Hom complexes
(`TauCeti.DGAdditiveClosure.isIso_embedding_map`), and it commutes with the DG functors induced
by a DG functor `F`.  So on one-term sums, the DG functor induced by `F` on additive closures is a
quasi-isomorphism on Hom complexes exactly when `F` is.

## Main results

* `CategoryTheory.EnrichedFunctor.quasiIso_mapDGAdditiveClosure_map_iff`: on one-term sums, the
  induced DG functor is a quasi-isomorphism on Hom complexes exactly when the original one is.
-/

public section

open CategoryTheory

namespace CategoryTheory.EnrichedFunctor

open TauCeti

universe v u u₂

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- **On one-term sums, the DG functor induced on additive closures is a quasi-isomorphism on Hom
complexes exactly when the original one is**: the additive closure does not change these Hom
complexes. -/
theorem quasiIso_mapDGAdditiveClosure_map_iff
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) (X Y : C) :
    QuasiIso (F.mapDGAdditiveClosure.map ((DGAdditiveClosure.embedding R).obj X)
      ((DGAdditiveClosure.embedding R).obj Y)) ↔ QuasiIso (F.map X Y) := by
  have e : ((DGAdditiveClosure.embedding R).comp _ F.mapDGAdditiveClosure).map X Y =
      (F.comp _ (DGAdditiveClosure.embedding R)).map X Y := by
    ext n f
    refine (dgMap_apply _ f).symm.trans
      (Eq.trans ?_ (dgMap_apply (F.comp _ (DGAdditiveClosure.embedding R)) f))
    rw [comp_dgMap, comp_dgMap]
    refine DGAdditiveClosure.dgHom_ext R fun i j ↦ ?_
    rw [dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom,
      DGAdditiveClosure.dgMap_embedding, DGAdditiveClosure.dgMap_embedding]
    -- Both entries are `F f`; the one-term sums are those of `embeddingHomEquiv` up to unfolding
    -- `DGAdditiveClosure.embedding_obj`.
    exact (congrArg (F.dgMap n) (DGAdditiveClosure.dgHomEquiv_embeddingHomEquiv R f i j)).trans
      (DGAdditiveClosure.dgHomEquiv_embeddingHomEquiv R (F.dgMap n f) i j).symm
  rw [comp_map, comp_map] at e
  have := quasiIso_of_isIso ((DGAdditiveClosure.embedding R).map X Y)
  rw [← quasiIso_iff_comp_left ((DGAdditiveClosure.embedding R).map X Y), e]
  exact quasiIso_iff_comp_right _ _
    (hφ' := quasiIso_of_isIso ((DGAdditiveClosure.embedding R).map (F.obj X) (F.obj Y)))

end CategoryTheory.EnrichedFunctor
