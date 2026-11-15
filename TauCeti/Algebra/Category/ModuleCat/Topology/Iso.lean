/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Isomorphisms in `TopModuleCat` with a discrete target

A morphism of topological modules whose target carries the discrete topology is an isomorphism of
`TopModuleCat R` as soon as the underlying morphism of modules is one
(`TopModuleCat.isIso_of_isIso_forget₂_map`), in particular as soon as it is bijective
(`TopModuleCat.isIso_of_bijective`): the inverse is continuous because its source is
discrete. This is the counterpart, for the forgetful functor to `ModuleCat R` and under
discreteness of the target, of Mathlib's `(forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms`.
It turns Mathlib's invertibility results for the homology of forgotten cochain complexes into
isomorphisms of discrete cohomology modules.
-/

public section

open CategoryTheory

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- The forgetful functor to `ModuleCat R` acts on a morphism as its underlying linear map, the
counterpart of Mathlib's `TopModuleCat.hom_forget₂_TopCat_map` for the other forgetful functor. -/
@[simp]
theorem hom_forget₂_ModuleCat_map {X Y : TopModuleCat R} (f : X ⟶ Y) :
    ((forget₂ _ (ModuleCat R)).map f).hom = f.hom := rfl

/-- The forward morphism of `TopModuleCat.ofIso e` is `e` as a continuous linear map. -/
@[simp]
theorem ofIso_hom {X Y : TopModuleCat R} (e : X ≃L[R] Y) :
    (ofIso e).hom = ofHom e.toContinuousLinearMap := rfl

/-- A bijective morphism of topological modules into a discrete module is an isomorphism: the
inverse is continuous because its source is discrete. -/
theorem isIso_of_bijective {X Y : TopModuleCat R} [DiscreteTopology Y] (f : X ⟶ Y)
    (hf : Function.Bijective f) : IsIso f :=
  have : IsIso ((forget₂ (TopModuleCat R) TopCat).map f) :=
    TopCat.isIso_of_bijective_of_isOpenMap _ hf fun _ _ ↦ isOpen_discrete (α := Y) _
  isIso_of_reflects_iso f (forget₂ (TopModuleCat R) TopCat)

/-- A morphism of topological modules into a discrete module is an isomorphism as soon as its
underlying morphism of modules is one: that morphism is then bijective. -/
theorem isIso_of_isIso_forget₂_map {X Y : TopModuleCat R} [DiscreteTopology Y] (f : X ⟶ Y)
    [IsIso ((forget₂ (TopModuleCat R) (ModuleCat R)).map f)] : IsIso f :=
  isIso_of_bijective f (ConcreteCategory.bijective_of_isIso ((forget₂ _ (ModuleCat R)).map f))

end TopModuleCat
