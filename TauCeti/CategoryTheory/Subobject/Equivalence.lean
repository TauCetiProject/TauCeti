/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Subobject lattices along an equivalence of categories

An equivalence of categories `e : C ≌ D` induces, for every object `X` of `C`, an equivalence
`MonoOver X ≌ MonoOver (e.functor.obj X)` (Mathlib's `CategoryTheory.MonoOver.congr`), hence an
equivalence between the thin skeletons, which are the subobject lattices. Since these lattices are
partial orders, that equivalence is an order isomorphism. This file records it as such, so that
lattice-theoretic properties of subobjects -- compactness, atoms, chain conditions -- can be
transported along equivalences.

## Main definitions

* `CategoryTheory.Equivalence.subobjectOrderIso`: the order isomorphism
  `Subobject X ≃o Subobject (e.functor.obj X)` induced by an equivalence `e`.

## Main results

* `CategoryTheory.Equivalence.subobjectOrderIso_mk`: it sends the subobject represented by a
  monomorphism `f` to the one represented by `e.functor.map f`.
-/

public section

namespace CategoryTheory.Equivalence

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) (X : C)

/-- **Subobjects along an equivalence.** An equivalence of categories `e` induces an order
isomorphism from the subobjects of `X` to the subobjects of `e.functor.obj X`. -/
noncomputable def subobjectOrderIso : Subobject X ≃o Subobject (e.functor.obj X) :=
  (Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso

/-- The induced order isomorphism sends the subobject represented by a monomorphism `f` to the
subobject represented by `e.functor.map f`. -/
@[simp]
theorem subobjectOrderIso_mk {Y : C} (f : Y ⟶ X) [Mono f] :
    e.subobjectOrderIso X (Subobject.mk f) = Subobject.mk (e.functor.map f) :=
  -- The proof is definitional, and no lemma-based proof is available: `Subobject.mk` and
  -- `Subobject.lower` are definitional wrappers around `toThinSkeleton` and `ThinSkeleton.map`,
  -- whose commutation `ThinSkeleton.comp_toThinSkeleton` is itself `rfl`, and Mathlib has no
  -- evaluation lemma for `MonoOver.congr` on `MonoOver.mk`. The functor equation
  -- `MonoOver.congr_functor` cannot be rewritten under `MonoOver.arrow` either, because the source
  -- of that arrow depends on the functor. Both sides reduce to `Subobject.mk` of the same
  -- `Over.post` image, which is why `rfl` closes the goal.
  (rfl)

end CategoryTheory.Equivalence
