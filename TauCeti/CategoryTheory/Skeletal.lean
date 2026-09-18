/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Comparing objects in the skeleton of a full subcategory

Mathlib's `CategoryTheory.toSkeleton_eq_toSkeleton_iff` says that two objects have the same class
in `CategoryTheory.Skeleton C` exactly when they are isomorphic *in `C`*. When `C` is a full
subcategory `P.FullSubcategory`, that is an isomorphism of the bundled pairs, whereas a consumer
starts and ends with objects of the ambient category and wants an isomorphism there. The gap is
only bookkeeping -- the inclusion `ObjectProperty.ι` is full and faithful, so the two notions of
isomorphism correspond -- but it has to be crossed every time the skeleton of a full subcategory is
used as a type of isomorphism classes. This file crosses it once.

The same gap is crossed once more to descend functions to such a skeleton: a function on the full
subcategory that is invariant under isomorphism in the ambient category descends to the skeleton.

Its consumers are `TauCeti.SimpleFDRepClasses` and `TauCeti.AlgebraicGeometry.LineBundleClass`,
the types of isomorphism classes of simple representations and of line bundles.

## Main results

* `CategoryTheory.ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso`: two objects of a full
  subcategory have the same class in its skeleton exactly when they are isomorphic in the ambient
  category;
* `CategoryTheory.ObjectProperty.skeletonLift` descends a function on a full subcategory that is
  invariant under isomorphism in the ambient category to its skeleton, with computation rule
  `CategoryTheory.ObjectProperty.skeletonLift_toSkeleton`.
-/

public section

namespace CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v w

namespace ObjectProperty

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Descend a function on a full subcategory that is invariant under isomorphism of the underlying
objects of the ambient category to the skeleton of the full subcategory.

`Skeleton` is by definition the quotient by `isIsomorphicSetoid`, so this is `Quotient.lift`, and
`skeletonLift_toSkeleton` holds by `rfl`. -/
noncomputable def skeletonLift {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Sort w} (f : P.FullSubcategory → α)
    (hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y) :
    Skeleton P.FullSubcategory → α :=
  Quotient.lift f fun X Y e ↦ e.elim fun i ↦ hf X Y ⟨P.ι.mapIso i⟩

/-- Applying `skeletonLift` to the class of `X` recovers the original function at `X`. -/
@[simp]
theorem skeletonLift_toSkeleton {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Sort w} {f : P.FullSubcategory → α}
    {hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y}
    (X : P.FullSubcategory) :
    P.skeletonLift f hf (toSkeleton X) = f X :=
  (rfl)

end ObjectProperty

end CategoryTheory
