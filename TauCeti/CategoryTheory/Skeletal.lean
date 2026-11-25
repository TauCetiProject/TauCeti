/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Set.Finite.Range

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

This is how types of isomorphism classes are built from the skeleton of a full subcategory, for
example the isomorphism classes of simple representations or of line bundles.

## Main results

* `CategoryTheory.ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso`: two objects of a full
  subcategory have the same class in its skeleton exactly when they are isomorphic in the ambient
  category;
* `CategoryTheory.ObjectProperty.finite_skeleton_iff_exists_finite_forall_exists_iso`: a full
  subcategory has finitely many isomorphism classes exactly when a finite set of objects of the
  ambient category contains a copy of each of its objects;
* `CategoryTheory.ObjectProperty.skeletonLift` descends a function on a full subcategory that is
  invariant under isomorphism in the ambient category to its skeleton, with computation rule
  `CategoryTheory.ObjectProperty.skeletonLift_toSkeleton`.
-/

public section

namespace CategoryTheory

universe u v w

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) :=
  toSkeleton_eq_toSkeleton_iff.trans P.fullyFaithfulι.isoEquiv.nonempty_congr

/-- A full subcategory has finitely many isomorphism classes exactly when a finite set of objects
of the ambient category contains a copy of each of its objects. -/
theorem finite_skeleton_iff_exists_finite_forall_exists_iso :
    Finite (Skeleton P.FullSubcategory) ↔
      ∃ S : Set C, S.Finite ∧ ∀ X, P X → ∃ Y ∈ S, Nonempty (X ≅ Y) := by
  refine ⟨fun h ↦ ?_, fun ⟨S, hS, h⟩ ↦ ?_⟩
  · -- One object from each isomorphism class.
    refine ⟨Set.range fun x : Skeleton P.FullSubcategory ↦ ((fromSkeleton _).obj x).obj,
      Set.finite_range _, fun X hX ↦ ?_⟩
    let Y : P.FullSubcategory := ⟨X, hX⟩
    exact ⟨_, ⟨toSkeleton Y, rfl⟩, ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)).symm⟩⟩
  · -- Send each class to a member of `S` isomorphic to its objects: this map is injective.
    have := hS.to_subtype
    choose q hq he using fun x : Skeleton P.FullSubcategory ↦ h _ ((fromSkeleton _).obj x).property
    refine Finite.of_injective (fun x ↦ (⟨q x, hq x⟩ : S)) fun x y hxy ↦ ?_
    obtain ⟨ex⟩ := he x
    obtain ⟨ey⟩ := he y
    rw [← toSkeleton_fromSkeleton_obj x, ← toSkeleton_fromSkeleton_obj y]
    exact (P.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _).mpr
      ⟨ex ≪≫ eqToIso (congrArg Subtype.val hxy) ≪≫ ey.symm⟩

/-- Descend a function on a full subcategory that is invariant under isomorphism of the underlying
objects of the ambient category to the skeleton of the full subcategory. -/
def skeletonLift {α : Sort w} (f : P.FullSubcategory → α)
    (hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y) :
    Skeleton P.FullSubcategory → α :=
  Quotient.lift f fun X Y e ↦ hf X Y (e.map P.ι.mapIso)

/-- Applying `skeletonLift` to the class of `X` recovers the original function at `X`. -/
@[simp]
theorem skeletonLift_toSkeleton {α : Sort w} {f : P.FullSubcategory → α}
    {hf : ∀ X Y : P.FullSubcategory, Nonempty (X.obj ≅ Y.obj) → f X = f Y}
    (X : P.FullSubcategory) :
    P.skeletonLift f hf (toSkeleton X) = f X :=
  (rfl)

end ObjectProperty

end CategoryTheory
