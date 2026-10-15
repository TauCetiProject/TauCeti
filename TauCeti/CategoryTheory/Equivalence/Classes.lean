/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Opposite

/-!
# The group of autoequivalence classes

The units of the monoid of natural isomorphism classes of endofunctors form a
group. Its opposite uses functional composition as multiplication: the product
of the classes of `F` and `G` is the class of `G ⋙ F`. Every self-equivalence
defines an element, with its inverse functor representing the inverse element.

This group is the target for the homotopy-category Artin representation.
For underlying skeleton calculations, activate `endofunctorMonoidalCategory`
locally, as in Mathlib.
-/

public section
noncomputable section
namespace TauCeti

open CategoryTheory
universe v u
variable (C : Type u) [Category.{v} C]
attribute [local instance] endofunctorMonoidalCategory

/-- Autoequivalence classes, with multiplication in functional composition order. -/
abbrev AutoequivalenceClass := ((Skeleton (C ⥤ C))ˣ)ᵐᵒᵖ

end TauCeti

namespace CategoryTheory

open TauCeti
universe v u
variable {C : Type u} [Category.{v} C]
attribute [local instance] endofunctorMonoidalCategory

private def equivalenceSkeletonUnit (e : C ≌ C) : (Skeleton (C ⥤ C))ˣ where
  val := toSkeleton e.functor
  inv := toSkeleton e.inverse
  val_inv := by
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact congr_toSkeleton_of_iso e.unitIso.symm
  inv_val := by
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact congr_toSkeleton_of_iso e.counitIso

/-- A self-equivalence determines its natural isomorphism class as a group element. -/
def Equivalence.toAutoequivalenceClass (e : C ≌ C) : AutoequivalenceClass C :=
  MulOpposite.op (equivalenceSkeletonUnit e)

/-- The forward functor represents the underlying endofunctor class. -/
@[simp]
theorem Equivalence.toAutoequivalenceClass_val (e : C ≌ C) :
    e.toAutoequivalenceClass.unop.val = toSkeleton e.functor := by
  -- Both projections compute from the chosen unit; the opposite changes only multiplication.
  rfl

/-- The inverse functor represents the inverse unit component. -/
@[simp]
theorem Equivalence.toAutoequivalenceClass_inv_val (e : C ≌ C) :
    (e.toAutoequivalenceClass.unop⁻¹).val = toSkeleton e.inverse := by
  -- The chosen inverse unit component is the inverse functor's class.
  rfl

/-- Two self-equivalences have the same class exactly when their functors
are naturally isomorphic. -/
theorem Equivalence.toAutoequivalenceClass_eq_iff (e e' : C ≌ C) :
    e.toAutoequivalenceClass = e'.toAutoequivalenceClass ↔ Nonempty (e.functor ≅ e'.functor) := by
  constructor
  · intro h
    have hv := congrArg (fun x : AutoequivalenceClass C ↦ x.unop.val) h
    simpa only [Equivalence.toAutoequivalenceClass_val, toSkeleton_eq_toSkeleton_iff] using hv
  · rintro ⟨h⟩
    apply MulOpposite.unop_injective
    apply Units.ext
    simpa only [Equivalence.toAutoequivalenceClass_val] using congr_toSkeleton_of_iso h

/-- The identity equivalence represents the identity group element. -/
@[simp]
theorem Equivalence.toAutoequivalenceClass_refl :
    (Equivalence.refl (C := C)).toAutoequivalenceClass = 1 := by
  apply MulOpposite.unop_injective
  apply Units.ext
  -- The identity functor is the tensor unit of the endofunctor monoidal category.
  change toSkeleton (𝟭 C) = 1
  exact Skeleton.one_eq.symm

/-- Taking the inverse equivalence gives the inverse group element. -/
@[simp]
theorem Equivalence.toAutoequivalenceClass_symm (e : C ≌ C) :
    e.symm.toAutoequivalenceClass = e.toAutoequivalenceClass⁻¹ := by
  apply MulOpposite.unop_injective
  apply Units.ext
  -- Both values are the class of the chosen inverse functor.
  rfl

/-- Equivalence composition is reversed in functional-order multiplication. -/
@[simp]
theorem Equivalence.toAutoequivalenceClass_trans (e e' : C ≌ C) :
    (e.trans e').toAutoequivalenceClass = e'.toAutoequivalenceClass * e.toAutoequivalenceClass := by
  apply MulOpposite.unop_injective
  apply Units.ext
  -- The endofunctor tensor product is diagrammatic functor composition.
  change toSkeleton (e.functor ⋙ e'.functor) = toSkeleton e.functor * toSkeleton e'.functor
  exact Skeleton.toSkeleton_tensorObj _ _

end CategoryTheory
