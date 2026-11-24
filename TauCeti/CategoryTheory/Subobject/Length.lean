/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.KrullDimension

/-!
# The length of an object

The **length** of an object `X` of a category is the Krull dimension of its lattice of subobjects,
the supremum of the lengths `n` of strict chains `X₀ < X₁ < ⋯ < Xₙ` of subobjects, in `ℕ∞`. This
mirrors Mathlib's `Module.length`, defined through the lattice of submodules, and agrees with it on
modules (`ModuleCat.length_eq`).

This file records the facts that hold in any category: the length is invariant under isomorphism
and monotone along monomorphisms, and in a category with zero morphisms and a zero object it
vanishes exactly on the zero objects. Additivity on short exact sequences, which needs an abelian
category, is in `TauCeti.CategoryTheory.Abelian.Length`.

## Main definitions

* `CategoryTheory.length X`: the length of an object `X`, the Krull dimension of `Subobject X`.

## Main results

* `CategoryTheory.length_eq_of_orderIso`: objects with isomorphic subobject lattices have the same
  length, and `CategoryTheory.Iso.length_eq`: length is invariant under isomorphism.
* `CategoryTheory.length_le_of_mono`: length is monotone along monomorphisms.
* `CategoryTheory.length_image_le_right`: the image of a morphism is at most as long as its target.
* `CategoryTheory.length_image_eq_of_fac`: if `f` factors as a strong epimorphism `e : X ⟶ I`
  followed by a monomorphism, the image of `f` is as long as `I`.
* `CategoryTheory.length_eq_zero_iff`: an object has length zero exactly when it is a zero object,
  in a category with zero morphisms and a zero object.
* `CategoryTheory.eq_zero_of_length_image_eq_zero`: a morphism whose image has length zero is
  zero.

## Implementation notes

A monomorphism `f : X ⟶ Y` induces an order embedding of `Subobject X` into `Subobject Y`
(`CategoryTheory.Subobject.map`), whence monotonicity. Images are Mathlib's
`CategoryTheory.Limits.image`; a strong epi-mono factorization of `f` is an image of `f`
(`CategoryTheory.Limits.StrongEpiMonoFactorisation.toMonoIsImage`), so it passes through an object
isomorphic to `image f`. Lengths take values in
`ℕ∞`, so that objects of infinite length are allowed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

namespace CategoryTheory

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- The **length** of an object `X`: the Krull dimension of the lattice of subobjects of `X`, that
is the supremum of the lengths `n` of strict chains `X₀ < X₁ < ⋯ < Xₙ` of subobjects. For a module
this is `Module.length` (`ModuleCat.length_eq`). -/
noncomputable def length (X : C) : ℕ∞ :=
  (Order.krullDim (Subobject X)).unbot (by simp [Order.krullDim_eq_bot_iff])

/-- The length of `X`, as an element of `WithBot ℕ∞`, is the Krull dimension of `Subobject X`. -/
lemma coe_length (X : C) : (length X : WithBot ℕ∞) = Order.krullDim (Subobject X) :=
  WithBot.coe_unbot _ _

/-- Objects whose lattices of subobjects are isomorphic have the same length; the objects may lie
in different categories. -/
lemma length_eq_of_orderIso {D : Type u'} [Category.{v'} D] {X : C} {Y : D}
    (e : Subobject X ≃o Subobject Y) : length X = length Y :=
  WithBot.coe_injective (by rw [coe_length, coe_length, Order.krullDim_eq_of_orderIso e])

/-- **Length is invariant under isomorphism.** -/
lemma Iso.length_eq {X Y : C} (e : X ≅ Y) : length X = length Y :=
  length_eq_of_orderIso (Subobject.mapIsoToOrderIso e)

/-- **Length is monotone along monomorphisms**: the subobjects of `X` embed into those of `Y`
along a monomorphism `f : X ⟶ Y`. -/
theorem length_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : length X ≤ length Y :=
  WithBot.coe_le_coe.1 (by
    rw [coe_length, coe_length]
    exact Order.krullDim_le_of_strictMono _
      ((Subobject.map f).monotone.strictMono_of_injective (Subobject.map_obj_injective f)))

/-- **The image of a morphism is at most as long as its target.** -/
theorem length_image_le_right {X Y : C} (f : X ⟶ Y) [HasImage f] : length (image f) ≤ length Y :=
  length_le_of_mono (image.ι f)

/-- **The image of a composite of a strong epimorphism and a monomorphism** is as long as the
object through which they pass: if `e ≫ m = f` with `e : X ⟶ I` a strong epimorphism and
`m : I ⟶ Y` a monomorphism, then `length (image f) = length I`. -/
theorem length_image_eq_of_fac {X Y I : C} {e : X ⟶ I} [StrongEpi e] {m : I ⟶ Y} [Mono m]
    {f : X ⟶ Y} [HasImage f] (fac : e ≫ m = f) : length (image f) = length I :=
  let F : StrongEpiMonoFactorisation f := { I := I, m := m, e := e, fac := fac }
  (IsImage.isoExt F.toMonoIsImage (Image.isImage f)).length_eq.symm

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C] {X Y : C}

/-- **An object has length zero exactly when it is a zero object.** -/
@[simp]
lemma length_eq_zero_iff : length X = 0 ↔ IsZero X := by
  rw [← WithBot.coe_inj, coe_length, WithBot.coe_zero, Order.krullDim_eq_zero_iff_of_orderTop]
  refine ⟨fun h ↦ by_contra fun hX ↦ ?_, Subobject.subsingleton_of_isZero⟩
  exact not_nontrivial_iff_subsingleton.2 h (Subobject.nontrivial_of_not_isZero hX)

/-- **A morphism is zero when its image has length zero.** -/
theorem eq_zero_of_length_image_eq_zero (f : X ⟶ Y) [HasImage f] (h : length (image f) = 0) :
    f = 0 := by
  rw [← image.fac f, (length_eq_zero_iff.mp h).eq_of_tgt (factorThruImage f) 0, zero_comp]

end ZeroObject

end CategoryTheory
