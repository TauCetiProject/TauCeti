/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Additive automorphisms are `ℤ`-linear automorphisms

An additive automorphism of a commutative additive group `M` is automatically `ℤ`-linear
(`AddEquiv.toIntLinearEquiv`), and this identifies the additive automorphism group of `M` with
its group of `ℤ`-linear automorphisms. Mathlib writes `AddAut M` additively, so this is an
isomorphism `AddAut M ≃+ Additive (M ≃ₗ[ℤ] M)`, of the same shape as Mathlib's
`ZMod.AddAutEquivUnits`.

Composing with Mathlib's `MulAutMultiplicative` gives the multiplicative form
`MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M)`. This identifies the automorphism group of a free
abelian group written multiplicatively, such as `Multiplicative (Fin n → ℤ)`, with its group of
`ℤ`-linear automorphisms, and from there with the invertible integer matrices.

## Main definitions

* `TauCeti.addAutEquivIntLinearEquiv`: `AddAut M ≃+ Additive (M ≃ₗ[ℤ] M)`.
* `TauCeti.mulAutMultiplicativeEquivIntLinearEquiv`: `MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M)`.
-/

public section

namespace TauCeti

open Multiplicative

/-- The additive automorphisms of `M` are its `ℤ`-linear automorphisms. -/
def addAutEquivIntLinearEquiv (M : Type*) [AddCommGroup M] :
    AddAut M ≃+ Additive (M ≃ₗ[ℤ] M) where
  toFun φ := .ofMul φ.toIntLinearEquiv
  invFun f := f.toMul.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The linear automorphism attached to `φ` acts as `φ` does. -/
@[simp]
theorem addAutEquivIntLinearEquiv_apply_apply {M : Type*} [AddCommGroup M] (φ : AddAut M)
    (x : M) : (addAutEquivIntLinearEquiv M φ).toMul x = φ x :=
  (rfl)

/-- The additive automorphism attached to `f` acts as `f` does. -/
@[simp]
theorem addAutEquivIntLinearEquiv_symm_apply_apply {M : Type*} [AddCommGroup M]
    (f : Additive (M ≃ₗ[ℤ] M)) (x : M) : (addAutEquivIntLinearEquiv M).symm f x = f.toMul x :=
  (rfl)

/-- The automorphisms of `M` written multiplicatively are its `ℤ`-linear automorphisms. -/
def mulAutMultiplicativeEquivIntLinearEquiv (M : Type*) [AddCommGroup M] :
    MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M) :=
  (MulAutMultiplicative M).trans (AddEquiv.toMultiplicativeLeft (addAutEquivIntLinearEquiv M))

/-- The linear automorphism attached to `φ` acts as `φ` does, read additively. -/
@[simp]
theorem mulAutMultiplicativeEquivIntLinearEquiv_apply_apply {M : Type*} [AddCommGroup M]
    (φ : MulAut (Multiplicative M)) (x : M) :
    mulAutMultiplicativeEquivIntLinearEquiv M φ x = (φ (ofAdd x)).toAdd :=
  (rfl)

/-- The automorphism of `Multiplicative M` attached to `f` acts as `f` does, read
multiplicatively. -/
@[simp]
theorem mulAutMultiplicativeEquivIntLinearEquiv_symm_apply_apply {M : Type*} [AddCommGroup M]
    (f : M ≃ₗ[ℤ] M) (x : Multiplicative M) :
    (mulAutMultiplicativeEquivIntLinearEquiv M).symm f x = ofAdd (f x.toAdd) :=
  (rfl)

end TauCeti
