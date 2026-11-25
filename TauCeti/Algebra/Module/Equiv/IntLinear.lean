/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Automorphisms of an additive group written multiplicatively

An additive automorphism of a commutative additive group `M` is automatically `ℤ`-linear
(`AddEquiv.toIntLinearEquiv`). Composing this with Mathlib's identification of the automorphisms
of `Multiplicative M` with the additive automorphisms of `M` gives an isomorphism of groups
`MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M)`. This identifies the automorphism group of a free
abelian group written multiplicatively, such as `Multiplicative (Fin n → ℤ)`, with its group of
`ℤ`-linear automorphisms, and from there with the invertible integer matrices.

## Main definitions

* `TauCeti.mulAutMultiplicativeEquiv`: `MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M)`.
-/

public section

namespace TauCeti

open Multiplicative

/-- The automorphisms of `M` written multiplicatively are its `ℤ`-linear automorphisms. -/
def mulAutMultiplicativeEquiv (M : Type*) [AddCommGroup M] :
    MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M) where
  toFun φ := (AddEquiv.toMultiplicative.symm φ).toIntLinearEquiv
  invFun f := AddEquiv.toMultiplicative f.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The linear automorphism attached to `φ` acts as `φ` does, read additively. -/
@[simp]
theorem mulAutMultiplicativeEquiv_apply_apply {M : Type*} [AddCommGroup M]
    (φ : MulAut (Multiplicative M)) (x : M) :
    mulAutMultiplicativeEquiv M φ x = (φ (ofAdd x)).toAdd :=
  (rfl)

/-- The automorphism of `Multiplicative M` attached to `f` acts as `f` does, read
multiplicatively. -/
@[simp]
theorem mulAutMultiplicativeEquiv_symm_apply_apply {M : Type*} [AddCommGroup M]
    (f : M ≃ₗ[ℤ] M) (x : Multiplicative M) :
    (mulAutMultiplicativeEquiv M).symm f x = ofAdd (f x.toAdd) :=
  (rfl)

end TauCeti
