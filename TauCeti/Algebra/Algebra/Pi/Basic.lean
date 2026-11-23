/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi

/-!
# Universal property of algebra homomorphisms into a dependent product

This module packages Mathlib's `AlgHom.pi` and `Pi.evalAlgHom` as the equivalence
`AlgHom.piEquiv : (∀ i, A →ₐ[k] R i) ≃ (A →ₐ[k] ∀ i, R i)`, oriented in the same direction as
Mathlib's `AlgHom.prodEquiv`.
-/

public section

namespace AlgHom

section PiEquiv

variable {k A ι : Type*} {R : ι → Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [∀ i, Semiring (R i)] [∀ i, Algebra k (R i)]

/-- Families of `k`-algebra homomorphisms into `R i` correspond to homomorphisms into
`∀ i, R i`. -/
def piEquiv : (∀ i, A →ₐ[k] R i) ≃ (A →ₐ[k] ∀ i, R i) where
  toFun := AlgHom.pi
  invFun x i := (Pi.evalAlgHom k R i).comp x
  left_inv f := by ext i a; rfl
  right_inv x := by ext a i; rfl

/-- Applying `AlgHom.piEquiv` gives `AlgHom.pi`. -/
@[simp]
theorem piEquiv_apply (f : ∀ i, A →ₐ[k] R i) :
    AlgHom.piEquiv f = AlgHom.pi f := (rfl)

/-- Evaluating `AlgHom.piEquiv f` on `a : A` at index `i` returns `f i a`. -/
theorem piEquiv_apply_apply (f : ∀ i, A →ₐ[k] R i) (a : A) (i : ι) :
    AlgHom.piEquiv f a i = f i a := (rfl)

/-- Evaluating `AlgHom.piEquiv.symm x` at index `i` postcomposes with `Pi.evalAlgHom k R i`. -/
@[simp]
theorem piEquiv_symm_apply (x : A →ₐ[k] ∀ i, R i) (i : ι) :
    AlgHom.piEquiv.symm x i = (Pi.evalAlgHom k R i).comp x := (rfl)

end PiEquiv

end AlgHom
