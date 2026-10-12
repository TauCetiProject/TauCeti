/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Transporting bialgebra homomorphisms along bialgebra equivalences

Bialgebra equivalences `A₁ ≃ₐc[R] A₁'` and `A₂ ≃ₐc[R] A₂'` identify the bialgebra homomorphisms
`A₁ →ₐc[R] A₂` with the bialgebra homomorphisms `A₁' →ₐc[R] A₂'`, by conjugation. This is the
bialgebra analogue of Mathlib's `AlgEquiv.arrowCongr`. It is used to compare functors of bialgebra
homomorphisms whose values are only identified up to canonical bialgebra isomorphisms, such as
iterated base changes.

## Main definitions

* `BialgEquiv.arrowCongr`: the bijection `(A₁ →ₐc[R] A₂) ≃ (A₁' →ₐc[R] A₂')` induced by two
  bialgebra equivalences.

## Main results

* `BialgEquiv.arrowCongr_apply` and `BialgEquiv.arrowCongr_symm_apply`: it and its inverse are
  conjugation by the two equivalences.
-/

public section

namespace BialgEquiv

variable {R A₁ A₂ A₁' A₂' : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₁']
  [Semiring A₂'] [Bialgebra R A₁] [Bialgebra R A₂] [Bialgebra R A₁'] [Bialgebra R A₂']

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as bialgebras, then the type of
bialgebra homomorphisms `A₁ →ₐc[R] A₂` is equivalent to the type of bialgebra homomorphisms
`A₁' →ₐc[R] A₂'`. -/
def arrowCongr (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') : (A₁ →ₐc[R] A₂) ≃ (A₁' →ₐc[R] A₂') where
  toFun f := (e₂ : A₂ →ₐc[R] A₂').comp (f.comp (e₁.symm : A₁' →ₐc[R] A₁))
  invFun f := (e₂.symm : A₂' →ₐc[R] A₂).comp (f.comp (e₁ : A₁ →ₐc[R] A₁'))
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- `BialgEquiv.arrowCongr e₁ e₂` sends `f` to `e₂ ∘ f ∘ e₁⁻¹`. -/
@[simp]
theorem arrowCongr_apply (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') (f : A₁ →ₐc[R] A₂) :
    arrowCongr e₁ e₂ f = (e₂ : A₂ →ₐc[R] A₂').comp (f.comp (e₁.symm : A₁' →ₐc[R] A₁)) :=
  (rfl)

/-- The inverse of `BialgEquiv.arrowCongr e₁ e₂` sends `f` to `e₂⁻¹ ∘ f ∘ e₁`. -/
@[simp]
theorem arrowCongr_symm_apply (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') (f : A₁' →ₐc[R] A₂') :
    (arrowCongr e₁ e₂).symm f = (e₂.symm : A₂' →ₐc[R] A₂).comp (f.comp (e₁ : A₁ →ₐc[R] A₁')) :=
  (rfl)

end BialgEquiv
