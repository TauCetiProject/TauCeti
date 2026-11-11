/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor products with spaces of finitely supported functions

Supplements to Mathlib's `TensorProduct.finsuppScalarLeft`, which identifies `(ι →₀ R) ⊗[R] N`
with `ι →₀ N` by taking coefficients against the standard basis, and to `finsuppTensorFinsupp'`,
which identifies `(α →₀ R) ⊗[R] (β →₀ R)` with `α × β →₀ R`.

## Main results

* `TensorProduct.finsuppScalarLeft_lTensor_apply`: taking coefficients is natural in `N`.
* `TensorProduct.sum_single_tmul_finsuppScalarLeft`: an element is the sum of its coefficients
  against the basis vectors.
* `finsuppTensorFinsupp'_mapDomain`: the identification of the tensor product of two spaces of
  finitely supported functions with functions on the product of the index types is natural in the
  index types.
-/

public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {N N' : Type*}
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

/-- The coefficients of `(1 ⊗ g) t` in `(ι →₀ R) ⊗ N'` are the images under `g` of the
coefficients of `t`. -/
@[simp]
lemma finsuppScalarLeft_lTensor_apply (g : N →ₗ[R] N') (t : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N' ι (g.lTensor _ t) i = g (finsuppScalarLeft R N ι t i) := by
  induction t <;> simp_all

/-- An element of `(ι →₀ R) ⊗ N` is the sum of its coefficients against the basis vectors. -/
lemma sum_single_tmul_finsuppScalarLeft (t : (ι →₀ R) ⊗[R] N) :
    ∑ i ∈ (finsuppScalarLeft R N ι t).support,
      Finsupp.single i (1 : R) ⊗ₜ finsuppScalarLeft R N ι t i = t := by
  simpa [Finsupp.sum, finsuppScalarLeft_symm_apply_single] using
    congr((finsuppScalarLeft R N ι).symm $(Finsupp.sum_single (finsuppScalarLeft R N ι t)))

end TensorProduct

section FinsuppTensorFinsupp

variable {R : Type*} [CommSemiring R] {α β α' β' : Type*}

/-- The identification `(α →₀ R) ⊗ (β →₀ R) ≃ (α × β →₀ R)` is natural in the index types: the
tensor product of two pushforwards is the pushforward along the product map. -/
theorem finsuppTensorFinsupp'_mapDomain (g₁ : α → α') (g₂ : β → β') (c : α →₀ R) (d : β →₀ R) :
    finsuppTensorFinsupp' R α' β' (Finsupp.mapDomain g₁ c ⊗ₜ[R] Finsupp.mapDomain g₂ d) =
      Finsupp.mapDomain (Prod.map g₁ g₂) (finsuppTensorFinsupp' R α β (c ⊗ₜ[R] d)) := by
  -- Both sides are linear in `c ⊗ₜ d`, so it suffices to compare them on basis vectors.
  have h : (finsuppTensorFinsupp' R α' β').toLinearMap ∘ₗ
      TensorProduct.map (Finsupp.lmapDomain R R g₁) (Finsupp.lmapDomain R R g₂) =
      Finsupp.lmapDomain R R (Prod.map g₁ g₂) ∘ₗ (finsuppTensorFinsupp' R α β).toLinearMap := by
    ext; simp [Finsupp.mapDomain_single]
  exact congr($h (c ⊗ₜ d))

end FinsuppTensorFinsupp
