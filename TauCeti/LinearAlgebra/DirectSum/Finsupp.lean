/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Coefficients in a tensor product with a free module

Two facts about Mathlib's `TensorProduct.finsuppScalarLeft`, which identifies `(ι →₀ R) ⊗[R] N`
with `ι →₀ N` by taking coefficients against the standard basis.

## Main results

* `TensorProduct.finsuppScalarLeft_lTensor_apply`: taking coefficients is natural in `N`.
* `TensorProduct.sum_single_tmul_finsuppScalarLeft`: an element is the sum of its coefficients
  against the basis vectors.
-/

public section

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] {N N' : Type*}
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

/-- The coefficients of `(1 ⊗ g) t` in `(ι →₀ R) ⊗ N'` are the images under `g` of the
coefficients of `t`. -/
lemma finsuppScalarLeft_lTensor_apply (g : N →ₗ[R] N') (t : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N' ι (g.lTensor _ t) i = g (finsuppScalarLeft R N ι t i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => simp
  | add a b ha hb => simp [ha, hb]

/-- An element of `(ι →₀ R) ⊗ N` is the sum of its coefficients against the basis vectors. -/
lemma sum_single_tmul_finsuppScalarLeft (t : (ι →₀ R) ⊗[R] N) :
    ∑ i ∈ (finsuppScalarLeft R N ι t).support,
      Finsupp.single i (1 : R) ⊗ₜ finsuppScalarLeft R N ι t i = t := by
  conv_rhs => rw [← (finsuppScalarLeft R N ι).symm_apply_apply t,
    ← Finsupp.sum_single (finsuppScalarLeft R N ι t)]
  simp [Finsupp.sum, finsuppScalarLeft_symm_apply_single]

end TensorProduct
