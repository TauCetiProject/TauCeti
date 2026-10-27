/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Binomial expansions under extension of scalars of multivariate polynomials

Under the identification `A ⊗[R] R[X_σ] ≃ A[X_σ]` of `MvPolynomial.algebraTensorAlgEquiv`, the
power `(u - a v) ^ i` of polynomials `u, v` over `R` and a scalar `a` of `A` is the image of the
tensor `∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. Contracting the `A`-leg of this tensor against a
linear functional gives a weighted sum of the binomial terms. For `A = R[t]` and `a = t`,
coefficient functionals extract individual terms: the coefficient of `tⁿ` in `(u - t v) ^ i`
is `(-1)ⁿ (i choose n) uⁱ⁻ⁿ vⁿ`.

## Main declarations

* `MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow`: the binomial expansion of
  `(u - a v) ^ i` on the tensor side.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} {A : Type*} [CommRing A] [Algebra R A]

/-- The binomial expansion of `(u - a v) ^ i` under `A ⊗[R] R[X_σ] ≃ A[X_σ]`: it is the image of
`∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. -/
theorem algebraTensorAlgEquiv_sum_tmul_pow_mul_pow (a : A) (u v : MvPolynomial σ R) (i : ℕ) :
    algebraTensorAlgEquiv R A
        (∑ l ∈ Finset.range (i + 1),
          (((-1) ^ l * (i.choose l : R)) • a ^ l) ⊗ₜ[R] (u ^ (i - l) * v ^ l)) =
      (map (algebraMap R A) u - C a * map (algebraMap R A) v) ^ i := by
  rw [sub_eq_neg_add, add_pow, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [algebraTensorAlgEquiv_tmul, smul_eq_C_mul, Algebra.smul_def]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

end MvPolynomial
