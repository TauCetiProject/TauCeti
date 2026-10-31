/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Binomial expansions and coefficients under extension of scalars of multivariate polynomials

Under the identification `A ⊗[R] R[X_σ] ≃ A[X_σ]` of `MvPolynomial.algebraTensorAlgEquiv`, the
power `(u - a v) ^ i` of polynomials `u, v` over `R` and a scalar `a` of `A` is the image of the
tensor `∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. Contracting the `A`-leg of this tensor against a
linear functional gives a weighted sum of the binomial terms. For `A = R[t]` and `a = t`,
coefficient functionals extract individual terms: the coefficient of `tⁿ` in `(u - t v) ^ i`
is `(-1)ⁿ (i choose n) uⁱ⁻ⁿ vⁿ`.

An element of `R[X_σ] ⊗[R] N` is determined by its coefficients, the images of the coefficient
functionals `MvPolynomial.lcoeff R e` on the polynomial leg.

## Main declarations

* `MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow`: the binomial expansion of
  `(u - a v) ^ i` on the tensor side.
* `MvPolynomial.ext_lid_rTensor_lcoeff`: elements of `R[X_σ] ⊗[R] N` with the same coefficients
  are equal.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section Binomial

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

end Binomial

section Ext

variable {R : Type*} [CommSemiring R] {σ : Type*} {N : Type*} [AddCommMonoid N] [Module R N]

/-- Elements of `R[X_σ] ⊗[R] N` with the same coefficients are equal. -/
theorem ext_lid_rTensor_lcoeff {x y : MvPolynomial σ R ⊗[R] N}
    (h : ∀ e, TensorProduct.lid R N ((lcoeff R e).rTensor N x) =
      TensorProduct.lid R N ((lcoeff R e).rTensor N y)) : x = y := by
  classical
  have hcoord (e : σ →₀ ℕ) : (basisMonomials σ R).coord e = lcoeff R e :=
    (basisMonomials σ R).ext fun s ↦ by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self]
      simp [coeff_monomial, Finsupp.single_apply]
  apply (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).injective
  ext e
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply,
    hcoord, h]

end Ext

end MvPolynomial
