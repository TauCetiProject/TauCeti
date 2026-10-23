/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Coefficients of polynomial laws

For a polynomial law `f : M →ₚₗ[R] N` and a finite family `m : ι → M`, the value of `f` at the
generic combination `∑ⱼ Xⱼ ⊗ mⱼ` over the polynomial ring `R[Xⱼ]` is a finite sum
`∑ₖ Xᵏ ⊗ cₖ`. The coefficients `cₖ = coeff m f k` determine `f`: after scalar extension to any
commutative `R`-algebra `S`,
`f (∑ⱼ sⱼ ⊗ mⱼ) = ∑ₖ (∏ⱼ sⱼ ^ kⱼ) ⊗ coeff m f k`.

These coefficients are the values of the linear maps out of divided powers which represent
homogeneous polynomial laws, so this file supplies the comparison tools used to construct them:
the change-of-variables formula for coefficients, the fact that a law is determined by its
coefficients, and the vanishing of the coefficients of a homogeneous law of degree `d` outside
total degree `d`.

## Main declarations

* `PolynomialLaw.coeff m`: the coefficients of a law at the generic combination of `m`, as an
  `R`-linear map to finitely supported functions on monomials.
* `PolynomialLaw.coeff_apply`: the coefficient of `Xᵏ`, extracted by `MvPolynomial.lcoeff`.
* `PolynomialLaw.toFun_sum_tmul_eq_coeff_sum`: the value of a law on any finite sum of pure
  tensors, in terms of its coefficients.
* `PolynomialLaw.coeff_eq_sum_of_sum_tmul_eq`: change of variables for coefficients.
* `PolynomialLaw.ext_coeff`: a law is determined by its coefficients on families indexed by
  `Fin n`.
* `PolynomialLaw.IsHomogeneousOfDegree.coeff_eq_zero`: a law homogeneous of degree `d` has no
  coefficients outside total degree `d`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Chapitre I][Roby-1963]
-/

public section

noncomputable section

universe u

open TensorProduct MvPolynomial

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

section Coeff

variable {ι : Type*} [Fintype ι]

variable (R N) in
/-- The coefficients of polynomial laws `M →ₚₗ[R] N` at the generic combination `∑ⱼ Xⱼ ⊗ mⱼ`:
`coeff m f k` is the coefficient of the monomial `Xᵏ` in `f (∑ⱼ Xⱼ ⊗ mⱼ)`, computed over the
polynomial ring `R[Xⱼ]`. -/
def coeff (m : ι → M) : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N where
  toFun f := by
    classical
    exact TensorProduct.equivFinsuppOfBasisLeft (basisMonomials ι R)
      (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))
  map_add' f g := by simp [toFun_add_apply]
  map_smul' r f := by simp [toFun_smul]

/-- The coefficient of `Xᵏ` in `f (∑ⱼ Xⱼ ⊗ mⱼ)`, extracted by `MvPolynomial.lcoeff`. -/
theorem coeff_apply (m : ι → M) (f : M →ₚₗ[R] N) (k : ι →₀ ℕ) :
    coeff R N m f k = TensorProduct.lid R N ((lcoeff R k).rTensor N
      (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))) := by
  classical
  rw [coeff, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.equivFinsuppOfBasisLeft_apply]
  rfl

/-- The value of `f` at the generic combination `∑ⱼ Xⱼ ⊗ mⱼ` is `∑ₖ Xᵏ ⊗ coeff m f k`. -/
theorem toFun_sum_X_tmul (m : ι → M) (f : M →ₚₗ[R] N) :
    f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j) =
      (coeff R N m f).sum fun k n ↦ monomial k 1 ⊗ₜ[R] n := by
  classical
  have := (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials ι R)).symm_apply_apply
    (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at this
  simpa only [coeff, LinearMap.coe_mk, AddHom.coe_mk, coe_basisMonomials] using this.symm

/-- The value of a polynomial law on a finite sum of pure tensors, in terms of its coefficients:
`f (∑ⱼ sⱼ ⊗ mⱼ) = ∑ₖ (∏ⱼ sⱼ ^ kⱼ) ⊗ coeff m f k`, for a commutative `R`-algebra `S` in any
universe. -/
theorem toFun_sum_tmul_eq_coeff_sum (m : ι → M) (f : M →ₚₗ[R] N) {S : Type*} [CommSemiring S]
    [Algebra R S] (s : ι → S) :
    f.toFun S (∑ j, s j ⊗ₜ[R] m j) =
      (coeff R N m f).sum fun k n ↦ (∏ j, s j ^ k j) ⊗ₜ[R] n := by
  have hs : ∑ j, s j ⊗ₜ[R] m j =
      (aeval s).toLinearMap.rTensor M (∑ j, X j ⊗ₜ[R] m j) := by
    simp
  rw [hs, ← isCompat_apply, toFun_sum_X_tmul, map_finsuppSum]
  refine Finsupp.sum_congr fun k _ ↦ ?_
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]

/-- Change of variables for coefficients: if the generic combination of `m'` is obtained from
`∑ⱼ sⱼ ⊗ mⱼ` for polynomials `sⱼ`, then each coefficient of `f` at `m'` is a combination of the
coefficients of `f` at `m`. -/
theorem coeff_eq_sum_of_sum_tmul_eq {κ : Type*} [Fintype κ] (f : M →ₚₗ[R] N) (m : ι → M)
    (s : ι → MvPolynomial κ R) (m' : κ → M)
    (h : ∑ j, s j ⊗ₜ[R] m j = ∑ i, X i ⊗ₜ[R] m' i) (k : κ →₀ ℕ) :
    coeff R N m' f k =
      (coeff R N m f).sum fun l n ↦ (∏ j, s j ^ l j).coeff k • n := by
  rw [coeff_apply, ← h, toFun_sum_tmul_eq_coeff_sum, map_finsuppSum, map_finsuppSum]
  simp

/-- A polynomial law is determined by its coefficients on families indexed by `Fin n`. -/
theorem ext_coeff {f g : M →ₚₗ[R] N}
    (h : ∀ (n : ℕ) (m : Fin n → M), coeff R N m f = coeff R N m g) : f = g := by
  ext S _ _ x
  rw [toFun'_eq_toFun, toFun'_eq_toFun]
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  rw [toFun_sum_tmul_eq_coeff_sum, toFun_sum_tmul_eq_coeff_sum, h]

/-- A law homogeneous of degree `d` has no coefficients outside total degree `d`. -/
theorem IsHomogeneousOfDegree.coeff_eq_zero {d : ℕ} {f : M →ₚₗ[R] N}
    (hf : f.IsHomogeneousOfDegree d) (m : ι → M) {k : ι →₀ ℕ} (hk : ∑ j, k j ≠ d) :
    coeff R N m f k = 0 := by
  classical
  -- Compare the coefficients of `Y ^ |k| Xᵏ` on both sides of `f (Y • x) = Y ^ d • f x`, over
  -- the polynomial ring `R[Xⱼ][Y]`, for `x = ∑ⱼ Xⱼ ⊗ mⱼ`.
  let Φ : Polynomial (MvPolynomial ι R) ⊗[R] N →ₗ[R] N :=
    TensorProduct.lid R N ∘ₗ ((lcoeff R k).restrictScalars R ∘ₗ
      (Polynomial.lcoeff (MvPolynomial ι R) (∑ j, k j)).restrictScalars R).rTensor N
  have hΦ (a : ι →₀ ℕ) (e : ℕ) (b : N) :
      Φ ((Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ e) ⊗ₜ[R] b) =
        if a = k ∧ ∑ j, k j = e then b else 0 := by
    rw [show ∏ j, (X j : MvPolynomial ι R) ^ a j = monomial a 1 by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]]
    simp only [Φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply,
      Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp_all
  have hx := congrArg Φ (hf.toFun_smul (Polynomial.X : Polynomial (MvPolynomial ι R))
    (∑ j, Polynomial.C (X j) ⊗ₜ[R] m j))
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul,
    toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum, map_finsuppSum] at hx
  have hL (a : ι →₀ ℕ) : ∏ j, (Polynomial.X * Polynomial.C (X j : MvPolynomial ι R)) ^ a j =
      Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ ∑ j, a j := by
    rw [Finset.prod_congr rfl fun j _ ↦ mul_pow _ _ (a j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, mul_comm, map_prod]
    simp only [map_pow]
  have hR (a : ι →₀ ℕ) : Polynomial.X ^ d * ∏ j, Polynomial.C (X j : MvPolynomial ι R) ^ a j =
      Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ d := by
    rw [mul_comm, map_prod]
    simp only [map_pow]
  simp only [hL, hR, hΦ] at hx
  simp only [ite_and, hk, ite_false, ite_self] at hx
  simpa using hx

end Coeff

end PolynomialLaw
