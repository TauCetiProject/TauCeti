/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Extension of scalars of multivariate polynomials

Under the identification `A ⊗[R] R[X_σ] ≃ A[X_σ]` of `MvPolynomial.algebraTensorAlgEquiv`, the
power `(u - a v) ^ i` of polynomials `u, v` over `R` and a scalar `a` of `A` is the image of the
tensor `∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. Contracting the `A`-leg of this tensor against a
linear functional gives a weighted sum of the binomial terms. For `A = R[t]` and `a = t`,
coefficient functionals extract individual terms: the coefficient of `tⁿ` in `(u - t v) ^ i`
is `(-1)ⁿ (i choose n) uⁱ⁻ⁿ vⁿ`.

An element of `R[X_σ] ⊗[R] N` is determined by its coefficients, the images of the coefficient
functionals `MvPolynomial.lcoeff R e` on the polynomial leg.

Evaluating `S[X_ι]` at `1 ⊗ₜ yᵢ` inside `S ⊗[R] A` factors as `(algebraTensorAlgEquiv R S).symm`
followed by `lTensor S (aeval y)`
(`MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm`,
`MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm`). Consequently, module-finiteness
and integrality of `MvPolynomial.aeval y` are preserved under arbitrary base change `S / R`
(`MvPolynomial.finite_aeval_one_tmul`, `MvPolynomial.isIntegral_aeval_one_tmul`).

## Main declarations

* `MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow`: the binomial expansion of
  `(u - a v) ^ i` on the tensor side.
* `MvPolynomial.ext_lid_rTensor_lcoeff`: elements of `R[X_σ] ⊗[R] N` with the same coefficients
  are equal.
* `MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm`,
  `MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm`: `aeval (1 ⊗ₜ y ·)` factors
  through `MvPolynomial.algebraTensorAlgEquiv` and `Algebra.TensorProduct.lTensor`.
* `MvPolynomial.finite_aeval_one_tmul`, `MvPolynomial.isIntegral_aeval_one_tmul`: scalar extension
  preserves module-finiteness and integrality of `MvPolynomial.aeval`.
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

section BaseChange

section CommSemiring

variable {ι R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Evaluating polynomials over `S` at `1 ⊗ₜ[R] y i` in `S ⊗[R] A` factors as the `S`-algebra
isomorphism `(algebraTensorAlgEquiv R S).symm` followed by `lTensor S (aeval y)`. -/
theorem aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm {S : Type*} [CommSemiring S]
    [Algebra R S] (y : ι → A) :
    aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) =
      (Algebra.TensorProduct.lTensor S (aeval (R := R) y)).comp
        (algebraTensorAlgEquiv R S).symm.toAlgHom :=
  algHom_ext fun i ↦ by simp

/-- Evaluating a polynomial over `S` at `1 ⊗ₜ[R] y i` in `S ⊗[R] A` agrees with transporting along
`(algebraTensorAlgEquiv R S).symm` and applying `id_S ⊗ aeval y`. -/
theorem aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm {S : Type*} [CommSemiring S]
    [Algebra R S] (y : ι → A) (p : MvPolynomial ι S) :
    aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) p =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)
        ((algebraTensorAlgEquiv R S).symm p) := by
  have hl : (Algebra.TensorProduct.lTensor (S := S) S (aeval (R := R) y)).restrictScalars R =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y) := by
    ext <;> simp
  rw [aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, ← AlgHom.restrictScalars_apply R, hl]

private theorem aeval_one_tmul_toRingHom {S : Type*} [CommSemiring S] [Algebra R S] (y : ι → A) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
        (algebraTensorAlgEquiv R S).symm.toRingHom :=
  RingHom.ext (aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm y)

end CommSemiring

section CommRing

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Module-finiteness of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra
`S`. -/
theorem finite_aeval_one_tmul (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hfin : (aeval (R := R) y).Finite) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).Finite := by
  rw [AlgHom.Finite, aeval_one_tmul_toRingHom]
  exact (RingHom.Finite.tensorProductMap (AlgHom.Finite.id R S) hfin).comp
    (RingHom.Finite.of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective)

/-- Integrality of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra `S`. -/
theorem isIntegral_aeval_one_tmul (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hint : (aeval (R := R) y).toRingHom.IsIntegral) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom.IsIntegral := by
  rw [aeval_one_tmul_toRingHom]
  refine RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective) ?_
  intro z
  refine z.inductionOn (fun s a ↦ ?_) (fun u v hu hv ↦ RingHom.IsIntegralElem.add _ hu hv)
  have hcomp :
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom.comp
        (aeval (R := R) y).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R) (A := S) (B := MvPolynomial ι R)).toRingHom := by
    simp only [AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom,
      Algebra.TensorProduct.map_comp_includeRight]
  have ha : (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.IsIntegralElem
      ((1 : S) ⊗ₜ[R] a) := by
    have ha' := (hint a).map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom
    rw [hcomp] at ha'
    simpa using ha'.of_comp
  have hs : (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.IsIntegralElem
      (s ⊗ₜ[R] (1 : A)) := by
    simpa using RingHom.isIntegralElem_map
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom
      (x := s ⊗ₜ[R] (1 : MvPolynomial ι R))
  simpa [Algebra.TensorProduct.tmul_mul_tmul] using RingHom.IsIntegralElem.mul _ hs ha

end CommRing

end BaseChange

end MvPolynomial
