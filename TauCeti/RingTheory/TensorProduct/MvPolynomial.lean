/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

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

The cokernel of finitely many relations over `R[X_σ]`, with coefficients extended to `A`, is the
base change along `R → A` of the cokernel of the original relations.

## Main declarations

* `MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow`: the binomial expansion of
  `(u - a v) ^ i` on the tensor side.
* `MvPolynomial.ext_lid_rTensor_lcoeff`: elements of `R[X_σ] ⊗[R] N` with the same coefficients
  are equal.
* `MvPolynomial.exists_isBaseChange_quotient_range_linearCombination`: taking the cokernel of
  finitely many relations over a polynomial ring commutes with extending the coefficients.
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

section QuotientRange

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Taking the cokernel of finitely many relations over a polynomial ring commutes with extending
the coefficients: if the relations `v` over `MvPolynomial σ A` are the images of relations `w`
over `MvPolynomial σ R`, then the cokernel of `v` is the base change along `R → A` of the
cokernel of `w`. -/
theorem exists_isBaseChange_quotient_range_linearCombination {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {σ ι κ : Type*} [Fintype ι] [Finite κ] (w : ι → κ → MvPolynomial σ R)
    (v : ι → κ → MvPolynomial σ A)
    (hw : ∀ i k, MvPolynomial.map (algebraMap R A) (w i k) = v i k) :
    ∃ h : ((κ → MvPolynomial σ R) ⧸
        LinearMap.range (Fintype.linearCombination (MvPolynomial σ R) w)) →ₗ[R]
      ((κ → MvPolynomial σ A) ⧸ LinearMap.range (Fintype.linearCombination (MvPolynomial σ A) v)),
      IsBaseChange A h := by
  let P₀ := MvPolynomial σ R
  let P := MvPolynomial σ A
  let f₀ := Fintype.linearCombination P₀ w
  let f₁ := Fintype.linearCombination P v
  let h₁ : (ι → P₀) →ₗ[R] (ι → P) := (IsScalarTower.toAlgHom R P₀ P).toLinearMap.compLeft ι
  let h₂ : (κ → P₀) →ₗ[R] (κ → P) := (IsScalarTower.toAlgHom R P₀ P).toLinearMap.compLeft κ
  have comm₁ : h₂ ∘ₗ f₀.restrictScalars R = (f₁.restrictScalars R) ∘ₗ h₁ := by
    refine LinearMap.ext fun c ↦ funext fun k ↦ ?_
    simp [h₁, h₂, f₀, f₁, P₀, P, Fintype.linearCombination_apply, Algebra.smul_def, hw]
  have hle : (LinearMap.range f₀).restrictScalars R ≤
      LinearMap.ker ((LinearMap.range f₁).mkQ.restrictScalars R ∘ₗ h₂) := by
    rintro _ ⟨c, rfl⟩
    have := congr($comm₁ c)
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply] at this
    simp [this]
  let h₃ : (κ → P₀) ⧸ LinearMap.range f₀ →ₗ[R] (κ → P) ⧸ LinearMap.range f₁ :=
    ((LinearMap.range f₀).restrictScalars R).liftQ _ hle ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range f₀)).symm.toLinearMap
  have comm₂ : h₃ ∘ₗ (LinearMap.range f₀).mkQ.restrictScalars R =
      (((LinearMap.range f₁).mkQ.restrictScalars A).restrictScalars R) ∘ₗ h₂ :=
    LinearMap.ext fun x ↦
      Submodule.liftQ_apply ((LinearMap.range f₀).restrictScalars R)
        ((LinearMap.range f₁).mkQ.restrictScalars R ∘ₗ h₂) (h := hle) x
  have hb₁ : IsBaseChange A h₁ := IsBaseChange.finitePow ι Algebra.IsPushout.out
  have hb₂ : IsBaseChange A h₂ := IsBaseChange.finitePow κ Algebra.IsPushout.out
  have e₀ : Function.Exact (f₀.restrictScalars R) ((LinearMap.range f₀).mkQ.restrictScalars R) :=
    LinearMap.exact_map_mkQ_range f₀
  have s₀ : Function.Surjective ((LinearMap.range f₀).mkQ.restrictScalars R) :=
    Submodule.mkQ_surjective (LinearMap.range f₀)
  have e₁ : Function.Exact (f₁.restrictScalars A) ((LinearMap.range f₁).mkQ.restrictScalars A) :=
    LinearMap.exact_map_mkQ_range f₁
  have s₁ : Function.Surjective ((LinearMap.range f₁).mkQ.restrictScalars A) :=
    Submodule.mkQ_surjective (LinearMap.range f₁)
  exact ⟨h₃, IsBaseChange.of_right_exact A h₁ h₂ h₃
    (f := f₀.restrictScalars R) (g := (LinearMap.range f₀).mkQ.restrictScalars R)
    (f' := f₁.restrictScalars A) (g' := (LinearMap.range f₁).mkQ.restrictScalars A)
    comm₁ comm₂ hb₁ hb₂ e₀ s₀ e₁ s₁⟩

end QuotientRange

end MvPolynomial
