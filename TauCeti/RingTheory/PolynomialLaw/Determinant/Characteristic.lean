/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import TauCeti.LinearAlgebra.TensorProduct.Tower
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Characteristic polynomial laws

The characteristic coefficients of a determinant are polynomial laws on its algebra.
Evaluating the characteristic polynomial at its argument gives a homogeneous law with values
in the algebra itself. For a finite family `r : ι → R`, its mixed coefficients
are `PolynomialLaw.coeff A R r D.charpolyLaw`. These are the coefficients of
`χ_D(∑ j, Xⱼ rⱼ)`, and they provide the relations for Cayley–Hamilton quotients.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.10](https://arxiv.org/abs/0809.0415)
-/

public noncomputable section

open TensorProduct Polynomial

namespace TauCeti.Determinant

universe u

section CommSemiring

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)

section Coefficients

variable {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra A S] [Algebra A T]

private def atParameter (x : S ⊗[A] R) : S[X] ⊗[A] R :=
  (X : S[X]) • (Polynomial.CAlgHom (R := A) (A := S)).toLinearMap.rTensor R x + 1

private theorem map_atParameter (f : S →ₐ[A] T) (x : S ⊗[A] R) :
    (Polynomial.mapAlgHom f).toLinearMap.rTensor R (atParameter x) =
      atParameter (f.toLinearMap.rTensor R x) := by
  have h : (Polynomial.mapAlgHom f).comp Polynomial.CAlgHom = Polynomial.CAlgHom.comp f :=
    AlgHom.ext fun s ↦ by simp
  simp only [atParameter, map_add, AlgHom.rTensor_toLinearMap_apply_smul, Polynomial.coe_mapAlgHom,
    Polynomial.map_X]
  rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
  simp [← AlgHom.comp_toLinearMap, h, AlgHom.rTensor_toLinearMap_apply]

private def parameterCoeff (i : ℕ) : S[X] ⊗[A] A →ₗ[A] S ⊗[A] A :=
  ((Polynomial.lcoeff S i).restrictScalars A).rTensor A

private theorem parameterCoeff_map (f : S →ₐ[A] T) (i : ℕ) (y : S[X] ⊗[A] A) :
    parameterCoeff i ((Polynomial.mapAlgHom f).toLinearMap.rTensor A y) =
      f.toLinearMap.rTensor A (parameterCoeff i y) := by
  rw [parameterCoeff, parameterCoeff, ← LinearMap.rTensor_comp_apply,
    ← LinearMap.rTensor_comp_apply]
  have h : ((Polynomial.lcoeff T i).restrictScalars A).comp (Polynomial.mapAlgHom f).toLinearMap =
      f.toLinearMap.comp ((Polynomial.lcoeff S i).restrictScalars A) :=
    LinearMap.ext fun p ↦ Polynomial.coeff_mapAlgHom_apply f p i
  rw [h]

/-- The characteristic coefficient `Λᵢ` as a polynomial law. At a commutative
`A`-algebra `S` and `x : S ⊗[A] R` it takes the coefficient of `X ^ i` in
`D(1 + X x)` over `S[X]`. -/
def charCoeffLaw (i : ℕ) : R →ₚₗ[A] A where
  toFun' S _ _ x := parameterCoeff i (D.toLaw.toFun S[X] (atParameter x))
  isCompat' f := funext fun x ↦ by
    simp only [Function.comp_apply]
    rw [← parameterCoeff_map, PolynomialLaw.isCompat_apply, map_atParameter]

private theorem charCoeffLaw_toFun (i : ℕ) (x : S ⊗[A] R) :
    (D.charCoeffLaw i).toFun S x = parameterCoeff i (D.toLaw.toFun S[X] (atParameter x)) := by
  obtain ⟨n, f, y, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact (parameterCoeff_map f i _).symm.trans (by
    rw [PolynomialLaw.isCompat_apply, map_atParameter])

/-- Over any commutative coefficient algebra, the law `Λᵢ` is computed by extracting
a coefficient from the determinant of `1 + X x`. -/
theorem rid_charCoeffLaw_toFun (i : ℕ) (x : S ⊗[A] R) :
    Algebra.TensorProduct.rid A S S ((D.charCoeffLaw i).toFun S x) =
      (Algebra.TensorProduct.rid A S[X] S[X] (D.toLaw.toFun S[X]
        ((X : S[X]) • (Polynomial.CAlgHom (R := A) (A := S)).toLinearMap.rTensor R x + 1))).coeff
        i := by
  rw [charCoeffLaw_toFun D i, atParameter]
  generalize D.toLaw.toFun S[X]
    ((X : S[X]) • (Polynomial.CAlgHom (R := A) (A := S)).toLinearMap.rTensor R x + 1) = y
  induction y using TensorProduct.inductionOn with
  | tmul p a => simp [parameterCoeff]
  | add y z hy hz => simp [hy, hz]

/-- On the original algebra, the coefficient law agrees with the pointwise
characteristic coefficient. -/
@[simp]
theorem ground_charCoeffLaw (i : ℕ) (x : R) : (D.charCoeffLaw i).ground x = D.charCoeff i x := by
  rw [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, charCoeffLaw_toFun]
  simp only [atParameter, LinearMap.rTensor_tmul, smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.one_def, D.toFun_tmul_add_tmul_one, one_pow,
    parameterCoeff, map_sum, TensorProduct.lid_tmul, Polynomial.lcoeff_apply,
    LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply]
  by_cases hi : i ≤ d
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (by omega))]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
  · rw [D.charCoeff_eq_zero (by omega)]
    exact Finset.sum_eq_zero fun j hj ↦ by
      have hji : j ≠ i := by simp at hj; omega
      simp [Ne.symm hji]

private def rescaleParameter (s : S) : S[X] →ₐ[A] S[X] :=
  Polynomial.eval₂AlgHom Polynomial.CAlgHom (C s * X) (fun _ ↦ Commute.all _ _)

@[simp]
private theorem rescaleParameter_C (s b : S) :
    rescaleParameter (A := A) s (C b) = C b := by
  simp [rescaleParameter]

@[simp]
private theorem rescaleParameter_X (s : S) :
    rescaleParameter (A := A) s X = C s * X := by
  simp [rescaleParameter]

private theorem coeff_rescaleParameter (s : S) (p : S[X]) (i : ℕ) :
    (rescaleParameter (A := A) s p).coeff i = s ^ i * p.coeff i := by
  have h : rescaleParameter (A := A) s p = p.comp (C s * X) := (rfl)
  rw [h, Polynomial.comp_C_mul_X_coeff, mul_comm]

private theorem rescaleParameter_atParameter (s : S) (x : S ⊗[A] R) :
    (rescaleParameter s).toLinearMap.rTensor R (atParameter x) = atParameter (s • x) := by
  have h : (rescaleParameter (A := A) s).comp Polynomial.CAlgHom = Polynomial.CAlgHom :=
    AlgHom.ext fun b ↦ by simp
  simp only [atParameter, map_add, AlgHom.rTensor_toLinearMap_apply_smul, rescaleParameter_X]
  rw [← LinearMap.rTensor_comp_apply]
  rw [← AlgHom.comp_toLinearMap, h, CAlgHom_apply, smul_smul, mul_comm (C s)]
  simp only [AlgHom.rTensor_toLinearMap_apply, _root_.map_one]

private theorem parameterCoeff_rescale (s : S) (i : ℕ) (y : S[X] ⊗[A] A) :
    parameterCoeff i ((rescaleParameter s).toLinearMap.rTensor A y) =
      s ^ i • parameterCoeff i y := by
  induction y using TensorProduct.inductionOn with
  | tmul p a => simp [parameterCoeff, coeff_rescaleParameter, smul_tmul', smul_eq_mul]
  | add p q hp hq => simp [hp, hq, smul_add]

/-- The `i`-th characteristic coefficient law is homogeneous of degree `i`. -/
theorem isHomogeneousOfDegree_charCoeffLaw (i : ℕ) :
    (D.charCoeffLaw i).IsHomogeneousOfDegree i := by
  apply PolynomialLaw.isHomogeneousOfDegree_iff.mpr
  intro S _ _ s x
  simp only [PolynomialLaw.toFun'_eq_toFun, charCoeffLaw_toFun]
  rw [← rescaleParameter_atParameter, ← PolynomialLaw.isCompat_apply, parameterCoeff_rescale]

/-- The zeroth characteristic coefficient is the constant law with value `1`. -/
@[simp]
theorem charCoeffLaw_zero_toFun (x : S ⊗[A] R) : (D.charCoeffLaw 0).toFun S x = 1 := by
  have h := (D.isHomogeneousOfDegree_charCoeffLaw 0).toFun_smul (0 : S) x
  rw [zero_smul, pow_zero, one_smul] at h
  rw [← h, charCoeffLaw_toFun]
  simp [atParameter, Algebra.TensorProduct.one_def, parameterCoeff]

/-- The first characteristic coefficient law is the polynomial law of the trace. -/
@[simp]
theorem charCoeffLaw_one : D.charCoeffLaw 1 = D.trace.toPolynomialLaw := by
  let h := D.isHomogeneousOfDegree_charCoeffLaw 1
  rw [← h.toPolynomialLaw_toLinearMap]
  congr 1
  ext x
  rw [h.coe_toLinearMap, ground_charCoeffLaw, trace_apply]

end Coefficients

end CommSemiring

section CommRing

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)
variable {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra A S] [Algebra A T]

private def charpolyLawValue (x : S ⊗[A] R) : S ⊗[A] R :=
  ∑ i ∈ Finset.range (d + 1),
    ((-1 : A) ^ i) •
      (Algebra.TensorProduct.rid A S S ((D.charCoeffLaw i).toFun S x) • x ^ (d - i))

private theorem map_charpolyLawValue (f : S →ₐ[A] T) (x : S ⊗[A] R) :
    f.toLinearMap.rTensor R (D.charpolyLawValue x) =
      D.charpolyLawValue (f.toLinearMap.rTensor R x) := by
  have hrid (y : S ⊗[A] A) :
      f (Algebra.TensorProduct.rid A S S y) =
        Algebra.TensorProduct.rid A T T (f.toLinearMap.rTensor A y) := by
    induction y using TensorProduct.inductionOn with
    | tmul s a => simp [Algebra.smul_def]
    | add y z hy hz => simp [hy, hz]
  simp only [charpolyLawValue, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.map_smul, AlgHom.rTensor_toLinearMap_apply_smul, hrid, PolynomialLaw.isCompat_apply]
  simp [AlgHom.rTensor_toLinearMap_apply]

/-- The characteristic polynomial law `x ↦ χ_D(x, x)`. Its value over a commutative
coefficient algebra uses the characteristic coefficients formed over that algebra. -/
def charpolyLaw : R →ₚₗ[A] R where
  toFun' _ _ _ x := D.charpolyLawValue x
  isCompat' f := funext (D.map_charpolyLawValue f)

/-- The characteristic law over any commutative coefficient algebra, expressed using
the scalar-extended characteristic coefficient laws. -/
theorem charpolyLaw_toFun (x : S ⊗[A] R) :
    D.charpolyLaw.toFun S x = ∑ i ∈ Finset.range (d + 1),
      ((-1 : A) ^ i) •
        (Algebra.TensorProduct.rid A S S ((D.charCoeffLaw i).toFun S x) • x ^ (d - i)) := by
  obtain ⟨n, f, y, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact D.map_charpolyLawValue f y

/-- The value of the characteristic law on the original algebra is the characteristic
polynomial evaluated at its argument. -/
@[simp]
theorem ground_charpolyLaw (x : R) : D.charpolyLaw.ground x = aeval x (D.charpoly x) := by
  rw [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, charpolyLaw_toFun,
    D.charpoly_eq_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← PolynomialLaw.one_tmul_ground, ground_charCoeffLaw, Algebra.TensorProduct.rid_tmul,
    smul_eq_mul, mul_one, ← Algebra.TensorProduct.includeRight_apply, ← map_pow]
  simp only [Algebra.TensorProduct.includeRight_apply, _root_.map_smul, lid_tmul, one_smul]
  simp only [_root_.map_mul, map_pow, map_neg, _root_.map_one, aeval_C, aeval_X,
    Algebra.smul_def, mul_assoc]
  have hneg : (-1 : A[X]) = C (-1 : A) := by rw [C_neg, C_1]
  rw [hneg, aeval_C]

/-- The characteristic polynomial law of a degree-`d` determinant is homogeneous of
degree `d`. -/
theorem isHomogeneousOfDegree_charpolyLaw : D.charpolyLaw.IsHomogeneousOfDegree d := by
  apply PolynomialLaw.isHomogeneousOfDegree_iff.mpr
  intro S _ _ s x
  simp only [PolynomialLaw.toFun'_eq_toFun, charpolyLaw_toFun, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hid : i + (d - i) = d := by simp at hi; omega
  rw [(D.isHomogeneousOfDegree_charCoeffLaw i).toFun_smul, _root_.map_smul, smul_pow]
  rw [smul_comm (s ^ d) ((-1 : A) ^ i)]
  simp only [smul_eq_mul, smul_smul]
  rw [mul_right_comm, ← pow_add, hid]

end CommRing

end TauCeti.Determinant
