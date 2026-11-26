/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Alternating.ModIdeal

/-!
# Full polarization and the matrix of a quadratic form

The matrix `Q.toMatrix b` uses the half-polarization, so its diagonal coefficients are the
quadratic coefficients. The matrix of the full polarization is twice this matrix. Its determinant
therefore differs from the quadratic discriminant by `2` to the dimension, including dimension
zero. These formulas make the convention explicit when changing between bilinear and quadratic
Gram determinants.

Without `2` invertible, a quadratic form `q` is still `x ↦ xᵀ M x` in the coordinates of a basis
`b` indexed by a linearly ordered type, for its upper triangular *coefficient matrix* `M`
(`QuadraticForm.coefficientMatrix`): the diagonal entries are the values `q(bᵢ)`, the entries above
the diagonal are the polar values `q(bᵢ + bⱼ) - q(bᵢ) - q(bⱼ)`, and the entries below it are `0`
(`QuadraticForm.coefficientMatrix_apply`). The matrix of the full polarization is then `M + Mᵀ`
(`QuadraticForm.toMatrix_polarBilin_eq_coefficientMatrix_add_transpose`). For a form on `R^ι`,
reading `M` in an `R`-algebra `A` gives the form `q_A` on `A^ι` with the same coefficients
(`QuadraticForm.baseChangeForm`). Mathlib's `QuadraticForm.baseChange` instead lives on
`A ⊗[R] R^ι` and assumes `2` invertible.
A matrix `P` with `q'(P x) = q(x)` over `R` satisfies `q'_A(P x) = q_A(x)` over every `A`
(`QuadraticForm.baseChangeForm_map_mulVec`): the matrix `Pᵀ M' P - M` has vanishing quadratic
expression, so it is alternating (`Matrix.isAltMod_bot_iff`) and stays alternating over `A`. This
holds in characteristic two, where `q` is not determined by its polar form.

## Main declarations

* `QuadraticForm.toMatrix_polarBilin` and `QuadraticForm.det_toMatrix_polarBilin`: the full
  polar matrix and its determinant.
* `QuadraticForm.coefficientMatrix` and `QuadraticForm.coefficientMatrix_apply`: the upper
  triangular coefficient matrix of a quadratic form in an ordered basis.
* `QuadraticForm.toMatrix_polarBilin_eq_coefficientMatrix_add_transpose`: the full polar matrix is
  `M + Mᵀ`, with no assumption on `2`.
* `QuadraticForm.baseChangeForm`, `QuadraticForm.baseChangeForm_apply` and
  `QuadraticForm.baseChangeForm_self`: the form with the same coefficients over an `R`-algebra.
* `QuadraticForm.baseChangeForm_map_mulVec`: a matrix carrying `q` to `q'` over `R` carries `q_A`
  to `q'_A` over every `R`-algebra `A`.
* `QuadraticForm.baseChangeForm_add` and `QuadraticForm.baseChangeForm_proj`: `q ↦ q_A` is
  additive and sends the coordinate product `xᵢ xⱼ` to `xᵢ xⱼ`.
* `QuadraticForm.coefficientMatrix_baseChangeForm`: the coefficient matrix of `q_A` is that of `q`
  read in `A`.
-/

public section

namespace QuadraticForm

variable {R V ι : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

/-- The full polar matrix is twice the quadratic Gram matrix. -/
theorem toMatrix_polarBilin (Q : QuadraticForm R V) (b : Module.Basis ι R V) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = (2 : R) • Q.toMatrix b := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.smul_apply, QuadraticForm.toMatrix,
    LinearMap.toMatrix₂_apply]
  have h := congrArg (fun B : LinearMap.BilinForm R V => B (b i) (b j))
    (QuadraticMap.two_nsmul_associated R Q)
  simpa only [LinearMap.add_apply, two_nsmul, Matrix.smul_apply, smul_eq_mul, two_mul] using h.symm

/-- The determinant of the full polar matrix is `2^dim` times the quadratic discriminant. -/
theorem det_toMatrix_polarBilin (Q : QuadraticForm R V) (b : Module.Basis ι R V) :
    (LinearMap.BilinForm.toMatrix b Q.polarBilin).det =
      (2 : R) ^ Fintype.card ι * Q.discr b := by
  rw [toMatrix_polarBilin, Matrix.det_smul, QuadraticForm.discr]

end QuadraticForm

open scoped Matrix

namespace QuadraticForm

section Coefficients

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Fintype ι] [LinearOrder ι]

/-- The **coefficient matrix** of a quadratic form `q` in a basis `b` indexed by a linearly ordered
type: the upper triangular matrix `M` with `q(Σ xᵢ bᵢ) = xᵀ M x`, from Mathlib's
`QuadraticMap.toBilin`. -/
noncomputable def coefficientMatrix (q : QuadraticForm R V) (b : Module.Basis ι R V) :
    Matrix ι ι R :=
  LinearMap.toMatrix₂ b b (q.toBilin b)

/-- The entries of the coefficient matrix: `q(bᵢ)` on the diagonal, the polar value
`q(bᵢ + bⱼ) - q(bᵢ) - q(bⱼ)` above it and `0` below it. -/
theorem coefficientMatrix_apply (q : QuadraticForm R V) (b : Module.Basis ι R V) (i j : ι) :
    coefficientMatrix q b i j =
      if i = j then q (b i) else if i < j then QuadraticMap.polar q (b i) (b j) else 0 := by
  rw [coefficientMatrix, LinearMap.toMatrix₂_apply, QuadraticMap.toBilin_apply]

/-- The coefficient matrix is additive in the form. -/
@[simp]
theorem coefficientMatrix_add (q q' : QuadraticForm R V) (b : Module.Basis ι R V) :
    coefficientMatrix (q + q') b = coefficientMatrix q b + coefficientMatrix q' b := by
  ext k l
  simp only [coefficientMatrix_apply, Matrix.add_apply]
  split_ifs <;> simp [QuadraticMap.polar_add]

/-- The coefficient matrix of the coordinate product `xᵢ xⱼ` has a single entry `1`, in position
`(min i j, max i j)`. -/
@[simp]
theorem coefficientMatrix_proj (i j : ι) :
    coefficientMatrix (QuadraticMap.proj (R := R) i j) (Pi.basisFun R ι) =
      Matrix.single (min i j) (max i j) 1 := by
  ext k l
  simp only [coefficientMatrix_apply, QuadraticMap.polar, QuadraticMap.proj_apply,
    Pi.basisFun_apply, Pi.add_apply, Pi.single_apply, Matrix.single_apply]
  rcases le_total i j with h | h <;> simp only [min_eq_left, min_eq_right, max_eq_left,
    max_eq_right, h] <;> split_ifs <;> grind

/-- Without any assumption on `2`, the matrix of the full polarization of `q` is `M + Mᵀ`, for `M`
the coefficient matrix of `q`. -/
theorem toMatrix_polarBilin_eq_coefficientMatrix_add_transpose (q : QuadraticForm R V)
    (b : Module.Basis ι R V) :
    LinearMap.BilinForm.toMatrix b q.polarBilin =
      coefficientMatrix q b + (coefficientMatrix q b)ᵀ := by
  conv_lhs => rw [← QuadraticMap.toQuadraticMap_toBilin q b]
  ext i j
  simp only [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.BilinForm.toMatrix_apply,
    Matrix.add_apply, Matrix.transpose_apply, coefficientMatrix, LinearMap.toMatrix₂_apply,
    LinearMap.add_apply, LinearMap.flip_apply]

/-- The form `q_A` on `A^ι` with the same coefficients as a form `q` on `R^ι`: `x ↦ xᵀ M x` for
the coefficient matrix `M` of `q` in the standard basis, read in `A`. -/
noncomputable def baseChangeForm (q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] : QuadraticForm A (ι → A) :=
  Matrix.toQuadraticForm' ((coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A))

/-- The form `q_A` evaluates as `xᵀ M x`. -/
@[simp]
theorem baseChangeForm_apply (q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] (x : ι → A) :
    baseChangeForm q A x =
      x ⬝ᵥ ((coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A) *ᵥ x) := by
  rw [baseChangeForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- Over `R` itself, the form with the coefficients of `q` is `q`. -/
@[simp]
theorem baseChangeForm_self (q : QuadraticForm R (ι → R)) : baseChangeForm q R = q := by
  simp only [baseChangeForm, coefficientMatrix, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id, Matrix.toQuadraticForm', LinearMap.toMatrix₂_basisFun,
    Matrix.toLinearMap₂'_toMatrix', QuadraticMap.toQuadraticMap_toBilin]

/-- **A matrix carrying `q` to `q'` over `R` does so over every `R`-algebra.** If `q'(P x) = q(x)`
for every `x ∈ R^ι`, then `q'_A(P x) = q_A(x)` for every `x ∈ A^ι`, with `P` read in `A`. -/
theorem baseChangeForm_map_mulVec {κ : Type*} [Fintype κ] [LinearOrder κ]
    {q : QuadraticForm R (ι → R)} {q' : QuadraticForm R (κ → R)} {P : Matrix κ ι R}
    (hP : ∀ x, q' (P *ᵥ x) = q x) (A : Type*) [CommRing A] [Algebra R A] (x : ι → A) :
    baseChangeForm q' A (P.map (algebraMap R A) *ᵥ x) = baseChangeForm q A x := by
  set M := coefficientMatrix q (Pi.basisFun R ι)
  set M' := coefficientMatrix q' (Pi.basisFun R κ)
  have hR : Matrix.IsAltMod ⊥ (Pᵀ * M' * P - M) := by
    rw [Matrix.isAltMod_bot_iff]
    intro y
    have h1 := hP y
    rw [← baseChangeForm_self q', ← baseChangeForm_self q, baseChangeForm_apply,
      baseChangeForm_apply] at h1
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_transpose_mul_mul_mulVec, h1,
      sub_self]
  have hA := (Matrix.isAltMod_bot_iff _).mp
    (hR.map (algebraMap R A) (by rw [Ideal.map_bot])) x
  rw [Matrix.map_sub _ (map_sub (algebraMap R A)), Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.dotProduct_transpose_mul_mul_mulVec, sub_eq_zero] at hA
  rw [baseChangeForm_apply, baseChangeForm_apply]
  exact hA

/-- The form with the coefficients of `q + q'` is the sum of the forms with the coefficients of
`q` and of `q'`. -/
@[simp]
theorem baseChangeForm_add (q q' : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] : baseChangeForm (q + q') A = baseChangeForm q A + baseChangeForm q' A := by
  ext x
  simp [Matrix.map_add, Matrix.add_mulVec]

/-- The form with the coefficients of the coordinate product `xᵢ xⱼ` is again `xᵢ xⱼ`. -/
@[simp]
theorem baseChangeForm_proj (i j : ι) (A : Type*) [CommRing A] [Algebra R A] :
    baseChangeForm (QuadraticMap.proj (R := R) i j) A = QuadraticMap.proj (R := A) i j := by
  ext x
  rcases le_total i j with h | h <;>
    simp [h, Matrix.single_mulVec, dotProduct, Function.update_apply, mul_comm]

/-- **The coefficients of `q_A` are those of `q`.** The coefficient matrix of the form `q_A` on
`A^ι` with the coefficients of `q` is the coefficient matrix of `q` read in `A`, since the
coefficient matrix is upper triangular. -/
@[simp]
theorem coefficientMatrix_baseChangeForm (q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] :
    coefficientMatrix (baseChangeForm q A) (Pi.basisFun A ι) =
      (coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A) := by
  classical
  have hlow : ∀ i j, j < i → coefficientMatrix q (Pi.basisFun R ι) i j = 0 :=
    fun i j hji ↦ by simp [coefficientMatrix_apply, ne_of_gt hji, not_lt.mpr hji.le]
  have hsingle (i j : ι) : (Pi.single i 1 : ι → A) ⬝ᵥ
      ((coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A) *ᵥ Pi.single j 1) =
        algebraMap R A (coefficientMatrix q (Pi.basisFun R ι) i j) := by
    simp
  ext i j
  rw [coefficientMatrix_apply]
  split_ifs with hij hlt
  · subst hij
    rw [Pi.basisFun_apply, baseChangeForm_apply, hsingle, Matrix.map_apply]
  · simp only [QuadraticMap.polar, Pi.basisFun_apply, baseChangeForm_apply, Matrix.mulVec_add,
      dotProduct_add, add_dotProduct, hsingle, hlow j i hlt, map_zero, Matrix.map_apply]
    ring
  · rw [Matrix.map_apply, hlow i j (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)), map_zero]

end Coefficients

end QuadraticForm
