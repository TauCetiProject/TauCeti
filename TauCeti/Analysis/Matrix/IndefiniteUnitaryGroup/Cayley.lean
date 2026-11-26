/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Normed.Algebra.CayleyChart
public import TauCeti.LinearAlgebra.Matrix.Hermitian.Congruence
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Cayley
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.RingTheory.Complex
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Cayley coordinates on a complex unitary group and their logarithmic Jacobian

Let `A` be an invertible Hermitian complex matrix, for instance `J = diag(1, …, 1, -1, …, -1)`, and
`U(A) = Matrix.unitaryGroupOf A` the group of matrices `g` with `gᴴ A g = A`. Its Lie algebra is
`{X | Xᴴ A + A X = 0} = A⁻¹ 𝔲(n)`, where `𝔲(n)` is the real vector space of skew-Hermitian matrices,
so that the skew-Hermitian matrices are real coordinates on the Lie algebra of every `U(A)`. The
**Cayley chart** of `U(A)` is

`φ(S) = c(-A⁻¹ S / 2) = (1 + A⁻¹ S / 2) (1 - A⁻¹ S / 2)⁻¹`

on the skew-Hermitian `S` with `D(S) = 1 - A⁻¹ S / 2` invertible
(`Matrix.unitaryGroupOf.cayleyChart`), where `c` is the Cayley transform
`TauCeti.cayleyCoord 1`. It is a bijection onto the `g ∈ U(A)` with `1 + g` invertible
(`Matrix.unitaryGroupOf.cayleyChartEquiv`), with inverse `g ↦ -2 A c(g)`. At `S = 0` it is `1`, with
differential `T ↦ A⁻¹ T`: the identification of `𝔲(n)` with the Lie algebra of `U(A)`.

The differential of the chart at `S` is `T ↦ D⁻¹ A⁻¹ T D⁻¹`
(`Matrix.unitaryGroupOf.hasFDerivAt_cayleyChart`). Its **logarithmic derivative**
`T ↦ A φ(S)⁻¹ dφ_S(T) = φ(S)ᴴ A dφ_S(T)`, the left-invariant Maurer–Cartan form of `U(A)` pulled
back by the chart and read in the coordinates `𝔲(n)`, is the congruence `T ↦ D⁻ᴴ T D⁻¹` of the
skew-Hermitian matrices (`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`). Its
real determinant is `|det D(S)|^(-2 n)`
(`Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart`), equal to `1` at
`S = 0`. This determinant is the Jacobian through which a left Haar measure of `U(A)` is
written in Cayley coordinates against Lebesgue measure on `𝔲(n)`; no measure is constructed here.

Derivatives are taken for the Frobenius norm on matrices; matrix norms are only scoped instances.

## Main definitions

* `Matrix.unitaryGroupOf.cayleyChart A S`: the Cayley chart `(1 + A⁻¹ S / 2) (1 - A⁻¹ S / 2)⁻¹`.
* `Matrix.unitaryGroupOf.cayleyChartEquiv`: the chart as a bijection from the skew-Hermitian `S`
  with `1 - A⁻¹ S / 2` invertible onto the `g ∈ U(A)` with `1 + g` invertible.

## Main results

* `Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_cayleyChart`: the chart takes values in `U(A)`.
* `Matrix.unitaryGroupOf.hasFDerivAt_cayleyChart`: the differential of the chart.
* `Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`: the logarithmic derivative
  of the chart is the congruence by `D⁻ᴴ`.
* `Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart`: its determinant is
  `|det D|^(-2 n)`.

## Provenance

`Matrix.unitaryGroupOf.cayleyChart`, `Matrix.unitaryGroupOf.cayleyChartEquiv`,
`Matrix.unitaryGroupOf.hasFDerivAt_cayleyChart`,
`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart` and
`Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart` are adapted from
`New.cayleyDenom`, `New.cayleyChart`, `New.cayleyChartInv`, `New.cayleyChart_injOn`,
`New.cayleyChart_cayleyChartInv`, `New.logDerivU_cayleyChart` and
`New.abs_det_logDerivU_cayleyChart` (file `src/Lib/DiscreteSeries/Haar/CayleyChart.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where `A` is a
Hermitian involution, the chart is totalized by `2 D⁻¹ - 1`, and the Jacobian is the absolute
determinant in real coordinates of the skew-Hermitian matrices. The coordinate-free statement on
the real vector space of skew-Hermitian matrices, the exact determinant, the generalization to every
invertible Hermitian `A`, and the factorization through the Cayley transform
`TauCeti.cayleyCoord 1` are new here.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press, 1939, Chapter II, §10 (Cayley's
  rational parametrization).
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, §VIII.2 (left Haar
  measure in coordinates as the determinant of the Maurer–Cartan form).
-/

public section

open Complex TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace unitaryGroupOf

variable {A : Matrix n n ℂ} {S : skewAdjoint.submodule ℝ (Matrix n n ℂ)}

/-- The **Cayley chart** of the unitary group of `A`: the matrix
`c(-A⁻¹ S / 2) = (1 + A⁻¹ S / 2) (1 - A⁻¹ S / 2)⁻¹` attached to a skew-Hermitian matrix `S`. For
Hermitian `A` it preserves the form of `A` where `1 - A⁻¹ S / 2` is invertible
(`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_cayleyChart`); elsewhere its value is `0`. -/
noncomputable def cayleyChart (A : Matrix n n ℂ) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    Matrix n n ℂ :=
  cayleyCoord 1 (-((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))))

/-- The definition of the Cayley chart. -/
theorem cayleyChart_def (A : Matrix n n ℂ) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyChart A S = cayleyCoord 1 (-((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) :=
  (rfl)

/-- The Cayley chart is `(1 + A⁻¹ S / 2) (1 - A⁻¹ S / 2)⁻¹`. -/
theorem cayleyChart_eq (A : Matrix n n ℂ) (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    cayleyChart A S = (1 + (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) *
      (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ := by
  rw [cayleyChart_def, cayleyCoord_def, ← nonsing_inv_eq_ringInverse,
    sub_neg_eq_add, ← sub_eq_add_neg]

/-- The Cayley chart sends `0` to the identity. -/
@[simp]
theorem cayleyChart_zero (A : Matrix n n ℂ) : cayleyChart A 0 = 1 := by
  simp [cayleyChart]

/-- For Hermitian `A` and skew-Hermitian `S`, the matrix `-A⁻¹ S / 2` lies in the Lie algebra of
the unitary group of `A`: it is skew-adjoint for the form of `A`. -/
theorem star_neg_smul_inv_mul_mul_add (hA : A.IsHermitian)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    star (-((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) * A +
      A * -((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) = 0 := by
  have hS : star (S : Matrix n n ℂ) = -S := skewAdjoint.mem_iff.1 S.property
  have hA' : star A⁻¹ = A⁻¹ := by
    rw [star_eq_conjTranspose, conjTranspose_nonsing_inv, hA.eq]
  simp only [star_neg, star_smul, star_mul, hS, hA', Matrix.neg_mul, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, star_inv₀, star_ofNat]
  -- `S A⁻¹ A = A A⁻¹ S`: either `A` is invertible, or `A⁻¹ = 0`.
  by_cases hd : IsUnit A.det
  · simp [nonsing_inv_mul_cancel_right _ _ hd, mul_nonsing_inv_cancel_left _ _ hd]
  · simp [nonsing_inv_apply_not_isUnit A hd]

/-- **The Cayley chart takes values in the unitary group.** For Hermitian `A` and skew-Hermitian
`S` with `1 - A⁻¹ S / 2` invertible, `φ(S)ᴴ A φ(S) = A`. -/
theorem star_cayleyChart_mul_mul_cayleyChart (hA : A.IsHermitian)
    (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) :
    star (cayleyChart A S) * A * cayleyChart A S = A :=
  star_cayleyCoord_one_mul_mul_cayleyCoord_one (star_neg_smul_inv_mul_mul_add hA S)
    (by rwa [← sub_eq_add_neg])

/-- **The Cayley chart as a bijection.** For an invertible Hermitian `A`, the Cayley chart is a
bijection from the skew-Hermitian `S` with `1 - A⁻¹ S / 2` invertible onto the elements `g` of the
unitary group of `A` with `1 + g` invertible. Its inverse is `g ↦ -2 A c(g)`, where `c` is the
Cayley transform. -/
noncomputable def cayleyChartEquiv (hA : A.IsHermitian) (hA' : IsUnit A) :
    {S : skewAdjoint.submodule ℝ (Matrix n n ℂ) //
        IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))} ≃
      {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))} :=
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA'
  have key (X : Matrix n n ℂ) : (2 : ℂ)⁻¹ • (A⁻¹ * (-(2 : ℂ) • (A * X))) = -X := by
    rw [Matrix.mul_smul, smul_smul, nonsing_inv_mul_cancel_left _ _ hd]
    norm_num
  Equiv.trans (β := {X : Matrix n n ℂ // star X * A + A * X = 0 ∧ IsUnit (1 + X)})
    { toFun S := ⟨-((2 : ℂ)⁻¹ • (A⁻¹ * (S.val : Matrix n n ℂ))),
        star_neg_smul_inv_mul_mul_add hA S.val, by rw [← sub_eq_add_neg]; exact S.property⟩
      invFun X := ⟨⟨-(2 : ℂ) • (A * X.val), skewAdjoint.mem_iff.2 <| by
          rw [star_smul, star_mul, star_eq_conjTranspose A, hA.eq,
            eq_neg_of_add_eq_zero_left X.property.1]
          simp⟩, by rw [key, sub_neg_eq_add]; exact X.property.2⟩
      left_inv S := Subtype.ext <| Subtype.ext <| by
        simp [smul_smul, mul_nonsing_inv_cancel_left _ _ hd]
      right_inv X := Subtype.ext <| by simp only [key, neg_neg] }
    (cayleyEquiv hA' (by norm_num))

/-- The image of `S` under `Matrix.unitaryGroupOf.cayleyChartEquiv` is the Cayley chart at `S`. -/
@[simp]
theorem coe_cayleyChartEquiv_apply (hA : A.IsHermitian) (hA' : IsUnit A)
    (S : {S : skewAdjoint.submodule ℝ (Matrix n n ℂ) //
      IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))}) :
    (((cayleyChartEquiv hA hA' S).val : GL n ℂ) : Matrix n n ℂ) = cayleyChart A S.val :=
  coe_cayleyEquiv_apply _ _ _

/-- The inverse of `Matrix.unitaryGroupOf.cayleyChartEquiv` is `g ↦ -2 A c(g)`, where `c` is the
Cayley transform. -/
@[simp]
theorem coe_cayleyChartEquiv_symm_apply (hA : A.IsHermitian) (hA' : IsUnit A)
    (g : {g : unitaryGroupOf A // IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))}) :
    (((cayleyChartEquiv hA hA').symm g).val : Matrix n n ℂ) =
      -(2 : ℂ) • (A * cayleyCoord 1 ((g.val : GL n ℂ) : Matrix n n ℂ)) := by
  simp [cayleyChartEquiv]

section Calculus

open scoped Matrix.Norms.Frobenius

/-- **The derivative of the Cayley chart.** At a skew-Hermitian `S` with `D = 1 - A⁻¹ S / 2`
invertible, the Cayley chart has derivative `T ↦ D⁻¹ A⁻¹ T D⁻¹`. -/
theorem hasFDerivAt_cayleyChart (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) :
    HasFDerivAt (cayleyChart A)
      ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
        ((1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ * A⁻¹)
        (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹).comp
        (skewAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL :
          skewAdjoint.submodule ℝ (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ) S := by
  -- The chart is the Cayley transform composed with the linear map `Y : S ↦ -A⁻¹ S / 2`.
  let Y : skewAdjoint.submodule ℝ (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (-((2 : ℂ)⁻¹ • A⁻¹))).comp
      (skewAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL
  have hY (S' : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      Y S' = -((2 : ℂ)⁻¹ • (A⁻¹ * (S' : Matrix n n ℂ))) := by
    -- Frobenius and default matrix topology instances agree after unfolding, so the
    -- `_apply` lemmas of the composite do not fire.
    change -((2 : ℂ)⁻¹ • A⁻¹) * (S' : Matrix n n ℂ) = _
    rw [Matrix.neg_mul, Matrix.smul_mul]
  have h1 : IsUnit (1 + Y S) := by rwa [hY, ← sub_eq_add_neg]
  have hfun : cayleyChart A = cayleyCoord 1 ∘ Y :=
    funext fun S' ↦ by rw [Function.comp_apply, hY, cayleyChart_def]
  rw [hfun]
  refine ((hasFDerivAt_cayleyCoord_one (𝕜 := ℝ) h1).comp S Y.hasFDerivAt).congr_fderiv ?_
  ext T : 1
  -- The composite mixes Frobenius and default matrix topology instances, so the CLM `_apply`
  -- lemmas do not fire; unfolding and converting `Ring.inverse` states its value directly.
  simp only [← nonsing_inv_eq_ringInverse]
  change -(2 : ℝ) • ((1 + Y S)⁻¹ * Y T * (1 + Y S)⁻¹) = _ * (T : Matrix n n ℂ) * _
  rw [hY, hY, ← sub_eq_add_neg]
  simp only [Matrix.mul_neg, Matrix.neg_mul, smul_neg, neg_smul, neg_neg, Matrix.mul_smul,
    Matrix.smul_mul]
  rw [← Complex.coe_smul, smul_smul]
  norm_num [Matrix.mul_assoc]

/-- The Cayley chart is differentiable at every skew-Hermitian `S` with `1 - A⁻¹ S / 2`
invertible. -/
theorem differentiableAt_cayleyChart
    (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) :
    DifferentiableAt ℝ (cayleyChart A) S :=
  (hasFDerivAt_cayleyChart hS).differentiableAt

/-- The value of the derivative of the Cayley chart: with `D = 1 - A⁻¹ S / 2` invertible,
`dφ_S(T) = D⁻¹ A⁻¹ T D⁻¹`. -/
theorem fderiv_cayleyChart_apply (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))))
    (T : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    fderiv ℝ (cayleyChart A) S T =
      (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ * A⁻¹ * T *
        (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ := by
  -- `HasFDerivAt.fderiv` states `fderiv` with the instances of `HasFDerivAt`, which agree with
  -- those of the statement only up to unfolding, so it is applied by `exact`, not rewritten.
  exact (DFunLike.congr_fun (hasFDerivAt_cayleyChart hS).fderiv T).trans (rfl)

/-- At `0` the derivative of the Cayley chart is `T ↦ A⁻¹ T`: it identifies the skew-Hermitian
matrices with the Lie algebra `A⁻¹ 𝔲(n)` of the unitary group of `A`. -/
theorem fderiv_cayleyChart_zero_apply (T : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    fderiv ℝ (cayleyChart A) 0 T = A⁻¹ * T := by
  rw [fderiv_cayleyChart_apply (by simp)]
  simp

/-- **The logarithmic derivative of the Cayley chart.** For an invertible Hermitian `A` and a
skew-Hermitian `S` with `D = 1 - A⁻¹ S / 2` invertible, the pull-back
`T ↦ φ(S)ᴴ A dφ_S(T) = A φ(S)⁻¹ dφ_S(T)` of the Maurer–Cartan form of the unitary group of `A` by
the Cayley chart `φ` is the congruence `T ↦ D⁻ᴴ T D⁻¹`. -/
theorem star_cayleyChart_mul_mul_fderiv_cayleyChart (hA : A.IsHermitian) (hA' : IsUnit A)
    (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))))
    (T : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    star (cayleyChart A S) * A * fderiv ℝ (cayleyChart A) S T =
      star (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ * T *
        (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹ := by
  -- `φ(S)ᴴ A D⁻¹ = D⁻ᴴ A`, since `-A⁻¹ S / 2` is skew-adjoint for the form of `A`.
  have key := star_cayleyCoord_one_mul_mul_inv (star_neg_smul_inv_mul_mul_add hA S)
  rw [← sub_eq_add_neg, ← cayleyChart_def] at key
  rw [fderiv_cayleyChart_apply hS]
  generalize 1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)) = D at key ⊢
  calc star (cayleyChart A S) * A * (D⁻¹ * A⁻¹ * T * D⁻¹)
      = star (cayleyChart A S) * A * D⁻¹ * A⁻¹ * T * D⁻¹ := by simp only [Matrix.mul_assoc]
    _ = star D⁻¹ * (A * A⁻¹) * T * D⁻¹ := by
        rw [key]
        simp only [Matrix.mul_assoc]
    _ = star D⁻¹ * T * D⁻¹ := by
        rw [mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hA'), Matrix.mul_one]

/-- The logarithmic derivative of the Cayley chart takes skew-Hermitian values. -/
theorem star_cayleyChart_mul_mul_fderiv_cayleyChart_mem (hA : A.IsHermitian) (hA' : IsUnit A)
    (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))))
    (T : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    star (cayleyChart A S) * A * fderiv ℝ (cayleyChart A) S T ∈
      skewAdjoint.submodule ℝ (Matrix n n ℂ) := by
  rw [star_cayleyChart_mul_mul_fderiv_cayleyChart hA hA' hS]
  exact skewAdjoint.conjugate' T.property _

/-- **The logarithmic Jacobian of the Cayley chart.** For an invertible Hermitian `A` and a
skew-Hermitian `S` with `D = 1 - A⁻¹ S / 2` invertible, the logarithmic derivative
`T ↦ φ(S)ᴴ A dφ_S(T)` of the Cayley chart `φ` is a real linear endomorphism of the skew-Hermitian
matrices, with determinant `|det D|^(-2 n)`, equal to `1` at `S = 0`. It is the Jacobian through
which a left Haar measure of the unitary group of `A` is written in Cayley coordinates. -/
theorem det_codRestrict_mulLeft_comp_fderiv_cayleyChart (hA : A.IsHermitian) (hA' : IsUnit A)
    (hS : IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) :
    LinearMap.det (LinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
        (LinearMap.mulLeft ℝ (star (cayleyChart A S) * A) ∘ₗ
          (fderiv ℝ (cayleyChart A) S :
            skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ))
        (star_cayleyChart_mul_mul_fderiv_cayleyChart_mem hA hA' hS)) =
      (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ := by
  have h : LinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
        (LinearMap.mulLeft ℝ (star (cayleyChart A S) * A) ∘ₗ
          (fderiv ℝ (cayleyChart A) S :
            skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ))
        (star_cayleyChart_mul_mul_fderiv_cayleyChart_mem hA hA' hS) =
      skewAdjointConjugate ℝ (star (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))⁻¹) := by
    ext T : 2
    exact (star_cayleyChart_mul_mul_fderiv_cayleyChart hA hA' hS T).trans
      (by simp [star_eq_conjTranspose])
  rw [h, det_skewAdjointConjugate Complex.mem_range_algebraMap_of_isSelfAdjoint
    Complex.val_mk0_I_mem_skewAdjoint, Algebra.norm_complex_apply, star_eq_conjTranspose,
    det_conjTranspose, det_nonsing_inv]
  simp

end Calculus

end unitaryGroupOf

end Matrix
