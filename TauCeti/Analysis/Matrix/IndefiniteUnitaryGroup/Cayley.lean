/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.Analysis.Normed.Algebra.CayleyChart
public import TauCeti.LinearAlgebra.Matrix.Hermitian.Congruence
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Cayley
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
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
* `Matrix.unitaryGroupOf.cayleyChartInv`: the differentiable inverse chart on matrices with
  `1 + g` invertible, extended to all matrices by taking the skew-adjoint part.
* `Matrix.unitaryGroupOf.cayleyChartUnitary`: the chart with values in the unitary group.
* `Matrix.unitaryGroupOf.cayleyChartEquiv`: the chart as a bijection from the skew-Hermitian `S`
  with `1 - A⁻¹ S / 2` invertible onto the `g ∈ U(A)` with `1 + g` invertible.

## Main results

* `Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_cayleyChart`: the chart takes values in `U(A)`.
* `Matrix.unitaryGroupOf.hasFDerivAt_cayleyChart`: the differential of the chart.
* `Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`: the logarithmic derivative
  of the chart is the congruence by `D⁻ᴴ`.
* `Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart`: its determinant is
  `|det D|^(-2 n)`.
* `Matrix.unitaryGroupOf.cayleyChartSource`: the open set of the `S` with `1 - A⁻¹ S / 2`
  invertible, on which the chart is continuous, and injective for invertible `A`
  (`Matrix.unitaryGroupOf.continuousOn_cayleyChart`, `Matrix.unitaryGroupOf.injOn_cayleyChart`).

## Provenance

`Matrix.unitaryGroupOf.cayleyChart`, `Matrix.unitaryGroupOf.cayleyChartEquiv`,
`Matrix.unitaryGroupOf.hasFDerivAt_cayleyChart`,
`Matrix.unitaryGroupOf.star_cayleyChart_mul_mul_fderiv_cayleyChart`,
`Matrix.unitaryGroupOf.det_codRestrict_mulLeft_comp_fderiv_cayleyChart` and the inverse-chart API
are adapted from
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

open Complex TauCeti Set

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace unitaryGroupOf

variable {A : Matrix n n ℂ} {S : skewAdjoint.submodule ℝ (Matrix n n ℂ)}

/-- The **source of the Cayley chart**: the skew-Hermitian `S` with `1 - A⁻¹ S / 2` invertible. -/
def cayleyChartSource (A : Matrix n n ℂ) : Set (skewAdjoint.submodule ℝ (Matrix n n ℂ)) :=
  {S | IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))}

/-- Membership in the source of the Cayley chart. -/
theorem mem_cayleyChartSource :
    S ∈ cayleyChartSource A ↔ IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))) :=
  Iff.rfl

/-- The source of the Cayley chart contains `0`, where the chart is `1`. -/
@[simp]
theorem zero_mem_cayleyChartSource : 0 ∈ cayleyChartSource A := by
  simp [mem_cayleyChartSource]

/-- A skew-Hermitian matrix belongs to the Cayley chart source exactly when the denominator
has nonzero determinant. -/
theorem mem_cayleyChartSource_iff_det_ne_zero :
    S ∈ cayleyChartSource A ↔
      (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ≠ 0 := by
  rw [mem_cayleyChartSource, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The base of the Cayley density is positive on the source of the chart. -/
theorem normSq_det_pow_pos_of_mem_cayleyChartSource (hS : S ∈ cayleyChartSource A) :
    0 < Complex.normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ))).det ^ Fintype.card n :=
  pow_pos (Complex.normSq_pos.2 (mem_cayleyChartSource_iff_det_ne_zero.1 hS)) _

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
  rw [cayleyChart_def, cayleyCoord_neg, ← nonsing_inv_eq_ringInverse]

/-- The Cayley chart is `0` where `1 - A⁻¹ S / 2` is not invertible. -/
theorem cayleyChart_of_not_isUnit
    (hS : ¬IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) : cayleyChart A S = 0 :=
  cayleyCoord_of_not_isUnit (by rwa [← sub_eq_add_neg])

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
    ↥(cayleyChartSource A) ≃
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
          simp⟩, by
          apply mem_cayleyChartSource.2
          -- The subtype coercion is the underlying skew-Hermitian matrix.
          change IsUnit (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (-(2 : ℂ) • (A * X.val))))
          rw [key, sub_neg_eq_add]
          exact X.property.2⟩
      left_inv S := Subtype.ext <| Subtype.ext <| by
        simp [smul_smul, mul_nonsing_inv_cancel_left _ _ hd]
      right_inv X := Subtype.ext <| by simp only [key, neg_neg] }
    (cayleyEquiv hA' (by norm_num))

/-- The image of `S` under `Matrix.unitaryGroupOf.cayleyChartEquiv` is the Cayley chart at `S`. -/
@[simp]
theorem coe_cayleyChartEquiv_apply (hA : A.IsHermitian) (hA' : IsUnit A)
    (S : cayleyChartSource A) :
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

/-- At `0` the derivative of the Cayley chart is `T ↦ A⁻¹ T` for any `A`. When `A` is invertible
and Hermitian, this identifies the skew-Hermitian matrices with the Lie algebra `A⁻¹ 𝔲(n)` of the
unitary group of `A`. -/
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

section Source

/-- The source of the Cayley chart is open. -/
theorem isOpen_cayleyChartSource : IsOpen (cayleyChartSource A) := by
  exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage (by fun_prop)

/-- The Cayley chart is continuous on its source. -/
theorem continuousOn_cayleyChart : ContinuousOn (cayleyChart A) (cayleyChartSource A) := by
  -- The derivative is taken for the Frobenius norm, whose topology is the topology of entries.
  open scoped Matrix.Norms.Frobenius in
  exact fun _ hS ↦ (differentiableAt_cayleyChart hS).continuousAt.continuousWithinAt

/-- The matrix `1 + φ(S)` is invertible: on the source of the chart this is the denominator of
the inverse chart, and elsewhere the chart is `0`. -/
theorem isUnit_one_add_cayleyChart (A : Matrix n n ℂ)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) : IsUnit (1 + cayleyChart A S) :=
  isUnit_one_add_cayleyCoord_one (by
    simpa only [map_ofNat] using (two_ne_zero.isUnit : IsUnit (2 : ℂ)).map
      (algebraMap ℂ (Matrix n n ℂ))) _

/-- The Cayley chart at a point of its source is invertible. -/
theorem isUnit_cayleyChart (hA : A.IsHermitian) (hA' : IsUnit A) (hS : S ∈ cayleyChartSource A) :
    IsUnit (cayleyChart A S) :=
  ⟨((cayleyChartEquiv hA hA' ⟨S, hS⟩).val : GL n ℂ), coe_cayleyChartEquiv_apply hA hA' ⟨S, hS⟩⟩

end Source

open Classical in
/-- The **Cayley chart with values in the unitary group**: the element `φ(S)` of the unitary group
of `A` given by the Cayley chart, where the chart takes invertible values preserving the form of
`A` (for invertible Hermitian `A`, exactly on the source of the chart), and `1` elsewhere. -/
noncomputable def cayleyChartUnitary (A : Matrix n n ℂ)
    (S : skewAdjoint.submodule ℝ (Matrix n n ℂ)) : unitaryGroupOf A :=
  if h : IsUnit (cayleyChart A S) ∧ star (cayleyChart A S) * A * cayleyChart A S = A then
    ⟨h.1.unit, mem_unitaryGroupOf_iff.2 (by rw [IsUnit.unit_spec]; exact h.2)⟩
  else 1

/-- The Cayley chart with values in the unitary group sends zero to the identity. -/
@[simp]
theorem cayleyChartUnitary_zero (A : Matrix n n ℂ) : cayleyChartUnitary A 0 = 1 := by
  classical
  apply unitaryGroupOf.ext
  simp [cayleyChartUnitary]

/-- On the source of the chart, `Matrix.unitaryGroupOf.cayleyChartUnitary` is the Cayley chart. -/
@[simp]
theorem coe_cayleyChartUnitary (hA : A.IsHermitian) (hA' : IsUnit A)
    (hS : S ∈ cayleyChartSource A) :
    (((cayleyChartUnitary A S : unitaryGroupOf A) : GL n ℂ) : Matrix n n ℂ) = cayleyChart A S := by
  have h : IsUnit (cayleyChart A S) ∧ star (cayleyChart A S) * A * cayleyChart A S = A :=
    ⟨isUnit_cayleyChart hA hA' hS,
      star_cayleyChart_mul_mul_cayleyChart hA (mem_cayleyChartSource.1 hS)⟩
  simp [cayleyChartUnitary, h]

/-- On the source of the chart, `Matrix.unitaryGroupOf.cayleyChartUnitary` is the chart
bijection `Matrix.unitaryGroupOf.cayleyChartEquiv`. -/
theorem cayleyChartUnitary_eq_cayleyChartEquiv (hA : A.IsHermitian) (hA' : IsUnit A)
    (hS : S ∈ cayleyChartSource A) :
    cayleyChartUnitary A S = (cayleyChartEquiv hA hA' ⟨S, hS⟩).val :=
  unitaryGroupOf.ext <| by rw [coe_cayleyChartUnitary hA hA' hS, coe_cayleyChartEquiv_apply]

/-- Off the source of the chart, `Matrix.unitaryGroupOf.cayleyChartUnitary` is `1`. -/
@[simp]
theorem cayleyChartUnitary_of_notMem (hS : S ∉ cayleyChartSource A) :
    cayleyChartUnitary A S = 1 := by
  cases isEmpty_or_nonempty n
  · exact unitaryGroupOf.ext (Subsingleton.elim _ _)
  · simp [cayleyChartUnitary, cayleyChart_of_not_isUnit (mt mem_cayleyChartSource.2 hS)]

/-- The Cayley chart with values in the unitary group is continuous on the source of the
chart. -/
theorem continuousOn_cayleyChartUnitary (hA : A.IsHermitian) (hA' : IsUnit A) :
    ContinuousOn (cayleyChartUnitary A) (cayleyChartSource A) := by
  rw [continuousOn_iff_continuous_domRestrict, Topology.IsInducing.subtypeVal.continuous_iff,
    Units.continuous_iff]
  constructor
  · refine (continuousOn_iff_continuous_domRestrict.1 continuousOn_cayleyChart).congr fun S ↦ ?_
    exact (coe_cayleyChartUnitary hA hA' S.property).symm
  · -- The inverse of `g` in the unitary group of `A` is `A⁻¹ gᴴ A`.
    refine (((continuous_const (y := A⁻¹)).mul ((continuousOn_iff_continuous_domRestrict.1
      continuousOn_cayleyChart).star)).mul (continuous_const (y := A))).congr fun S ↦ ?_
    simp only [Function.comp_apply, domRestrict_apply]
    rw [val_inv_of_mem_unitaryGroupOf hA' (cayleyChartUnitary A S).property,
      coe_cayleyChartUnitary hA hA' S.property, Pi.mul_apply, Pi.mul_apply, Pi.star_apply,
      domRestrict_apply]

/-- The inverse `g ↦ -2 A c(g)` of the Cayley chart, extended to all matrices `g` by taking the
skew-adjoint part. -/
noncomputable def cayleyChartInv (A g : Matrix n n ℂ) :
    skewAdjoint.submodule ℝ (Matrix n n ℂ) :=
  -- Mathlib's skew-adjoint subtype is the carrier of the skew-adjoint submodule.
  skewAdjointPart ℝ (-(2 : ℂ) • (A * cayleyCoord 1 g))

/-- The defining formula of the inverse Cayley chart. -/
theorem cayleyChartInv_def (A g : Matrix n n ℂ) :
    cayleyChartInv A g = skewAdjointPart ℝ (-(2 : ℂ) • (A * cayleyCoord 1 g)) :=
  (rfl)

/-- On the image of the chart, `cayleyChartInv` is the inverse of the chart bijection. -/
theorem cayleyChartInv_eq_cayleyChartEquiv_symm (hA : A.IsHermitian) (hA' : IsUnit A)
    (g : unitaryGroupOf A)
    (hg : IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))) :
    cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ) =
      ((cayleyChartEquiv hA hA').symm ⟨g, hg⟩).val := by
  set T := ((cayleyChartEquiv hA hA').symm ⟨g, hg⟩).val
  have hT : (T : Matrix n n ℂ) = -(2 : ℂ) • (A * cayleyCoord 1 ((g : GL n ℂ) : Matrix n n ℂ)) := by
    simp [T]
  rw [cayleyChartInv, ← hT]
  exact LinearMap.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint ℝ
    (A := Matrix n n ℂ)) T

open scoped Matrix.Norms.Frobenius in
/-- The inverse Cayley chart is differentiable where `1 + g` is invertible. -/
theorem differentiableAt_cayleyChartInv {g : Matrix n n ℂ} (hg : IsUnit (1 + g)) :
    DifferentiableAt ℝ (cayleyChartInv A) g := by
  -- Retype Mathlib's skew-adjoint projection with the submodule topology used by the chart.
  let p : Matrix n n ℂ →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix n n ℂ) := skewAdjointPart ℝ
  exact (LinearMap.toContinuousLinearMap p).differentiableAt.comp g
    (((hasFDerivAt_cayleyCoord_one (𝕜 := ℝ) hg).differentiableAt.const_mul A).const_smul
      (-(2 : ℂ)))

/-- The inverse of the chart undoes the chart on its source. -/
@[simp]
theorem cayleyChartInv_cayleyChart (hA' : IsUnit A) {S}
    (hS : S ∈ cayleyChartSource A) : cayleyChartInv A (cayleyChart A S) = S := by
  have h2 : IsUnit (2 : Matrix n n ℂ) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.2 (by norm_num : (2 : ℂ) ≠ 0)).map
      (algebraMap ℂ (Matrix n n ℂ))
  have hS' : IsUnit (1 + -((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) := by
    simpa only [← sub_eq_add_neg] using mem_cayleyChartSource.1 hS
  rw [cayleyChartInv_def, cayleyChart_def, cayleyCoord_one_cayleyCoord_one h2 hS']
  have h : -(2 : ℂ) • (A * -((2 : ℂ)⁻¹ • (A⁻¹ * (S : Matrix n n ℂ)))) = S := by
    simp [smul_smul, mul_nonsing_inv_cancel_left _ _
      ((isUnit_iff_isUnit_det _).1 hA')]
  rw [h]
  exact LinearMap.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint ℝ
    (A := Matrix n n ℂ)) S

/-- The inverse chart maps a unitary matrix with `1 + g` invertible into the source of the
chart, and the chart recovers that matrix. -/
theorem cayleyChartInv_mem_and_cayleyChartUnitary_cayleyChartInv
    (hA : A.IsHermitian) (hA' : IsUnit A)
    (g : unitaryGroupOf A)
    (hg : IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))) :
    cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ) ∈ cayleyChartSource A ∧
      cayleyChartUnitary A (cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ)) = g := by
  rw [cayleyChartInv_eq_cayleyChartEquiv_symm hA hA' g hg]
  have hmem := ((cayleyChartEquiv hA hA').symm ⟨g, hg⟩).property
  refine ⟨hmem, ?_⟩
  rw [cayleyChartUnitary_eq_cayleyChartEquiv hA hA' hmem]
  simp

/-- Applying the Cayley chart to its inverse recovers a unitary matrix when `1 + g` is
invertible. -/
theorem cayleyChart_cayleyChartInv (hA : A.IsHermitian) (hA' : IsUnit A)
    (g : unitaryGroupOf A) (hg : IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))) :
    cayleyChart A (cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ)) =
      ((g : GL n ℂ) : Matrix n n ℂ) := by
  obtain ⟨hmem, heq⟩ := cayleyChartInv_mem_and_cayleyChartUnitary_cayleyChartInv hA hA' g hg
  rw [← coe_cayleyChartUnitary hA hA' hmem, heq]

/-- The Cayley chart is injective on its source. -/
theorem injOn_cayleyChart (hA' : IsUnit A) :
    Set.InjOn (cayleyChart A) (cayleyChartSource A) := fun S hS S' hS' h ↦ by
  rw [← cayleyChartInv_cayleyChart hA' hS, h, cayleyChartInv_cayleyChart hA' hS']

/-- The inverse Cayley chart is continuous where `1 + g` is invertible. -/
theorem continuousOn_cayleyChartInv :
    ContinuousOn (cayleyChartInv A) {g : Matrix n n ℂ | IsUnit (1 + g)} := by
  open scoped Matrix.Norms.Frobenius in
  exact fun _ hg ↦ (differentiableAt_cayleyChartInv hg).continuousAt.continuousWithinAt

/-- The Cayley chart with values in the unitary group is an open map on the source of the chart:
on the open set of the `g` with `1 + g` invertible, the image of an open `V` is the preimage of `V`
under the inverse chart. -/
theorem isOpen_image_cayleyChartUnitary (hA : A.IsHermitian) (hA' : IsUnit A)
    {V : Set (skewAdjoint.submodule ℝ (Matrix n n ℂ))}
    (hV : IsOpen V) (hVs : V ⊆ cayleyChartSource A) : IsOpen (cayleyChartUnitary A '' V) := by
  have hW : IsOpen {g : unitaryGroupOf A | IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))} := by
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage (by fun_prop)
  have : cayleyChartUnitary A '' V =
      {g : unitaryGroupOf A | IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ))} ∩
        (fun g : unitaryGroupOf A ↦ cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ)) ⁻¹' V := by
    ext g
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [mem_inter_iff, mem_ofPred_eq, mem_preimage, coe_cayleyChartUnitary hA hA' (hVs hS),
        cayleyChartInv_cayleyChart hA' (hVs hS)]
      exact ⟨isUnit_one_add_cayleyChart A S, hS⟩
    · rintro ⟨hg, hg'⟩
      exact ⟨_, hg', (cayleyChartInv_mem_and_cayleyChartUnitary_cayleyChartInv
        hA hA' g hg).2⟩
  rw [this]
  exact ContinuousOn.isOpen_inter_preimage (continuousOn_cayleyChartInv.comp
    (Units.continuous_val.comp continuous_subtypeVal).continuousOn fun g hg ↦ hg) hW hV

end unitaryGroupOf

end Matrix
