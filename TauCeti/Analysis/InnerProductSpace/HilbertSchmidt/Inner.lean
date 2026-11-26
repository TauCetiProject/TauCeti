/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic

/-!
# The Hilbert–Schmidt inner product

For two linear maps `A B : W →L[ℝ] V` out of a finite-dimensional real inner product space, the
**Hilbert–Schmidt inner product** is `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` for any orthonormal basis `eᵢ`
of the source. It is defined as the metric trace `LinearMap.BilinMap.metricTrace` of the bilinear
form `(u, v) ↦ ⟪A u, B v⟫`, so it does not depend on a basis. It is symmetric and bilinear, and on
the diagonal it is the square of the Frobenius seminorm
`TauCeti.UnitarilyInvariantSeminorm.frobenius` and of the Hilbert–Schmidt norm
`ContinuousLinearMap.hilbertSchmidtNorm`.

## Main definitions

* `ContinuousLinearMap.hilbertSchmidtInner`: the Hilbert–Schmidt inner product `⟪A, B⟫_HS`.
* `ContinuousLinearMap.hilbertSchmidtInnerL`: the continuous linear functional `B ↦ ⟪A, B⟫_HS`.

## Main statements

* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum`: `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` in any
  orthonormal basis.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum_sum_inner_mul_inner`: the sum of products of
  matrix coefficients in independently chosen source and target orthonormal bases.
* `ContinuousLinearMap.hilbertSchmidtInner_comm`: symmetry.
* `ContinuousLinearMap.hilbertSchmidtInner_add_left`,
  `ContinuousLinearMap.hilbertSchmidtInner_sub_left`,
  `ContinuousLinearMap.hilbertSchmidtInner_neg_left`,
  `ContinuousLinearMap.hilbertSchmidtInner_smul_left` and their right-hand versions: bilinearity.
* `ContinuousLinearMap.hilbertSchmidtInner_self_eq_sq_frobenius` and
  `ContinuousLinearMap.hilbertSchmidtInner_self_eq_sq_hilbertSchmidtNorm`: `⟪A, A⟫_HS = ‖A‖_F²`
  and `⟪A, A⟫_HS = ‖A‖_HS²`.
* `ContinuousLinearMap.hilbertSchmidtInner_self_nonneg` and
  `ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero_iff`: positive definiteness.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **Hilbert–Schmidt inner product** `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two linear maps out of
a finite-dimensional real inner product space, for any orthonormal basis `eᵢ` of the source
(`ContinuousLinearMap.hilbertSchmidtInner_eq_sum`): the metric trace of the bilinear form
`(u, v) ↦ ⟪A u, B v⟫`, so it does not depend on a basis. -/
noncomputable def hilbertSchmidtInner (A B : W →L[ℝ] V) : ℝ :=
  LinearMap.BilinMap.metricTrace ((innerₗ V).compl₁₂ (A : W →ₗ[ℝ] V) (B : W →ₗ[ℝ] V))

/-- The Hilbert–Schmidt inner product is the metric trace of `(u, v) ↦ ⟪A u, B v⟫`. -/
theorem hilbertSchmidtInner_def (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner B =
      LinearMap.BilinMap.metricTrace ((innerₗ V).compl₁₂ (A : W →ₗ[ℝ] V) (B : W →ₗ[ℝ] V)) :=
  (rfl)

/-- The Hilbert–Schmidt inner product in an orthonormal basis: `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫`. -/
theorem hilbertSchmidtInner_eq_sum (A B : W →L[ℝ] V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ W) : A.hilbertSchmidtInner B = ∑ i, ⟪A (b i), B (b i)⟫_ℝ := by
  simp only [hilbertSchmidtInner_def, LinearMap.BilinMap.metricTrace_eq_sum _ b,
    LinearMap.compl₁₂_apply, innerₗ_apply_apply, coe_coe]

/-- The Hilbert–Schmidt inner product is the sum of products of matrix coefficients. -/
theorem hilbertSchmidtInner_eq_sum_sum_inner_mul_inner (A B : W →L[ℝ] V)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ W) (c : OrthonormalBasis κ ℝ V) :
    A.hilbertSchmidtInner B =
      ∑ i, ∑ j, inner ℝ (A (b i)) (c j) * inner ℝ (B (b i)) (c j) := by
  rw [hilbertSchmidtInner_eq_sum A B b]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [real_inner_comm (B (b i))] using
    (c.sum_inner_mul_inner (A (b i)) (B (b i))).symm

/-- The Hilbert–Schmidt inner product is symmetric. -/
theorem hilbertSchmidtInner_comm (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner B = B.hilbertSchmidtInner A := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), real_inner_comm (A _)]

/-- The Hilbert–Schmidt inner product vanishes when its left argument is zero. -/
@[simp]
theorem hilbertSchmidtInner_zero_left (B : W →L[ℝ] V) :
    (0 : W →L[ℝ] V).hilbertSchmidtInner B = 0 := by
  simp [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W)]

/-- The Hilbert–Schmidt inner product vanishes when its right argument is zero. -/
@[simp]
theorem hilbertSchmidtInner_zero_right (A : W →L[ℝ] V) : A.hilbertSchmidtInner 0 = 0 := by
  simp [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W)]

/-- The Hilbert–Schmidt inner product is additive in its left argument. -/
theorem hilbertSchmidtInner_add_left (A₁ A₂ B : W →L[ℝ] V) :
    (A₁ + A₂).hilbertSchmidtInner B = A₁.hilbertSchmidtInner B + A₂.hilbertSchmidtInner B := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), add_apply, inner_add_left,
    Finset.sum_add_distrib]

/-- The Hilbert–Schmidt inner product is additive in its right argument. -/
theorem hilbertSchmidtInner_add_right (A B₁ B₂ : W →L[ℝ] V) :
    A.hilbertSchmidtInner (B₁ + B₂) = A.hilbertSchmidtInner B₁ + A.hilbertSchmidtInner B₂ := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), add_apply, inner_add_right,
    Finset.sum_add_distrib]

/-- The Hilbert–Schmidt inner product is homogeneous in its left argument. -/
theorem hilbertSchmidtInner_smul_left (c : ℝ) (A B : W →L[ℝ] V) :
    (c • A).hilbertSchmidtInner B = c * A.hilbertSchmidtInner B := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), smul_apply,
    real_inner_smul_left, Finset.mul_sum]

/-- The Hilbert–Schmidt inner product is homogeneous in its right argument. -/
theorem hilbertSchmidtInner_smul_right (c : ℝ) (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner (c • B) = c * A.hilbertSchmidtInner B := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), smul_apply,
    real_inner_smul_right, Finset.mul_sum]

/-- The Hilbert–Schmidt inner product is subtractive in its left argument. -/
theorem hilbertSchmidtInner_sub_left (A₁ A₂ B : W →L[ℝ] V) :
    (A₁ - A₂).hilbertSchmidtInner B = A₁.hilbertSchmidtInner B - A₂.hilbertSchmidtInner B := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), sub_apply, inner_sub_left,
    Finset.sum_sub_distrib]

/-- The Hilbert–Schmidt inner product is subtractive in its right argument. -/
theorem hilbertSchmidtInner_sub_right (A B₁ B₂ : W →L[ℝ] V) :
    A.hilbertSchmidtInner (B₁ - B₂) = A.hilbertSchmidtInner B₁ - A.hilbertSchmidtInner B₂ := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), sub_apply, inner_sub_right,
    Finset.sum_sub_distrib]

/-- The Hilbert–Schmidt inner product changes sign with its left argument. -/
theorem hilbertSchmidtInner_neg_left (A B : W →L[ℝ] V) :
    (-A).hilbertSchmidtInner B = -A.hilbertSchmidtInner B := by
  simpa using hilbertSchmidtInner_smul_left (-1) A B

/-- The Hilbert–Schmidt inner product changes sign with its right argument. -/
theorem hilbertSchmidtInner_neg_right (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner (-B) = -A.hilbertSchmidtInner B := by
  simpa using hilbertSchmidtInner_smul_right (-1) A B

/-- The Hilbert–Schmidt inner product `B ↦ ⟪A, B⟫_HS` with a fixed left argument, as a continuous
linear functional. -/
noncomputable def hilbertSchmidtInnerL (A : W →L[ℝ] V) : (W →L[ℝ] V) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (A (stdOrthonormalBasis ℝ W i))).comp (apply ℝ V (stdOrthonormalBasis ℝ W i))

@[simp]
theorem hilbertSchmidtInnerL_apply (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInnerL B = A.hilbertSchmidtInner B := by
  simp [hilbertSchmidtInnerL, hilbertSchmidtInner_eq_sum A B (stdOrthonormalBasis ℝ W)]

/-- On the diagonal, the Hilbert–Schmidt inner product is the square of the Frobenius seminorm:
`⟪A, A⟫_HS = ‖A‖_F²`. -/
theorem hilbertSchmidtInner_self_eq_sq_frobenius (A : W →L[ℝ] V) :
    A.hilbertSchmidtInner A =
      TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ W V A.toLinearMap ^ 2 := by
  set b := stdOrthonormalBasis ℝ W
  rw [hilbertSchmidtInner_eq_sum _ _ b, TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b]
  simp

/-- On the diagonal, the Hilbert–Schmidt inner product is the square of the Hilbert–Schmidt norm:
`⟪A, A⟫_HS = ‖A‖_HS²`. -/
theorem hilbertSchmidtInner_self_eq_sq_hilbertSchmidtNorm (A : W →L[ℝ] V) :
    A.hilbertSchmidtInner A = A.hilbertSchmidtNorm ^ 2 := by
  let b := (stdOrthonormalBasis ℝ W).toHilbertBasis
  rw [A.sq_hilbertSchmidtNorm b, A.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius b,
    ENNReal.toReal_ofReal (sq_nonneg _), hilbertSchmidtInner_self_eq_sq_frobenius]

/-- The Hilbert–Schmidt inner product is nonnegative on the diagonal. -/
theorem hilbertSchmidtInner_self_nonneg (A : W →L[ℝ] V) : 0 ≤ A.hilbertSchmidtInner A := by
  rw [hilbertSchmidtInner_self_eq_sq_frobenius]
  exact sq_nonneg _

/-- The Hilbert–Schmidt inner product is positive definite: `⟪A, A⟫_HS = 0` exactly when
`A = 0`. -/
@[simp]
theorem hilbertSchmidtInner_self_eq_zero_iff (A : W →L[ℝ] V) :
    A.hilbertSchmidtInner A = 0 ↔ A = 0 := by
  set b := stdOrthonormalBasis ℝ W
  rw [hilbertSchmidtInner_self_eq_sq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by positivity]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, norm_eq_zero, coe_coe]
  refine ⟨fun h ↦ ext fun v ↦ ?_, fun h i ↦ by simp [h]⟩
  rw [← b.sum_repr' v]
  simp [h]

end ContinuousLinearMap
