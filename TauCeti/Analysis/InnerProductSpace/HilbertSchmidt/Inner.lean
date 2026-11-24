/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
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

## Main statements

* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum`: `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` in any
  orthonormal basis.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum_sum_inner_mul_inner`: the sum of products of
  matrix coefficients in independently chosen source and target orthonormal bases.
* `ContinuousLinearMap.hilbertSchmidtInner_comm`: symmetry.
* `ContinuousLinearMap.hilbertSchmidtInner_add_left`,
  `ContinuousLinearMap.hilbertSchmidtInner_smul_left` and their right-hand versions: bilinearity.
* `ContinuousLinearMap.hilbertSchmidtInner_self_eq_sq_frobenius` and
  `ContinuousLinearMap.hilbertSchmidtInner_self_eq_sq_hilbertSchmidtNorm`: `⟪A, A⟫_HS = ‖A‖_F²`
  and `⟪A, A⟫_HS = ‖A‖_HS²`.
* `ContinuousLinearMap.hilbertSchmidtInner_self_nonneg`,
  `ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero_iff` and
  `ContinuousLinearMap.hilbertSchmidtNorm_eq_zero`: positive definiteness.
* `ContinuousLinearMap.abs_hilbertSchmidtInner_le`: the Cauchy–Schwarz inequality
  `|⟪A, B⟫_HS| ≤ ‖A‖_HS ‖B‖_HS`.
* `ContinuousLinearMap.hilbertSchmidtInner_comp_linearIsometryEquiv`,
  `ContinuousLinearMap.hilbertSchmidtInner_linearIsometry_comp` and
  `ContinuousLinearMap.hilbertSchmidtInner_adjoint_comp`: isometric invariance and adjoint
  compatibility.
* `ContinuousLinearMap.hilbertSchmidtInner_rankOne_left` and
  `ContinuousLinearMap.hilbertSchmidtInner_rankOne_right`: pairing against rank-one operators.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_trace_adjoint_comp` and
  `ContinuousLinearMap.hilbertSchmidtInner_eq_sum_inv_gram`: operator-trace and inverse-Gram
  formulas.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (fiber inner products on bundle homomorphisms).
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {W W' V G : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

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

/-- **Definiteness of the Hilbert–Schmidt norm** on a finite-dimensional source. -/
@[simp]
theorem hilbertSchmidtNorm_eq_zero {A : W →L[ℝ] V} :
    A.hilbertSchmidtNorm = 0 ↔ A = 0 := by
  rw [← sq_eq_zero_iff, ← hilbertSchmidtInner_self_eq_sq_hilbertSchmidtNorm,
    hilbertSchmidtInner_self_eq_zero_iff]

private theorem norm_toLp_stdOrthonormalBasis_eq_hilbertSchmidtNorm (A : W →L[ℝ] V) :
    ‖(WithLp.toLp 2 fun i ↦ A (stdOrthonormalBasis ℝ W i) :
        PiLp 2 fun _ : Fin (Module.finrank ℝ W) ↦ V)‖ = A.hilbertSchmidtNorm := by
  rw [← sq_eq_sq₀ (norm_nonneg _) A.hilbertSchmidtNorm_nonneg, PiLp.norm_sq_eq_of_L2,
    ← A.hilbertSchmidtInner_self_eq_sq_hilbertSchmidtNorm,
    hilbertSchmidtInner_eq_sum A A (stdOrthonormalBasis ℝ W)]
  simp only [real_inner_self_eq_norm_sq]

/-- **Cauchy–Schwarz inequality for the Hilbert–Schmidt inner product.** -/
theorem abs_hilbertSchmidtInner_le (A B : W →L[ℝ] V) :
    |A.hilbertSchmidtInner B| ≤ A.hilbertSchmidtNorm * B.hilbertSchmidtNorm := by
  let e := stdOrthonormalBasis ℝ W
  let u : PiLp 2 (fun _ : Fin (Module.finrank ℝ W) ↦ V) := WithLp.toLp 2 fun i ↦ A (e i)
  let v : PiLp 2 (fun _ : Fin (Module.finrank ℝ W) ↦ V) := WithLp.toLp 2 fun i ↦ B (e i)
  have hinner : A.hilbertSchmidtInner B = ⟪u, v⟫_ℝ := by
    rw [hilbertSchmidtInner_eq_sum A B e, PiLp.inner_apply]
  rw [hinner, ← norm_toLp_stdOrthonormalBasis_eq_hilbertSchmidtNorm A,
    ← norm_toLp_stdOrthonormalBasis_eq_hilbertSchmidtNorm B]
  exact abs_real_inner_le_norm u v

/-- Precomposing both arguments with a linear isometric equivalence preserves the Hilbert–Schmidt
inner product. -/
@[simp]
theorem hilbertSchmidtInner_comp_linearIsometryEquiv (A B : W →L[ℝ] V) (U : W' ≃ₗᵢ[ℝ] W) :
    (A ∘L U.toContinuousLinearMap).hilbertSchmidtInner (B ∘L U.toContinuousLinearMap) =
      A.hilbertSchmidtInner B := by
  let e' := stdOrthonormalBasis ℝ W'
  rw [hilbertSchmidtInner_eq_sum _ _ e', hilbertSchmidtInner_eq_sum A B (e'.map U)]
  simp [OrthonormalBasis.map_apply]

/-- Postcomposing both arguments with a linear isometric map preserves the Hilbert–Schmidt inner
product. -/
@[simp]
theorem hilbertSchmidtInner_linearIsometry_comp (U : V →ₗᵢ[ℝ] G) (A B : W →L[ℝ] V) :
    (U.toContinuousLinearMap ∘L A).hilbertSchmidtInner (U.toContinuousLinearMap ∘L B) =
      A.hilbertSchmidtInner B := by
  let e := stdOrthonormalBasis ℝ W
  simp [hilbertSchmidtInner_eq_sum _ _ e, U.inner_map_map]

/-- Left composition with the operator adjoint moves to the right in `hilbertSchmidtInner`. -/
theorem hilbertSchmidtInner_adjoint_comp [CompleteSpace V] [CompleteSpace G]
    (C : V →L[ℝ] G) (A : W →L[ℝ] G) (B : W →L[ℝ] V) :
    (C.adjoint ∘L A).hilbertSchmidtInner B = A.hilbertSchmidtInner (C ∘L B) := by
  let e := stdOrthonormalBasis ℝ W
  simp only [hilbertSchmidtInner_eq_sum _ _ e, comp_apply, adjoint_inner_left]

/-- Pairing a rank-one operator `v ↦ ⟪x, v⟫ • y` on the left against `B` evaluates `⟪y, B x⟫_ℝ`. -/
@[simp]
theorem hilbertSchmidtInner_rankOne_left (y : V) (x : W) (B : W →L[ℝ] V) :
    (InnerProductSpace.rankOne ℝ y x).hilbertSchmidtInner B = ⟪y, B x⟫_ℝ := by
  let e := stdOrthonormalBasis ℝ W
  rw [hilbertSchmidtInner_eq_sum _ _ e]
  calc ∑ i, ⟪InnerProductSpace.rankOne ℝ y x (e i), B (e i)⟫_ℝ
      = ∑ i, ⟪y, ⟪e i, x⟫_ℝ • B (e i)⟫_ℝ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [InnerProductSpace.rankOne_apply, real_inner_smul_left, real_inner_smul_right,
          real_inner_comm x]
    _ = ⟪y, B (∑ i, ⟪e i, x⟫_ℝ • e i)⟫_ℝ := by
        rw [← inner_sum]
        simp_rw [← map_smul, ← map_sum]
    _ = ⟪y, B x⟫_ℝ := by rw [e.sum_repr']

/-- Pairing `A` against a rank-one operator `v ↦ ⟪x, v⟫ • y` on the right evaluates `⟪A x, y⟫_ℝ`. -/
@[simp]
theorem hilbertSchmidtInner_rankOne_right (A : W →L[ℝ] V) (y : V) (x : W) :
    A.hilbertSchmidtInner (InnerProductSpace.rankOne ℝ y x) = ⟪A x, y⟫_ℝ := by
  rw [hilbertSchmidtInner_comm, hilbertSchmidtInner_rankOne_left, real_inner_comm]

/-- When `V` is also finite-dimensional, the Hilbert–Schmidt inner product is the operator trace
`tr (A† B)`. -/
theorem hilbertSchmidtInner_eq_trace_adjoint_comp [FiniteDimensional ℝ V] (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner B = LinearMap.trace ℝ W (A.toLinearMap.adjoint ∘ₗ B.toLinearMap) := by
  let e := stdOrthonormalBasis ℝ W
  rw [hilbertSchmidtInner_eq_sum A B e, LinearMap.trace_eq_sum_inner _ e]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simp only [coe_coe]

/-- In an arbitrary basis `b` of `W`, the Hilbert–Schmidt inner product contracts the Gram
pairings `⟪A (b i), B (b j)⟫_ℝ` against the inverse Gram matrix `(Matrix.gram ℝ b)⁻¹`. -/
theorem hilbertSchmidtInner_eq_sum_inv_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : W →L[ℝ] V) (b : Module.Basis ι ℝ W) :
    A.hilbertSchmidtInner B =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * ⟪A (b i), B (b j)⟫_ℝ := by
  rw [hilbertSchmidtInner_def, LinearMap.BilinMap.metricTrace_eq_sum_inv_gram _ b]
  simp only [LinearMap.compl₁₂_apply, innerₗ_apply_apply, coe_coe, smul_eq_mul]

end ContinuousLinearMap
