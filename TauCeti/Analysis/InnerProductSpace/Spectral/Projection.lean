/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus

/-!
# Smooth spectral projections of self-adjoint operators in finite dimension

Let `T` be a self-adjoint operator on a finite-dimensional inner product space `E`. For a set
`Ω ⊆ ℝ`, the functional calculus `cfc (Ω.indicator 1) T` of the indicator of `Ω` is the
orthogonal projection onto the point-spectral subspace of `T` selected by `Ω`, the sum of the
eigenspaces of `T` at the eigenvalues in `Ω`
(`ContinuousLinearMap.cfc_indicator_eq_starProjection`).

For `Ω = (0, ∞)` and `Ω = (-∞, 0)` these are the projections `P₊(T)` and `P₋(T)` onto the
positive and the negative spectral subspaces of `T`. On a real space they depend smoothly, indeed
analytically, on `T` as long as `T` stays invertible
(`ContinuousLinearMap.contDiffOn_cfc_indicator_Ioi` and
`ContinuousLinearMap.contDiffOn_cfc_indicator_Iio`). The proof uses no eigenvectors: for an
invertible self-adjoint `T`, `2 P₊(T) = 1 + T |T|⁻¹` and `2 P₋(T) = 1 - T |T|⁻¹`
(`TauCeti.two_smul_cfc_indicator_Ioi`), where `|T| = √(T T)` is smooth in `T` by the smoothness of
the positive square root on strictly positive operators
(`ContinuousLinearMap.contDiffOn_sqrt`), and inversion is smooth on invertible operators.

Invertibility cannot be dropped: as `T` crosses a singular operator an eigenvalue changes sign
and the rank of `P₊(T)` jumps. For a smooth family of nondegenerate symmetric forms, such as the
normal Hessians along a nondegenerate critical submanifold expressed in local orthonormal frames,
these results make the positive and negative spectral subspaces the ranges of smoothly
varying orthogonal projections, without choosing smoothly varying eigenvectors.

## Main results

* `ContinuousLinearMap.cfc_indicator_eq_starProjection`: the spectral projector
  `cfc (Ω.indicator 1) T` is the orthogonal projection onto the point-spectral subspace of `T`
  selected by `Ω`.
* `ContinuousLinearMap.contDiffOn_cfc_indicator_Ioi` and
  `ContinuousLinearMap.contDiffOn_cfc_indicator_Iio`: the projections onto the positive and the
  negative spectral subspaces are smooth on the invertible self-adjoint operators.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Chapter 5 (the
  matrix sign function `A (A²)^(-1/2)` and the spectral projectors `(1 ± sign A) / 2`).
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Springer, 1976,
  Chapter II (analytic dependence of spectral projections in finite dimension).
-/

public section

open Set

namespace ContinuousLinearMap

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)]
  [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- **The spectral projector is an orthogonal projection.** For a self-adjoint operator `T` on a
finite-dimensional space and a set `Ω ⊆ ℝ`, `cfc (Ω.indicator 1) T` is the orthogonal projection
onto the sum of the eigenspaces of `T` at the eigenvalues in `Ω`. -/
theorem cfc_indicator_eq_starProjection (Ω : Set ℝ) {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    cfc (Ω.indicator 1) T =
      (Module.End.pointSpectralSubspace (T : E →ₗ[𝕜] E) Ω).starProjection := by
  have hs : (T : E →ₗ[𝕜] E).IsSymmetric := isSelfAdjoint_iff_isSymmetric.mp hT
  have h := hs.toContinuousLinearMap_cfc (Ω.indicator 1)
  have hT' : LinearMap.toContinuousLinearMap (T : E →ₗ[𝕜] E) = T := by
    ext
    simp
  rw [← hs.coe_starProjection_pointSpectralSubspace, hT'] at h
  ext v
  simpa using congr($h v).symm

end RCLike

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped ContDiff

/-- On the invertible self-adjoint operators, `T ↦ (T T)^(1/2)⁻¹` is smooth. -/
private theorem contDiffOn_ringInverse_sqrt_mul_self {n : ℕ∞ω} :
    ContDiffOn ℝ n (fun T : E →L[ℝ] E ↦ Ring.inverse (CFC.sqrt (T * T)))
      {T | IsSelfAdjoint T ∧ IsUnit T} := by
  have hpos {T : E →L[ℝ] E} (hT : IsSelfAdjoint T ∧ IsUnit T) : IsStrictlyPositive (T * T) :=
    IsStrictlyPositive.iff_of_unital.mpr
      ⟨by simpa [hT.1.star_eq] using star_mul_self_nonneg T, hT.2.mul hT.2⟩
  have hsqrt : ContDiffOn ℝ n (fun T : E →L[ℝ] E ↦ CFC.sqrt (T * T))
      {T | IsSelfAdjoint T ∧ IsUnit T} :=
    contDiffOn_sqrt.comp (contDiff_id.mul contDiff_id).contDiffOn fun _ hT ↦ hpos hT
  intro T hT
  have hu : IsUnit (CFC.sqrt (T * T)) := (IsStrictlyPositive.sqrt (T * T) (hpos hT)).isUnit
  have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := n) hu.unit
  rw [hu.unit_spec] at h
  exact h.comp_contDiffWithinAt T (hsqrt T hT)

/-- **Smoothness of the positive spectral projection.** On a finite-dimensional real inner
product space, the orthogonal projection `cfc ((Ioi 0).indicator 1) T` onto the positive spectral
subspace of `T` depends smoothly on `T` among the invertible self-adjoint operators. -/
theorem contDiffOn_cfc_indicator_Ioi {n : ℕ∞ω} :
    ContDiffOn ℝ n (fun T : E →L[ℝ] E ↦ cfc ((Ioi (0 : ℝ)).indicator 1) T)
      {T | IsSelfAdjoint T ∧ IsUnit T} := by
  have h := (contDiffOn_const (c := (1 : E →L[ℝ] E))).add
    (contDiffOn_id.mul (contDiffOn_ringInverse_sqrt_mul_self (n := n)))
  refine (h.const_smul (2⁻¹ : ℝ)).congr fun T hT ↦ ?_
  have habs : CFC.sqrt (T * T) = CFC.abs T := by rw [CFC.abs, hT.1.star_eq]
  rw [id, habs, ← TauCeti.two_smul_cfc_indicator_Ioi hT.2 hT.1, smul_smul]
  norm_num

/-- **Smoothness of the negative spectral projection.** On a finite-dimensional real inner
product space, the orthogonal projection `cfc ((Iio 0).indicator 1) T` onto the negative spectral
subspace of `T` depends smoothly on `T` among the invertible self-adjoint operators. -/
theorem contDiffOn_cfc_indicator_Iio {n : ℕ∞ω} :
    ContDiffOn ℝ n (fun T : E →L[ℝ] E ↦ cfc ((Iio (0 : ℝ)).indicator 1) T)
      {T | IsSelfAdjoint T ∧ IsUnit T} := by
  have h := (contDiffOn_const (c := (1 : E →L[ℝ] E))).sub
    (contDiffOn_id.mul (contDiffOn_ringInverse_sqrt_mul_self (n := n)))
  refine (h.const_smul (2⁻¹ : ℝ)).congr fun T hT ↦ ?_
  have habs : CFC.sqrt (T * T) = CFC.abs T := by rw [CFC.abs, hT.1.star_eq]
  rw [id, habs, ← TauCeti.two_smul_cfc_indicator_Iio hT.2 hT.1, smul_smul]
  norm_num

end Real

end ContinuousLinearMap
