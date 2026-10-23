/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import Mathlib.Data.Finsupp.Order

/-!
# Directed Frobenius sine between subspaces

For subspaces `U` and `V` of a finite-dimensional inner product space, the Frobenius sine
`U.sinThetaFrobenius V` is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`.
It packages the quantity used in Frobenius subspace perturbation inequalities without
selecting bases. The quantity is not generally symmetric and vanishes exactly when
`U ≤ V`, so it is not a distance on arbitrary subspaces.

The Frobenius sine is the square root of the sum of the squared principal sines.
The operator norm of the directed sine map sees only the largest principal sine;
the Frobenius quantity accounts for all of them.

## Source

* AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
* Source file: `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`.
-/

public section

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The Frobenius seminorm of the directed sine map between two subspaces. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
    (U.sinThetaMap V : E →ₗ[𝕜] E)

/-- The Frobenius sine is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`. -/
theorem sinThetaFrobenius_def (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
        (U.sinThetaMap V : E →ₗ[𝕜] E) :=
  (rfl)

/-- The Frobenius sine is nonnegative. -/
theorem sinThetaFrobenius_nonneg (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ U.sinThetaFrobenius V := by
  rw [sinThetaFrobenius_def]
  exact apply_nonneg _ _

/-- The Frobenius sine is the Euclidean norm of the principal-sine list. -/
theorem sinThetaFrobenius_eq_sqrt_sum_sq_principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = √((U.principalSines V).sum fun _ s => s ^ 2) := by
  rw [sinThetaFrobenius_def,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    ← principalSines_def]

/-- The squared Frobenius sine equals the sum of the squared principal sines. -/
theorem sq_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.sinThetaFrobenius V) ^ 2 = (U.principalSines V).sum fun _ s => s ^ 2 := by
  have hs : 0 ≤ (U.principalSines V).sum (fun _ s => s ^ 2) := by
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [sinThetaFrobenius_eq_sqrt_sum_sq_principalSines, Real.sq_sqrt hs]

/-- The directed projection gap is bounded by the Frobenius sine. -/
theorem directedProjectionGap_le_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap V ≤ U.sinThetaFrobenius V := by
  have h := TauCeti.UnitarilyInvariantSeminorm.opNorm_apply_le_schatten_apply 2
    (U.sinThetaMap V : E →ₗ[𝕜] E)
  rw [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
    TauCeti.UnitarilyInvariantSeminorm.schatten_two] at h
  have hcont : LinearMap.toContinuousLinearMap
      (U.sinThetaMap V : E →ₗ[𝕜] E) = U.sinThetaMap V :=
    (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl
  simpa only [hcont, U.norm_sinThetaMap V, sinThetaFrobenius_def] using h

/-- The Frobenius sine vanishes precisely when the first subspace is contained in the second. -/
@[simp]
theorem sinThetaFrobenius_eq_zero_iff (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = 0 ↔ U ≤ V := by
  constructor
  · intro h
    exact (U.directedProjectionGap_eq_zero_iff V).mp <|
      le_antisymm (h ▸ U.directedProjectionGap_le_sinThetaFrobenius V)
        (U.directedProjectionGap_nonneg V)
  · intro h
    rw [sinThetaFrobenius_def, (U.sinThetaMap_eq_zero_iff V).mpr h]
    simp

/-- The Frobenius sine from a subspace to itself is zero. -/
@[simp]
theorem sinThetaFrobenius_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : U.sinThetaFrobenius U = 0 :=
  (U.sinThetaFrobenius_eq_zero_iff U).mpr le_rfl

end Submodule
