/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star.LinearMap

/-!
# Continuity and norm preservation of intrinsic conjugation of operators

Mathlib's intrinsic star on `WithConv (E →L[𝕜] F)` sends `f` to
`x ↦ star (f (star x))`, unlike the Hilbert-space adjoint. When the source and target are
`NormedStarGroup` normed spaces, this operation preserves operator norms
(`ContinuousLinearMap.norm_ofConv_star_toConv`), and over `ℂ` the real and imaginary parts under
intrinsic conjugation satisfy `‖(realPart (toConv f)).ofConv‖ ≤ ‖f‖` and
`‖(imaginaryPart (toConv f)).ofConv‖ ≤ ‖f‖`
(`ContinuousLinearMap.norm_ofConv_realPart_toConv_le`,
`ContinuousLinearMap.norm_ofConv_imaginaryPart_toConv_le`). Over a complete nontrivially normed
field, for finite-dimensional source spaces this operation is continuous in the operator topology
(`ContinuousLinearMap.continuous_intrinsicStar`). In particular, entrywise conjugation
preserves continuous families of finite matrices.

The operator and its algebraic laws are those of
`Mathlib.Topology.Algebra.Star.LinearMap` (Monica Omar).
-/

public section

open WithConv

namespace ContinuousLinearMap

/-- Intrinsic conjugation preserves the operator norm of continuous linear maps between
`NormedStarGroup` seminormed spaces. -/
@[simp]
theorem norm_ofConv_star_toConv {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [InvolutiveStar 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [StarAddMonoid E] [StarModule 𝕜 E]
    [NormedStarGroup E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
    [NormedStarGroup F]
    (f : E →L[𝕜] F) : ‖(star (toConv f)).ofConv‖ = ‖f‖ := by
  have hle : ∀ g : E →L[𝕜] F, ‖(star (toConv g)).ofConv‖ ≤ ‖g‖ := fun g =>
    opNorm_le_bound _ (norm_nonneg g) fun x => by
      rw [intrinsicStar_apply, norm_star]
      exact (g.le_opNorm (star x)).trans_eq (by rw [norm_star])
  exact le_antisymm (hle f) (by simpa using hle (star (toConv f)).ofConv)

/-- The real part under intrinsic conjugation has operator norm at most `‖f‖`. -/
theorem norm_ofConv_realPart_toConv_le {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E] [StarModule ℂ E]
    [NormedStarGroup E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
    [NormedStarGroup F]
    (f : E →L[ℂ] F) :
    ‖(realPart (toConv f) : WithConv (E →L[ℂ] F)).ofConv‖ ≤ ‖f‖ := by
  have hval : (realPart (toConv f) : WithConv (E →L[ℂ] F)).ofConv =
      (2 : ℝ)⁻¹ • (f + (star (toConv f)).ofConv) := by
    simpa [WithConv.ofConv_smul, WithConv.ofConv_add] using
      congrArg WithConv.ofConv (realPart_apply_coe (toConv f))
  rw [hval, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (2 : ℝ)⁻¹ * ‖f + (star (toConv f)).ofConv‖
      ≤ 2⁻¹ * (‖f‖ + ‖(star (toConv f)).ofConv‖) := by
        gcongr; exact norm_add_le _ _
    _ = ‖f‖ := by rw [norm_ofConv_star_toConv]; ring

/-- The imaginary part under intrinsic conjugation has operator norm at most `‖f‖`. -/
theorem norm_ofConv_imaginaryPart_toConv_le {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E] [StarModule ℂ E]
    [NormedStarGroup E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
    [NormedStarGroup F]
    (f : E →L[ℂ] F) :
    ‖(imaginaryPart (toConv f) : WithConv (E →L[ℂ] F)).ofConv‖ ≤ ‖f‖ := by
  have heq : (imaginaryPart (toConv f) : WithConv (E →L[ℂ] F)).ofConv =
      -(realPart (toConv (Complex.I • f)) : WithConv (E →L[ℂ] F)).ofConv := by
    simp [WithConv.ofConv_neg, WithConv.toConv_smul]
  rw [heq, norm_neg]
  exact (norm_ofConv_realPart_toConv_le (Complex.I • f)).trans_eq (by simp [norm_smul])

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [InvolutiveStar 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [StarAddMonoid E] [StarModule 𝕜 E]
  [ContinuousStar E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F]

/-- Intrinsic conjugation is continuous on operators with finite-dimensional source. -/
theorem continuous_intrinsicStar :
    Continuous (fun f : E →L[𝕜] F => (star (toConv f)).ofConv) := by
  refine continuous_clm_apply.2 fun x => ?_
  -- Intrinsic star evaluates as `star (f (star x))`; `ofConv` only removes the wrapper.
  exact (ContinuousLinearMap.apply 𝕜 F (star x)).continuous.star

end ContinuousLinearMap
