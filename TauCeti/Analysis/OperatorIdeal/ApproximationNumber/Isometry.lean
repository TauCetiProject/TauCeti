/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Approximation numbers under isometric changes of coordinates -/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A linear isometric equivalence is a contraction as a continuous linear map. -/
private theorem norm_linearIsometryEquiv_le_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (g : X ≃ₗᵢ[𝕜] Y) : ‖g.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  simp

/-- One half of the isometric invariance: sandwiching by isometries cannot increase an
approximation number, because both factors are contractions. -/
private theorem approximationNumber_linearIsometryEquiv_sandwich_le {X Y X' Y' : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup X'] [NormedSpace 𝕜 X'] [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
    (a : X' ≃ₗᵢ[𝕜] X) (b : Y ≃ₗᵢ[𝕜] Y') (S : X →L[𝕜] Y) (n : ℕ) :
    (b.toLinearIsometry.toContinuousLinearMap ∘L S ∘L
        a.toLinearIsometry.toContinuousLinearMap).approximationNumber n
      ≤ S.approximationNumber n := by
  calc
    _ ≤ ‖b.toLinearIsometry.toContinuousLinearMap‖ * S.approximationNumber n *
        ‖a.toLinearIsometry.toContinuousLinearMap‖ :=
      approximationNumber_comp_comp_le _ _ _ n
    _ ≤ 1 * S.approximationNumber n * 1 := by
      gcongr <;>
        first
          | exact norm_linearIsometryEquiv_le_one b
          | exact norm_linearIsometryEquiv_le_one a
          | exact approximationNumber_nonneg _ _
          | exact norm_nonneg _
          | exact mul_nonneg zero_le_one (approximationNumber_nonneg _ _)
    _ = _ := by simp

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Isometric changes of domain and codomain preserve every approximation number,
including when the spaces live in different universes. -/
theorem approximationNumber_comp_linearIsometryEquiv
    (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) (n : ℕ) :
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap).approximationNumber n =
      T.approximationNumber n := by
  refine le_antisymm (approximationNumber_linearIsometryEquiv_sandwich_le e f T n) ?_
  have h := approximationNumber_linearIsometryEquiv_sandwich_le e.symm f.symm
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap) n
  have heq : f.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap) ∘L
        e.symm.toLinearIsometry.toContinuousLinearMap = T := by
    ext x
    simp
  rwa [heq] at h

end ContinuousLinearMap
