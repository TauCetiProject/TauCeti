/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

/-!
# Approximation numbers under isometric changes of coordinates

The approximation-number sequence is unchanged by linear isometric changes of
coordinates in the domain and codomain. Consequently, two operators related by
such a change have the same approximation-number sequence and Ky Fan prefix
gauges. This permits transferring approximation-number invariants between
isometric presentations of operator spaces, even across different universes.
The result applies to seminormed spaces without finite-dimensionality or
completeness assumptions.

## Provenance

Adapted from `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Isometry.lean`
in [AIQ-Kitware/aiq-dkps-formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc., Apache-2.0).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Sandwiching an operator by linear isometric equivalences does not increase
its approximation numbers. -/
private theorem singularValue_linearIsometryEquiv_sandwich_le {X Y X' Y' : Type*}
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup X'] [NormedSpace 𝕜 X']
    [SeminormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
    (S : X →L[𝕜] Y) (a : X' ≃ₗᵢ[𝕜] X) (b : Y ≃ₗᵢ[𝕜] Y') (n : ℕ) :
    (b.toLinearIsometry.toContinuousLinearMap ∘L S ∘L
        a.toLinearIsometry.toContinuousLinearMap).singularValue n
      ≤ S.singularValue n := by
  calc
    _ ≤ ‖b.toLinearIsometry.toContinuousLinearMap‖₊ * S.singularValue n *
        ‖a.toLinearIsometry.toContinuousLinearMap‖₊ :=
      singularValue_comp_comp_le _ _ _ n
    _ ≤ 1 * S.singularValue n * 1 := by
      gcongr <;>
        first
          | apply NNReal.coe_le_coe.mp
            simpa only [coe_nnnorm, NNReal.coe_one] using
              b.toLinearIsometry.norm_toContinuousLinearMap_le
          | apply NNReal.coe_le_coe.mp
            simpa only [coe_nnnorm, NNReal.coe_one] using
              a.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = _ := by simp

variable {E F E' F' : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Linear isometric changes of domain and codomain preserve the canonical
nonnegative approximation numbers, even across different universes. -/
@[simp] theorem singularValue_comp_linearIsometryEquiv
    (T : E →L[𝕜] F) (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (n : ℕ) :
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap).singularValue n =
      T.singularValue n := by
  refine le_antisymm (singularValue_linearIsometryEquiv_sandwich_le T e f n) ?_
  have h := singularValue_linearIsometryEquiv_sandwich_le
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap) e.symm f.symm n
  have heq : f.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap) ∘L
        e.symm.toLinearIsometry.toContinuousLinearMap = T := by
    ext x
    simp
  rwa [heq] at h

/-- A change of isometric coordinates preserves the equivalence class of the
approximation-number sequence. -/
@[simp] theorem sameSingularValues_comp_linearIsometryEquiv
    (T : E →L[𝕜] F) (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') :
    SameSingularValues
      (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        e.toLinearIsometry.toContinuousLinearMap) T := by
  apply (sameSingularValues_iff _ _).2
  intro n
  exact singularValue_comp_linearIsometryEquiv T e f n

/-- Ky Fan prefix gauges are invariant under linear isometric coordinate changes. -/
@[simp] theorem kyFanGauge_comp_linearIsometryEquiv
    (T : E →L[𝕜] F) (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (k : ℕ) :
    (f.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
      e.toLinearIsometry.toContinuousLinearMap).kyFanGauge k = T.kyFanGauge k :=
  (sameSingularValues_comp_linearIsometryEquiv T e f).kyFanGauge_eq k

end ContinuousLinearMap
