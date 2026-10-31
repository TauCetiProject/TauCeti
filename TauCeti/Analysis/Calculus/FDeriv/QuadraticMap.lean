/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Fréchet derivatives of quadratic maps

A quadratic map `Q` on a finite-dimensional normed space over a complete field is strictly
differentiable, and its derivative at `x` is the linear map `h ↦ polar Q x h`
(`QuadraticMap.hasStrictFDerivAt`). This upgrades Mathlib's line derivative of a quadratic map
(`QuadraticMap.hasLineDerivAt`), which requires no topology on the domain, to a Fréchet
derivative.

The proof writes `Q` as `x ↦ B x x` for a bilinear map `B`, which is possible because the
space is free (`LinearMap.BilinMap.toQuadraticMap_surjective`); no assumption on the
characteristic of the field is needed.
-/

public section

namespace QuadraticMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A quadratic map on a finite-dimensional space is strictly differentiable, with derivative
`h ↦ polar Q x h` at `x`. -/
theorem hasStrictFDerivAt (Q : QuadraticMap 𝕜 E F) (x : E) :
    HasStrictFDerivAt Q (LinearMap.toContinuousLinearMap (polarBilin Q x)) x := by
  obtain ⟨B, rfl⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  have hd : LinearMap.toContinuousLinearMap (polarBilin B.toQuadraticMap x) =
      B.toContinuousBilinearMap.precompR E x (.id 𝕜 E) +
        B.toContinuousBilinearMap.precompL E (.id 𝕜 E) x := by
    ext h
    simp [LinearMap.BilinMap.polar_toQuadraticMap]
  rw [hd]
  exact B.toContinuousBilinearMap.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id x)
    (hasStrictFDerivAt_id x)

/-- A quadratic map on a finite-dimensional space has derivative `h ↦ polar Q x h` at `x`. -/
theorem hasFDerivAt (Q : QuadraticMap 𝕜 E F) (x : E) :
    HasFDerivAt Q (LinearMap.toContinuousLinearMap (polarBilin Q x)) x :=
  (Q.hasStrictFDerivAt x).hasFDerivAt

/-- A quadratic map on a finite-dimensional space is differentiable. -/
theorem differentiable (Q : QuadraticMap 𝕜 E F) : Differentiable 𝕜 Q :=
  fun x ↦ (Q.hasFDerivAt x).differentiableAt

/-- The derivative of a quadratic map on a finite-dimensional space at `x` is
`h ↦ polar Q x h`. -/
theorem fderiv_apply (Q : QuadraticMap 𝕜 E F) (x h : E) : fderiv 𝕜 Q x h = polar Q x h := by
  rw [(Q.hasFDerivAt x).fderiv]
  simp

end QuadraticMap
