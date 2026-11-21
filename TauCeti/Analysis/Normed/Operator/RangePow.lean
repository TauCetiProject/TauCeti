/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.LinearAlgebra.End.RangePow

/-!
# Invertibility on a stable range

A bounded endomorphism of a Banach space restricts to an invertible bounded operator on
a closed range of a power once both its kernel and range chains have stabilized.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- If both power chains stabilize at `n` and the range of the `n`th power is closed,
the restriction to that range has a bounded inverse. No compactness hypothesis is needed. -/
theorem isUnit_restrict_range_pow_of_stable (A : X →L[𝕜] X) (n : ℕ)
    (hk : LinearMap.ker ((A : X →ₗ[𝕜] X) ^ (n + 1)) =
      LinearMap.ker ((A : X →ₗ[𝕜] X) ^ n))
    (hr : LinearMap.range ((A : X →ₗ[𝕜] X) ^ (n + 1)) =
      LinearMap.range ((A : X →ₗ[𝕜] X) ^ n))
    (hc : IsClosed (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n) : Set X))
    (h : Set.MapsTo A (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n))
      (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := A.toLinearMap.mapsTo_range_pow n) :
    IsUnit (A.restrict h : LinearMap.range ((A : X →ₗ[𝕜] X) ^ n) →L[𝕜]
      LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := by
  have : CompleteSpace (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := hc.completeSpace_coe
  rw [isUnit_iff_bijective]
  exact LinearMap.bijective_restrict_range_pow_of_stable A.toLinearMap n hk hr h

end ContinuousLinearMap
