/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.EMetricSpace.Defs

/-!
# Power bounds for extended distances

For nonnegative real exponents, the triangle inequality gives a split upper bound for a power
of the extended distance in terms of powers of the distances from any fixed basepoint.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [WeakPseudoEMetricSpace X]

/-- **The split bound for a power of the distance.** For a nonnegative exponent `r`, the cost
`edist x y ^ r` is bounded by `K * edist x₀ x ^ r + K * edist x₀ y ^ r` about any basepoint `x₀`,
with the finite constant `K = ENNReal.LpAddConst (ENNReal.ofReal r)⁻¹`. -/
theorem edist_rpow_le_mul_edist_rpow_add_mul_edist_rpow {r : ℝ} (hr : 0 ≤ r) (x₀ x y : X) :
    edist x y ^ r ≤ ENNReal.LpAddConst (ENNReal.ofReal r)⁻¹ * edist x₀ x ^ r +
      ENNReal.LpAddConst (ENNReal.ofReal r)⁻¹ * edist x₀ y ^ r :=
  calc edist x y ^ r ≤ (edist x₀ x + edist x₀ y) ^ r :=
        ENNReal.rpow_le_rpow (edist_triangle_left _ _ _) hr
    _ ≤ ENNReal.LpAddConst (ENNReal.ofReal r)⁻¹ * (edist x₀ x ^ r + edist x₀ y ^ r) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ hr
    _ = _ := mul_add _ _ _


end TauCeti
