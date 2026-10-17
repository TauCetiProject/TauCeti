/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric structure on bounded continuous functions

The sup distance on bounded continuous functions `α →ᵇ β` into an ultrametric space `β` is
ultrametric, and so is the induced distance on the space `C₀(α, β)` of continuous functions
vanishing at infinity. This complements Mathlib's instance for `C(X, Y)` with `X` compact. In
particular, for a nonarchimedean normed ring `R` and a discrete index `I`, the model space
`C₀(I, R)` of nonarchimedean functional analysis has an ultrametric norm.
-/

public section

open scoped ZeroAtInfty BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β]

/-- The sup distance on bounded continuous functions into an ultrametric space is
ultrametric. -/
instance instIsUltrametricDist [IsUltrametricDist β] : IsUltrametricDist (α →ᵇ β) where
  dist_triangle_max f g h := (dist_le (by positivity)).2 fun x ↦
    (IsUltrametricDist.dist_triangle_max (f x) (g x) (h x)).trans
      (max_le_max (dist_coe_le_dist x) (dist_coe_le_dist x))

end BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

variable {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] [Zero β]

/-- The sup distance on continuous functions vanishing at infinity with values in an ultrametric
space is ultrametric. -/
instance instIsUltrametricDist [IsUltrametricDist β] : IsUltrametricDist C₀(α, β) where
  dist_triangle_max f g h := IsUltrametricDist.dist_triangle_max f.toBCF g.toBCF h.toBCF

end ZeroAtInftyContinuousMap
