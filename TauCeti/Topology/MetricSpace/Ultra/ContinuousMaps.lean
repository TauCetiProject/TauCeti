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

The uniform distance between two bounded continuous functions is the supremum of the pointwise
distances, and the strong triangle inequality passes to suprema. Hence bounded continuous
functions with values in an ultrametric space form an ultrametric space, and so do continuous
functions vanishing at infinity, whose distance is induced from bounded continuous functions.
For instance the space `C₀(I, E)` of null families on a discrete index type `I` with values in a
nonarchimedean normed group `E` has an ultrametric sup norm.

Mathlib's `ContinuousMap.isUltrametricDist` is the corresponding instance for continuous maps on
a compact space.
-/

public section

open scoped BoundedContinuousFunction ZeroAtInfty

variable {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] [IsUltrametricDist β]

/-- Bounded continuous functions with values in an ultrametric space form an ultrametric space. -/
instance BoundedContinuousFunction.isUltrametricDist : IsUltrametricDist (α →ᵇ β) where
  dist_triangle_max f g h := (dist_le (by positivity)).2 fun x ↦
    (dist_triangle_max (f x) (g x) (h x)).trans
      (max_le_max (dist_coe_le_dist x) (dist_coe_le_dist x))

/-- Continuous functions vanishing at infinity with values in an ultrametric space form an
ultrametric space. -/
instance ZeroAtInftyContinuousMap.isUltrametricDist [Zero β] : IsUltrametricDist C₀(α, β) where
  dist_triangle_max f g h := by
    simpa only [dist_toBCF_eq_dist] using dist_triangle_max f.toBCF g.toBCF h.toBCF
