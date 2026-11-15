/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distance on binary products

The product `X × Y` of two pseudometric spaces carries the sup distance
`dist x y = max (dist x.1 y.1) (dist x.2 y.2)`. When both factors are ultrametric, their binary
product is again ultrametric, complementing Mathlib's `Pi.instIsUltrametricDist` for finite
dependent products.
-/

public section

/-- The binary product of two ultrametric pseudometric spaces is ultrametric under the sup
distance. -/
instance Prod.instIsUltrametricDist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) where
  dist_triangle_max x y z := by
    simp only [Prod.dist_eq, max_le_iff]
    exact ⟨(dist_triangle_max x.1 y.1 z.1).trans (max_le_max (le_max_left _ _) (le_max_left _ _)),
      (dist_triangle_max x.2 y.2 z.2).trans (max_le_max (le_max_right _ _) (le_max_right _ _))⟩
