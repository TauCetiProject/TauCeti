/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Spheres and balls in pseudo-metric spaces

A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same centre
(`Metric.sphere_abs_subset_ball`); the radius is written `|r|`, as in circle integrals.
-/

public section

open Metric

/-- A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same
centre; the radius is written `|r|`, as in circle integrals. -/
theorem Metric.sphere_abs_subset_ball {X : Type*} [PseudoMetricSpace X] {x : X} {r R : ℝ}
    (hr : r ∈ Set.Ioo 0 R) : sphere x |r| ⊆ ball x R := by
  rw [abs_of_pos hr.1]
  exact sphere_subset_ball hr.2
