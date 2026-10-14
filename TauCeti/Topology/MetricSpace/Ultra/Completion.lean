/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Completions of ultrametric spaces

The distance on the completion of a pseudometric space extends the distance on the space by
continuity, and the strong triangle inequality `dist x z ≤ max (dist x y) (dist y z)` is a closed
condition, so the completion of an ultrametric space is ultrametric. In particular the
completion of a nonarchimedean normed ring has an ultrametric norm.
-/

public section

namespace UniformSpace.Completion

/-- **The completion of an ultrametric space is ultrametric.** -/
instance {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X] :
    IsUltrametricDist (Completion X) where
  dist_triangle_max x y z := by
    induction x, y, z using induction_on₃ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b c => simpa only [Completion.dist_eq] using IsUltrametricDist.dist_triangle_max a b c

end UniformSpace.Completion
