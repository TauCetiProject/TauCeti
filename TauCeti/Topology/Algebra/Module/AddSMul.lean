/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Moving a short time along a direction

In a topological module `E` over a topological semiring `R`, the point `b + t • w` tends to `b`
as `t` tends to `0`, also within any set of times such as `Set.Ioi 0`. This is the limit used to
approach a point along a ray.
-/

public section

open Filter Topology

namespace TauCeti

/-- Moving from `b` in the direction `w` for a short time, taken in any set `s` of times, stays
close to `b`. -/
theorem tendsto_add_smul_nhdsWithin_zero {R E : Type*} [Semiring R] [TopologicalSpace R]
    [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module R E] [ContinuousSMul R E]
    (s : Set R) (b w : E) : Tendsto (fun t : R => b + t • w) (𝓝[s] 0) (𝓝 b) :=
  tendsto_nhdsWithin_of_tendsto_nhds <| by
    simpa using tendsto_const_nhds.add ((tendsto_id (x := 𝓝 (0 : R))).smul_const w)

end TauCeti
