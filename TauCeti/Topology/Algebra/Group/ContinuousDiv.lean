/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Neighbourhoods given by quotients of a continuous map

If a group-valued map `f` is continuous at `x` and `V` is a neighbourhood of `1`, the points `z`
with `f z / f x ∈ V` form a neighbourhood of `x`. Additively, the points with `f z - f x ∈ V`, for
a neighbourhood `V` of `0`, form a neighbourhood of `x`. Assigning such a neighbourhood to every
point gives a gauge, for instance in the construction of Riemann-sum integrals.

## Main results

* `ContinuousAt.setOf_div_mem_nhds`: `{z | f z / f x ∈ V} ∈ 𝓝 x`.
* `ContinuousAt.setOf_sub_mem_nhds`: `{z | f z - f x ∈ V} ∈ 𝓝 x`.
-/

public section

open Filter Topology

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G] [ContinuousDiv G]

/-- If `f` is continuous at `x` and `V` is a neighbourhood of `1`, the points `z` with
`f z / f x ∈ V` form a neighbourhood of `x`. -/
@[to_additive /-- If `f` is continuous at `x` and `V` is a neighbourhood of `0`, the points `z`
with `f z - f x ∈ V` form a neighbourhood of `x`. -/]
theorem ContinuousAt.setOf_div_mem_nhds {f : X → G} {x : X} (hf : ContinuousAt f x) {V : Set G}
    (hV : V ∈ 𝓝 1) : {z | f z / f x ∈ V} ∈ 𝓝 x := by
  have := hf.tendsto.div' (tendsto_const_nhds : Tendsto (fun _ ↦ f x) (𝓝 x) (𝓝 (f x)))
  rw [div_self'] at this
  exact this hV
