/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Translates of large multiples in an open cone

Let `Γ` be an open subset of a real topological vector space which is closed under
multiplication by positive reals, such as an open cone of frequencies in microlocal analysis.
If `ξ ∈ Γ`, then `Γ` contains `t • ξ + w` for every fixed `w` and all sufficiently large `t`:
writing `t • ξ + w = t • (ξ + t⁻¹ • w)`, the vector `ξ + t⁻¹ • w` tends to `ξ`.

## Main results

* `IsOpen.eventually_smul_add_mem`: an open set closed under positive scaling contains
  `t • ξ + w` for all large `t` whenever it contains `ξ`.
-/

public section

open Filter Topology

namespace IsOpen

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E]

/-- An open set `Γ` containing `ξ` and closed under multiplication by positive reals contains
`t • ξ + w` for all sufficiently large `t`, since `t • ξ + w = t • (ξ + t⁻¹ • w)` and
`ξ + t⁻¹ • w` tends to `ξ`. -/
theorem eventually_smul_add_mem {Γ : Set E} (hΓ : IsOpen Γ) {ξ : E} (hξΓ : ξ ∈ Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) (w : E) : ∀ᶠ t : ℝ in atTop, t • ξ + w ∈ Γ := by
  have hlim : Tendsto (fun t : ℝ => ξ + t⁻¹ • w) atTop (𝓝 ξ) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w)
  filter_upwards [hlim (hΓ.mem_nhds hξΓ), eventually_gt_atTop 0] with t ht ht0
  simpa [smul_add, smul_smul, ht0.ne'] using hcone t ht0 _ ht

end IsOpen
