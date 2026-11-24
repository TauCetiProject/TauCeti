/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Limits of integer powers

In an Archimedean ordered field, for a base `b > 1` the integer powers `b ^ n` tend to `∞` as
`n → ∞` and to `0` as `n → -∞` along the integers. These are the scales `2^j`, `j ∈ ℤ`, of
homogeneous dyadic decompositions.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜] {b : 𝕜}

/-- For `b > 1`, `b ^ n → ∞` as `n → ∞` along the integers. -/
theorem tendsto_zpow_atTop_atTop_of_one_lt (hb : 1 < b) :
    Tendsto (fun n : ℤ ↦ b ^ n) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun x ↦ ?_
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x hb
  refine ⟨n, fun m hm ↦ hn.le.trans ?_⟩
  simpa only [zpow_natCast] using zpow_right_mono₀ hb.le hm

/-- For `b > 1`, `b ^ n → 0` as `n → -∞` along the integers. -/
theorem tendsto_zpow_atBot_nhds_zero_of_one_lt [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (hb : 1 < b) : Tendsto (fun n : ℤ ↦ b ^ n) atBot (𝓝 0) := by
  simpa only [Function.comp_def, zpow_neg, inv_inv, neg_neg] using
    tendsto_inv_atTop_zero.comp
      ((tendsto_zpow_atTop_atTop_of_one_lt hb).comp tendsto_neg_atBot_atTop)

end TauCeti
