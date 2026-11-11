/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Neighborhoods of a point times a relative neighborhood

In a product of pseudometric spaces, a property holds eventually for the product filter
`𝓝 x ×ˢ 𝓝[s] t` exactly when it holds on a box of points `(y, τ)` with `dist y x < δ`, `τ ∈ s`
and `dist τ t < δ` (`Metric.eventually_nhds_prod_nhdsWithin_iff`). This is the form of
`Metric.eventually_nhds_prod_iff` in which the second filter is also given by a distance bound,
as used for functions of a space variable and a time variable restricted to an interval.
-/

public section

open Set Filter
open scoped Topology

namespace Metric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A property holds eventually near `x` and near `t` within `s` if and only if it holds on a box
`dist y x < δ`, `τ ∈ s`, `dist τ t < δ`. -/
theorem eventually_nhds_prod_nhdsWithin_iff {P : X × Y → Prop} {x : X} {s : Set Y} {t : Y} :
    (∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, P p) ↔
      ∃ δ > 0, ∀ y, dist y x < δ → ∀ τ ∈ s, dist τ t < δ → P (y, τ) := by
  rw [← nhdsWithin_univ, ← nhdsWithin_prod_eq, eventually_nhdsWithin_iff, eventually_nhds_iff]
  simp only [Prod.forall, Prod.dist_eq, max_lt_iff, mem_prod, mem_univ, true_and]
  exact exists_congr fun δ ↦ and_congr_right fun _ ↦ ⟨fun h y hy τ hτ hτt ↦ h y τ ⟨hy, hτt⟩ hτ,
    fun h y τ hyτ hτ ↦ h y hyτ.1 τ hτ hyτ.2⟩

end Metric
