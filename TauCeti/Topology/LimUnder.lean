/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Defs.Filter

import Mathlib.Order.Filter.Map

/-!
# Congruence for `Filter.limUnder`

Two functions that agree eventually along a filter induce the same pushed-forward filter and
therefore have equal `Filter.limUnder` limits, without requiring convergence or separation.

## Main results

* `Filter.limUnder_congr`: if `g₁ =ᶠ[l] g₂`, then `limUnder l g₁ = limUnder l g₂`.
-/

public section

open Filter

/-- Two eventually equal functions have equal `Filter.limUnder` limits. -/
theorem Filter.limUnder_congr {α β : Type*} {l : Filter α} [TopologicalSpace β] [Nonempty β]
    {g₁ g₂ : α → β} (h : g₁ =ᶠ[l] g₂) : limUnder l g₁ = limUnder l g₂ := by
  rw [limUnder, limUnder, Filter.map_congr h]
