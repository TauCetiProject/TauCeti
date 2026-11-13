/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Indicator

/-!
# Continuity of indicator functions away from the frontier

The indicator of a set `s` of a function continuous on the interior of `s` is continuous at every
point off the frontier of `s` (`ContinuousOn.continuousAt_indicator`), hence continuous on every
set disjoint from the frontier. Applied to a spectrum, this is the continuity of the indicator
that the continuous functional calculus needs to define a spectral projection.

## Main results

* `ContinuousOn.continuousOn_mulIndicator_of_disjoint_frontier`,
  `ContinuousOn.continuousOn_indicator_of_disjoint_frontier`: the indicator `s.indicator f` is
  continuous on every set disjoint from `frontier s`.
-/

public section

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [One β] {f : α → β}
  {s t : Set α}

/-- The multiplicative indicator `s.mulIndicator f` of a function continuous on the interior of `s`
is continuous on every set disjoint from the frontier of `s`. -/
@[to_additive /-- The indicator `s.indicator f` of a function continuous on the interior of `s` is
continuous on every set disjoint from the frontier of `s`. -/]
theorem ContinuousOn.continuousOn_mulIndicator_of_disjoint_frontier
    (hf : ContinuousOn f (interior s)) (ht : Disjoint (frontier s) t) :
    ContinuousOn (s.mulIndicator f) t := fun _ hx ↦
  (hf.continuousAt_mulIndicator (ht.notMem_of_mem_right hx)).continuousWithinAt
