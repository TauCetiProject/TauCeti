/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Topology.Piecewise

/-!
# Continuity of indicator functions away from the frontier

The indicator function `Ω.indicator f` of a continuous function `f` can only fail to be
continuous at points of the frontier of `Ω`. So it is continuous on every set disjoint from that
frontier. Applied to a set `s` such as the spectrum of an operator, this is what makes a spectral
projection `𝟙_Ω(T)` accessible to the continuous functional calculus when `∂Ω` avoids the
spectrum of `T`.

## Main results

* `ContinuousOn.indicator_of_disjoint_frontier`: `Ω.indicator f` is continuous on any set `s`
  on which `f` is continuous and which is disjoint from the frontier of `Ω`.
-/

public section

open Set

variable {α M : Type*} [TopologicalSpace α] [TopologicalSpace M] [Zero M]

/-- The indicator function `Ω.indicator f` is continuous on every set `s` on which `f` is
continuous and which avoids the frontier of `Ω`. -/
theorem ContinuousOn.indicator_of_disjoint_frontier {f : α → M} {Ω s : Set α}
    (hf : ContinuousOn f s) (h : Disjoint s (frontier Ω)) : ContinuousOn (Ω.indicator f) s := by
  classical
  rw [← piecewise_eq_indicator]
  exact ContinuousOn.piecewise (fun a ha ↦ (h.notMem_of_mem_left ha.1 ha.2).elim)
    (hf.mono inter_subset_left) continuousOn_const
