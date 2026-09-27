/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable

/-!
# Connecting orbits of a real flow

A periodic orbit with a forward or backward limit is constant. A nonconstant orbit with either
limit is therefore injectively parametrized by time. In particular, an orbit connecting distinct
backward and forward limits has the freeness needed to divide parametrized Morse trajectories by
time translation when constructing their moduli spaces.

The argument uses only continuity of the flow and uniqueness of limits, so it also applies to
connecting trajectories in other dynamical systems. The trajectory-space interpretation follows
M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 2.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α] [T1Space α]
  {φ : _root_.Flow ℝ α} {p q x : α}

/-- An orbit connecting distinct backward and forward limits has a free time parameter. -/
theorem orbit_injective_of_ne_of_mem_unstableSet_inter_stableSet
    (hpq : p ≠ q) (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    Function.Injective (fun t : ℝ => φ t x) := by
  by_cases hxq : x = q
  · apply orbit_injective_of_mem_unstableSet_of_ne hx.1
    intro hxp
    exact hpq (hxp.symm.trans hxq)
  · exact orbit_injective_of_mem_stableSet_of_ne hx.2 hxq

end Flow

end
