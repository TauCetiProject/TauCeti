/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Topology.Path.Extend.Ioo
public import TauCeti.Analysis.SpecialFunctions.Sigmoid

/-!
# Connecting orbits of a real flow

Time translation on connecting points defines `Flow.connectingOrbitSetoid`, with no separation
assumption on the phase space. Its quotient represents unparametrized connecting orbits.

A periodic orbit with a forward or backward limit is constant. A nonconstant orbit with either
limit is therefore injectively parametrized by time. In particular, an orbit connecting distinct
backward and forward limits has the freeness needed to divide parametrized Morse trajectories by
time translation when constructing their moduli spaces.

The argument uses only continuity of the flow and uniqueness of limits, so it also applies to
connecting trajectories in other dynamical systems. The trajectory-space interpretation follows
M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 2.

A point `y` whose trajectory tends to `p` in backward time and to `q` in forward time traces a path
from `p` to `q`, `Flow.connectingPath`: the trajectory `t ↦ φ t y`, read along the
logit `s ↦ log (s / (1 - s))`, which reparametrises the open unit interval by the real line, and
completed by its limits at the two ends. Its homotopy class is what parallel transport in a local
coefficient system needs, for instance for Morse boundaries with twisted coefficients.
-/

public section

open Filter Set Topology

namespace Flow

section OrbitRelation

variable {E : Type*} [TopologicalSpace E] {φ : _root_.Flow ℝ E} {p q : E}

/-- Time translation on connecting points, obtained by restricting the ambient orbit relation.
The topology on its quotient is the quotient of the connecting set's subspace topology. -/
def connectingOrbitSetoid (φ : _root_.Flow ℝ E) (p q : E) :
    Setoid ↥(unstableSet φ p ∩ stableSet φ q) :=
  (@AddAction.orbitRel ℝ E _ φ.toAddAction).comap Subtype.val

/-- Connecting points are related exactly when one is a time translate of the other. -/
@[simp]
theorem connectingOrbitSetoid_apply
    (x y : ↥(unstableSet φ p ∩ stableSet φ q)) :
    connectingOrbitSetoid φ p q x y ↔ ∃ t : ℝ, φ t y.val = x.val :=
  Iff.rfl

end OrbitRelation

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

section ConnectingPath

variable {α : Type*} [TopologicalSpace α] {φ : _root_.Flow ℝ α} {p q y : α}

/-- **The path traced by a connecting trajectory.** If the trajectory of `y` tends to `p` in
backward time and to `q` in forward time, then it traces a path from `p` to `q`: at `s ∈ (0, 1)` it
passes through `φ (log (s / (1 - s))) y` (`Flow.connectingPath_apply_of_mem_Ioo`), and its ends
are the two limits. -/
noncomputable def connectingPath (hp : y ∈ unstableSet φ p) (hq : y ∈ stableSet φ q) : Path p q :=
  Path.ofContinuousOnIoo zero_lt_one
    ((φ.continuous continuous_id continuous_const).comp_continuousOn
      Real.continuousOn_log_div_one_sub)
    ((mem_unstableSet.1 hp).comp Real.tendsto_log_div_one_sub_nhdsGT_zero)
    ((mem_stableSet.1 hq).comp Real.tendsto_log_div_one_sub_nhdsLT_one)

/-- On the interior of the unit interval, the path traced by a connecting trajectory is the
trajectory at time `log (s / (1 - s))`. -/
@[simp]
theorem connectingPath_apply_of_mem_Ioo (hp : y ∈ unstableSet φ p) (hq : y ∈ stableSet φ q)
    {s : unitInterval} (hs : s ∈ Ioo (0 : unitInterval) 1) :
    connectingPath hp hq s = φ (Real.log (s / (1 - s))) y := by
  rw [connectingPath, Path.ofContinuousOnIoo_apply_of_mem_Ioo _ _ _ _ hs]
  simp [AffineMap.lineMap_apply_ring]

/-- The path traced by a connecting trajectory passes through the point `y` defining it, at the
middle of the unit interval. -/
theorem connectingPath_apply_half (hp : y ∈ unstableSet φ p) (hq : y ∈ stableSet φ q) :
    connectingPath hp hq ⟨1 / 2, by norm_num, by norm_num⟩ = y := by
  rw [connectingPath_apply_of_mem_Ioo hp hq
    (by constructor <;> (rw [← Subtype.coe_lt_coe]; norm_num))]
  norm_num

end ConnectingPath

end Flow

end
