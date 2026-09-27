/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable
-- Private: used only for the arithmetic progression tending to infinity.
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Connecting orbits of a real flow

An orbit with a forward limit cannot be periodic unless it is constant. Consequently, a flow
orbit connecting distinct backward and forward limits is injectively parametrized by time. This
is the freeness needed to divide parametrized Morse trajectories by time translation when
constructing their moduli spaces.

The argument uses only continuity of the flow and uniqueness of limits, so it also applies to
connecting trajectories in other dynamical systems. The trajectory-space interpretation follows
M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 2.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α] [T2Space α]
  {φ : _root_.Flow ℝ α} {p q x : α}

/-- A periodic flow orbit with a forward limit equals its limit. A nonzero period can always be
replaced by a positive one; along its positive integer multiples the orbit has constant value. -/
theorem eq_of_periodic_of_mem_stableSet (hx : x ∈ stableSet φ q) {T : ℝ}
    (hT : T ≠ 0) (hper : Function.Periodic (fun t => φ t x) T) : x = q := by
  have hpos : ∃ T' : ℝ, 0 < T' ∧ Function.Periodic (fun t => φ t x) T' := by
    rcases lt_trichotomy T 0 with hneg | heq | hpositive
    · exact ⟨-T, neg_pos.mpr hneg, hper.neg⟩
    · exact (hT heq).elim
    · exact ⟨T, hpositive, hper⟩
  obtain ⟨T', hT', hper'⟩ := hpos
  have htend : Tendsto (fun n : ℕ => n • T') atTop atTop := by
    simpa only [nsmul_eq_mul] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hT'
  have hlim : Tendsto (fun n : ℕ => φ (n • T') x) atTop (𝓝 q) :=
    (mem_stableSet.mp hx).comp htend
  have hconst : (fun n : ℕ => φ (n • T') x) = fun _ => x := by
    funext n
    simpa only [zero_add, φ.map_zero_apply] using (hper'.nsmul n 0)
  have hlim' : Tendsto (fun _ : ℕ => x) atTop (𝓝 q) := by
    simpa only [hconst] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim'

/-- A nonconstant orbit that converges in forward time is injectively parametrized by time. -/
theorem orbit_injective_of_mem_stableSet_of_ne
    (hx : x ∈ stableSet φ q) (hxq : x ≠ q) :
    Function.Injective (fun t : ℝ => φ t x) := by
  intro t u htu
  by_contra hne
  have hper : Function.Periodic (fun v => φ v x) (t - u) := by
    intro v
    calc
      φ (v + (t - u)) x = φ (v - u) (φ t x) := by
        rw [← φ.map_add]
        congr 1
        ring
      _ = φ (v - u) (φ u x) := congrArg (φ (v - u)) htu
      _ = φ v x := by rw [← φ.map_add, sub_add_cancel]
  exact hxq (eq_of_periodic_of_mem_stableSet hx (sub_ne_zero.mpr hne) hper)

/-- An orbit connecting distinct backward and forward limits has a free time parameter. -/
theorem orbit_injective_of_mem_unstableSet_inter_stableSet
    (hpq : p ≠ q) (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    Function.Injective (fun t : ℝ => φ t x) := by
  apply orbit_injective_of_mem_stableSet_of_ne hx.2
  intro hxq
  have hqfixed : ∀ t, φ t q = q := fun t => fixed_of_mem_stableSet hx.2 t
  have hlim : Tendsto (fun _ : ℝ => q) atBot (𝓝 p) := by
    simpa only [hxq, hqfixed] using (mem_unstableSet.mp hx.1)
  exact hpq (tendsto_nhds_unique hlim tendsto_const_nhds)

end Flow

end
