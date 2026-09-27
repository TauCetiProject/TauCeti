/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable
-- Private: used only for the arithmetic progression tending to infinity.
import Mathlib.Order.Filter.AtTopBot.Archimedean

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

/-- A periodic flow orbit with a forward limit equals its limit. -/
theorem eq_of_mem_stableSet_of_periodic (hx : x ∈ stableSet φ q) {T : ℝ}
    (hT : T ≠ 0) (hper : Function.Periodic (fun t => φ t x) T) : x = q := by
  have hpos : ∃ T' : ℝ, 0 < T' ∧ Function.Periodic (fun t => φ t x) T' := by
    rcases lt_trichotomy T 0 with hneg | heq | hpositive
    · exact ⟨-T, neg_pos.mpr hneg, hper.neg⟩
    · exact (hT heq).elim
    · exact ⟨T, hpositive, hper⟩
  obtain ⟨T', hT', hper'⟩ := hpos
  have htend : Tendsto (fun n : ℕ => n • T') atTop atTop :=
    tendsto_id.atTop_nsmul_const hT'
  have hlim : Tendsto (fun n : ℕ => φ (n • T') x) atTop (𝓝 q) :=
    (mem_stableSet.mp hx).comp htend
  have hconst : (fun n : ℕ => φ (n • T') x) = fun _ => x := by
    funext n
    simpa only [φ.map_zero_apply] using (hper'.nsmul_eq n)
  have hlim' : Tendsto (fun _ : ℕ => x) atTop (𝓝 q) := by
    simpa only [hconst] using hlim
  exact tendsto_const_nhds_iff.mp hlim'

/-- A periodic flow orbit with a backward limit equals its limit. -/
theorem eq_of_mem_unstableSet_of_periodic (hx : x ∈ unstableSet φ q) {T : ℝ}
    (hT : T ≠ 0) (hper : Function.Periodic (fun t => φ t x) T) : x = q := by
  apply eq_of_mem_stableSet_of_periodic (φ := φ.reverse) (by simpa using hx) hT
  intro t
  simpa only [_root_.Flow.reverse_apply, neg_add_rev, add_comm] using (hper.neg (-t))

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
  exact hxq (eq_of_mem_stableSet_of_periodic hx (sub_ne_zero.mpr hne) hper)

/-- A nonconstant orbit that converges in backward time is injectively parametrized by time. -/
theorem orbit_injective_of_mem_unstableSet_of_ne
    (hx : x ∈ unstableSet φ q) (hxq : x ≠ q) :
    Function.Injective (fun t : ℝ => φ t x) := by
  have h := orbit_injective_of_mem_stableSet_of_ne (φ := φ.reverse) (by simpa using hx) hxq
  intro t u htu
  apply neg_injective
  apply h
  simpa only [_root_.Flow.reverse_apply, neg_neg] using htu

/-- An orbit connecting distinct backward and forward limits has a free time parameter. -/
theorem orbit_injective_of_mem_unstableSet_inter_stableSet
    [T2Space α]
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
