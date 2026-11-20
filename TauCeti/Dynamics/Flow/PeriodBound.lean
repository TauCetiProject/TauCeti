/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
import Mathlib.Topology.Compactness.Compact

/-!
# Positive lower bounds for periods of a flow

For a continuous real flow, positive return times are locally bounded away from zero near every
nonstationary point. Consequently they have a uniform positive lower bound on any compact set
without stationary points. This includes all covered closed orbits meeting that set, not merely
primitive ones, and requires neither differentiability nor nondegeneracy.

This supplies the period bound used before proving finiteness of isolated closed orbits in an
action window.
-/

public section

open Set Topology

namespace Flow

variable {X : Type*} [TopologicalSpace X] [T2Space X] (ϕ : Flow ℝ X)

/-- Near a nonstationary point, positive return times have a common positive lower bound. -/
theorem exists_pos_period_le_nhds {x : X} (hx : ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0, ϕ T y = y → ε ≤ T := by
  -- The local argument uses an interval of times at which nearby points do not return. A
  -- sufficiently small period would have an integer multiple in that interval, a contradiction.
  obtain ⟨s, hs⟩ := hx
  have hopen : IsOpen {p : ℝ × X | ϕ p.1 p.2 ≠ p.2} :=
    isOpen_ne_fun ϕ.cont' continuous_snd
  obtain ⟨u, hu, U, hU, hsub⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε, hε, U, hU, fun y hy T hT hfix ↦ ?_⟩
  by_contra h
  -- An integer multiple of a small period lies within ε of the nonreturn time s.
  obtain ⟨k, hk, -⟩ := existsUnique_zsmul_near_of_pos hT s
  have hk' : (k : ℝ) * T ≤ s ∧ s < (k : ℝ) * T + T := by
    simpa only [zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, one_mul] using hk
  have htime : (k : ℝ) * T ∈ u := by
    apply hεu
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hk'.1)]
    linarith [hk'.2]
  have hreturn : ϕ ((k : ℝ) * T) y = y := by
    have hm := zsmul_mem (ϕ.mem_periods.mpr hfix) k
    simpa only [zsmul_eq_mul, mem_periods] using hm
  exact (@hsub ((k : ℝ) * T, y) ⟨htime, hy⟩) hreturn

/-- Positive return times near a compact set without stationary points are uniformly bounded
away from zero. The compact set need not have a compact neighborhood or be flow invariant. -/
theorem exists_pos_eventually_period_le_of_isCompact {K : Set X} (hK : IsCompact K)
    (hmove : ∀ x ∈ K, ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∀ᶠ x in 𝓝ˢ K, ∀ T > 0, ϕ T x = x → ε ≤ T := by
  have hbound : ∀ᶠ p : ℝ × X in 𝓝 0 ×ˢ 𝓝ˢ K,
      ∀ T > 0, ϕ T p.2 = p.2 → p.1 ≤ T := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    obtain ⟨ε, hε, U, hU, hbound⟩ := ϕ.exists_pos_period_le_nhds (hmove x hx)
    filter_upwards [(eventually_lt_nhds hε).prod_mk hU] with p hp T hT hfix
    exact hp.1.le.trans (hbound p.2 hp.2 T hT hfix)
  exact hbound.curry.exists_gt

/-- Closed orbits meeting a compact set without stationary points have periods uniformly bounded
away from zero. -/
theorem exists_pos_period_le_closedOrbit_of_isCompact {K : Set X} (hK : IsCompact K)
    (hmove : ∀ x ∈ K, ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∀ γ : ϕ.ClosedOrbit, (γ.support ∩ K).Nonempty → ε ≤ γ.period := by
  obtain ⟨ε, hε, hbound⟩ := ϕ.exists_pos_eventually_period_le_of_isCompact hK hmove
  refine ⟨ε, hε, fun γ ↦ γ.ind fun c hc ↦ ?_⟩
  obtain ⟨x, hx, hxK⟩ := hc
  rw [ClosedOrbit.support_mk, mem_orbit_iff] at hx
  obtain ⟨s, rfl⟩ := hx
  rw [ClosedOrbit.period_mk]
  exact hbound.self_of_nhdsSet (ϕ s c.point) hxK c.period c.period_pos (s +ᵥ c).apply_period

/-- On a compact space without stationary points, closed orbits of `ϕ` have periods uniformly
bounded away from zero. -/
theorem exists_pos_period_le_closedOrbit [CompactSpace X] (hmove : ∀ x, ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∀ γ : ϕ.ClosedOrbit, ε ≤ γ.period := by
  obtain ⟨ε, hε, hbound⟩ :=
    ϕ.exists_pos_period_le_closedOrbit_of_isCompact isCompact_univ fun x _ ↦ hmove x
  refine ⟨ε, hε, fun γ ↦ hbound γ (γ.ind fun c ↦ ⟨c.point, ?_, mem_univ _⟩)⟩
  rw [ClosedOrbit.support_mk]
  exact mem_orbit_self ϕ c.point

end Flow
