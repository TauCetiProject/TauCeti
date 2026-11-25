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

The local bound applies to families of additive subgroups of times with a locally excluded
time. Local lower bounds for positive times give one uniform bound near a compact set. These
results also apply to domain-valid returns of maximal flows.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- If a time is excluded from the subgroups of return times near a given time and point,
positive members of the subgroups near that point have a common positive lower bound. -/
theorem exists_pos_period_le_nhds_of_eventually_not_mem {X : Type*} [TopologicalSpace X]
    {P : X → AddSubgroup ℝ} {s : ℝ} {x : X}
    (hne : ∀ᶠ p : ℝ × X in 𝓝 (s, x), p.1 ∉ P p.2) :
    ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0, T ∈ P y → ε ≤ T := by
  obtain ⟨u, hu, U, hU, hsub⟩ := mem_nhds_prod_iff.mp hne
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε, hε, U, hU, fun y hy T hT hmem ↦ ?_⟩
  by_contra h
  -- An integer multiple of a small positive period lies within ε of the excluded time.
  obtain ⟨k, hk, -⟩ := existsUnique_zsmul_near_of_pos hT s
  rw [add_zsmul, one_zsmul] at hk
  have htime : k • T ∈ u := by
    apply hεu
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hk.1)]
    linarith [hk.2]
  exact (@hsub (k • T, y) ⟨htime, hy⟩) (zsmul_mem hmem k)

/-- Local positive lower bounds for times satisfying `P` at each point of a compact set
give a uniform positive lower bound on a neighborhood of the set. -/
theorem exists_pos_eventually_period_le_of_isCompact_of_locally {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {P : X → ℝ → Prop}
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0, P y T → ε ≤ T) :
    ∃ ε > 0, ∀ᶠ x in 𝓝ˢ K, ∀ T > 0, P x T → ε ≤ T := by
  have hbound : ∀ᶠ p : ℝ × X in 𝓝 0 ×ˢ 𝓝ˢ K, ∀ T > 0, P p.2 T → p.1 ≤ T := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    obtain ⟨ε, hε, U, hU, hbound⟩ := hlocal x hx
    filter_upwards [(eventually_lt_nhds hε).prod_mk hU] with p hp T hT hP
    exact hp.1.le.trans (hbound p.2 hp.2 T hT hP)
  exact hbound.curry.exists_gt

end TauCeti

namespace Flow

variable {X : Type*} [TopologicalSpace X] [T2Space X] (ϕ : Flow ℝ X)

/-- Near a nonstationary point, positive return times have a common positive lower bound. -/
theorem exists_pos_period_le_nhds {x : X} (hx : ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0, ϕ T y = y → ε ≤ T := by
  obtain ⟨s, hs⟩ := hx
  have hopen : IsOpen {p : ℝ × X | ϕ p.1 p.2 ≠ p.2} :=
    isOpen_ne_fun ϕ.cont' continuous_snd
  have hne : ∀ᶠ p : ℝ × X in 𝓝 (s, x), ϕ p.1 p.2 ≠ p.2 := hopen.mem_nhds hs
  have hnotMem : ∀ᶠ p : ℝ × X in 𝓝 (s, x), p.1 ∉ ϕ.periods p.2 :=
    hne.mono fun _ hp ↦ mt ϕ.mem_periods.mp hp
  simpa only [mem_periods] using TauCeti.exists_pos_period_le_nhds_of_eventually_not_mem hnotMem

/-- Positive return times near a compact set without stationary points are uniformly bounded
away from zero. The compact set need not have a compact neighborhood or be flow invariant. -/
theorem exists_pos_eventually_period_le_of_isCompact {K : Set X} (hK : IsCompact K)
    (hmove : ∀ x ∈ K, ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∀ᶠ x in 𝓝ˢ K, ∀ T > 0, ϕ T x = x → ε ≤ T :=
  TauCeti.exists_pos_eventually_period_le_of_isCompact_of_locally hK
    fun x hx ↦ ϕ.exists_pos_period_le_nhds (hmove x hx)

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
  apply hbound.self_of_nhdsSet (ϕ s c.point) hxK c.period c.period_pos
  simpa only [PeriodicTrajectory.period_vadd, PeriodicTrajectory.point_vadd] using
    (s +ᵥ c).apply_period

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
