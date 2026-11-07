/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Compactness.Compact

/-!
# Positive lower bounds for periods of a flow

For a continuous real flow, positive return times are locally bounded away from zero near every
nonstationary point. Consequently they have a uniform positive lower bound on any compact set
without stationary points. This includes all covered closed orbits meeting that set, not merely
primitive ones, and requires neither differentiability nor nondegeneracy.

The local argument uses an interval of times at which nearby points do not return. A sufficiently
small period would have an integer multiple in that interval, a contradiction. Compactness then
makes the local bounds uniform. This supplies the period bound used before proving finiteness of
isolated closed orbits in an action window.
-/

public section

open Set Topology

namespace Flow

variable {X : Type*} [TopologicalSpace X] [T2Space X] (ϕ : Flow ℝ X)

/-- Near a nonstationary point, positive return times have a common positive lower bound. -/
theorem exists_pos_period_le_nhds {x : X} (hx : ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ T > 0, ϕ T y = y → ε ≤ T := by
  obtain ⟨s, hs⟩ := hx
  have hopen : IsOpen {p : ℝ × X | ϕ p.1 p.2 ≠ p.2} :=
    isOpen_ne_fun ϕ.cont' continuous_snd
  obtain ⟨u, hu, U, hU, hsub⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε, hε, U, hU, fun y hy T hT hfix ↦ ?_⟩
  by_contra h
  have hTε : T < ε := lt_of_not_ge h
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

/-- Positive return times on a compact set without stationary points are uniformly bounded away
from zero. The compact set need not be invariant under the flow. -/
theorem exists_pos_period_le_of_isCompact {K : Set X} (hK : IsCompact K)
    (hmove : ∀ x ∈ K, ∃ s, ϕ s x ≠ x) :
    ∃ ε > 0, ∀ x ∈ K, ∀ T > 0, ϕ T x = x → ε ≤ T := by
  classical
  choose ε hε U hU hbound using fun x : K ↦
    ϕ.exists_pos_period_le_nhds (hmove x x.2)
  obtain ⟨c, hc⟩ := hK.elim_nhds_subcover' (fun x hx ↦ U ⟨x, hx⟩)
    (fun x hx ↦ hU ⟨x, hx⟩)
  -- A finite family of positive local bounds admits a common positive lower bound.
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, ∀ x ∈ c, r < ε x :=
    c.eventually_all.mpr fun x _ ↦ eventually_lt_nhds (hε x)
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall.exists_gt
  refine ⟨δ, hδ, fun x hx T hT hfix ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hc hx)
  exact (hδsmall y hy).le.trans (hbound y x hxy T hT hfix)

end Flow
