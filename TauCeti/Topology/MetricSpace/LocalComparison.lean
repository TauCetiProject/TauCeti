/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Connected.Clopen

/-!
# Completeness from local comparison of extended metrics

Suppose the identity from a complete reference topology to a target topology is continuous.
If reference distances are bounded above by a finite multiple of target distances on
each finite target ball, the target is complete. The comparison is local, its constants
may depend on the center and radius, and infinite distances are permitted. A second
version uses only one center when distances to it are finite.
This transfers completeness to time slices in complete pointed Ricci-flow limits.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace TauCeti

open Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*}

/-- A local upper bound on reference distances transfers Cauchy sequences. Continuity of the
identity transfers their reference limits back to the target topology, so a reverse distance
bound and ball containment are unnecessary. -/
theorem completeSpace_of_continuous_local_edist_bound
    (d₀ d₁ : PseudoEMetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hcontinuous : @Continuous X X d₀.toUniformSpace.toTopologicalSpace
      d₁.toUniformSpace.toTopologicalSpace id)
    (hcompare : ∀ p : X, ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₁.edist x p ≤ R → d₁.edist y p ≤ R →
      d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : PseudoEMetricSpace X := d₁
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  have huR : ∀ n ≥ N₀, d₁.edist (u n) (u N₀) ≤ (1 : ℝ≥0) :=
    fun n hn ↦ (hN₀ n hn).le
  obtain ⟨C, hC⟩ := hcompare (u N₀) 1
  have hucauchy := EMetric.cauchySeq_iff.mp hu
  have hlimit : ∃ x, Tendsto u atTop
      (@nhds X d₀.toUniformSpace.toTopologicalSpace x) := by
    let : PseudoEMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    apply cauchySeq_tendsto_of_complete
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hucauchy (ε / C) (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
    refine ⟨max N₀ N, fun m hm n hn ↦ ?_⟩
    apply lt_of_le_of_lt (hC _ _ (huR m ((le_max_left _ _).trans hm))
      (huR n ((le_max_left _ _).trans hn)))
    exact ENNReal.mul_lt_of_lt_div' (hN m ((le_max_right _ _).trans hm)
      n ((le_max_right _ _).trans hn))
  obtain ⟨x, hx⟩ := hlimit
  exact ⟨x, (@Continuous.tendsto X X d₀.toUniformSpace.toTopologicalSpace
    d₁.toUniformSpace.toTopologicalSpace id hcontinuous x).comp hx⟩

/-- A single center suffices when every target distance to it is finite. -/
theorem completeSpace_of_continuous_local_edist_bound_at_basepoint
    (d₀ d₁ : PseudoEMetricSpace X) (p : X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hcontinuous : @Continuous X X d₀.toUniformSpace.toTopologicalSpace
      d₁.toUniformSpace.toTopologicalSpace id)
    (hfinite : ∀ x : X, d₁.edist x p ≠ ∞)
    (hcompare : ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₁.edist x p ≤ R → d₁.edist y p ≤ R →
      d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  apply completeSpace_of_continuous_local_edist_bound d₀ d₁ hcomplete hcontinuous
  intro q R
  obtain ⟨C, hC⟩ := hcompare (R + (d₁.edist q p).toNNReal)
  refine ⟨C, fun x y hx hy ↦ hC x y ?_ ?_⟩
  · simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite q)] using
      (d₁.edist_triangle x q p).trans (add_le_add hx le_rfl)
  · simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite q)] using
      (d₁.edist_triangle y q p).trans (add_le_add hy le_rfl)

end TauCeti
