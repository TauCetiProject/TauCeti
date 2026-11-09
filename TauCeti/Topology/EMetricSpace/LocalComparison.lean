/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.EMetricSpace.Basic

/-!
# Completeness from local comparison of extended metrics

Completeness transfers from a reference extended metric to a target extended metric when the
identity is continuous and every target Cauchy sequence is reference Cauchy. A local upper
bound on reference distances on each target unit ball suffices for the Cauchy hypothesis.
The comparison constant may depend on the center, and infinite distances are permitted.
A single center also suffices when all target distances to it are finite and comparison
holds on every finite ball. These criteria apply to complete Ricci-flow time slices.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace TauCeti

open Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*}

/-- A target extended metric is complete if the identity from a complete reference extended
metric is continuous and every target Cauchy sequence is reference Cauchy. -/
theorem completeSpace_of_continuous_cauchySeq
    (d₀ d₁ : PseudoEMetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hcontinuous : @Continuous X X d₀.toUniformSpace.toTopologicalSpace
      d₁.toUniformSpace.toTopologicalSpace id)
    (hcauchy : ∀ u : ℕ → X, @CauchySeq X ℕ d₁.toUniformSpace _ u →
      @CauchySeq X ℕ d₀.toUniformSpace _ u) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : PseudoEMetricSpace X := d₁
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hlimit : ∃ x, Tendsto u atTop
      (@nhds X d₀.toUniformSpace.toTopologicalSpace x) := by
    let : PseudoEMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    exact cauchySeq_tendsto_of_complete (hcauchy u hu)
  obtain ⟨x, hx⟩ := hlimit
  exact ⟨x, (@Continuous.tendsto X X d₀.toUniformSpace.toTopologicalSpace
    d₁.toUniformSpace.toTopologicalSpace id hcontinuous x).comp hx⟩

/-- If the reference extended metric is complete, the identity to the target is continuous,
and reference distances are bounded by a finite multiple of target distances on each closed
target unit ball, then the target extended metric is complete. -/
theorem completeSpace_of_continuous_local_edist_bound
    (d₀ d₁ : PseudoEMetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hcontinuous : @Continuous X X d₀.toUniformSpace.toTopologicalSpace
      d₁.toUniformSpace.toTopologicalSpace id)
    (hcompare : ∀ p : X, ∃ C : ℝ≥0, ∀ x y : X,
      d₁.edist x p ≤ 1 → d₁.edist y p ≤ 1 →
      d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  apply completeSpace_of_continuous_cauchySeq d₀ d₁ hcomplete hcontinuous
  intro u hu
  let : PseudoEMetricSpace X := d₁
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  have huR : ∀ n ≥ N₀, d₁.edist (u n) (u N₀) ≤ 1 := fun n hn ↦ (hN₀ n hn).le
  obtain ⟨C, hC⟩ := hcompare (u N₀)
  have hucauchy := EMetric.cauchySeq_iff.mp hu
  let : PseudoEMetricSpace X := d₀
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hucauchy (ε / C) (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
  refine ⟨max N₀ N, fun m hm n hn ↦ ?_⟩
  apply lt_of_le_of_lt (hC _ _ (huR m ((le_max_left _ _).trans hm))
    (huR n ((le_max_left _ _).trans hn)))
  exact ENNReal.mul_lt_of_lt_div' (hN m ((le_max_right _ _).trans hm)
    n ((le_max_right _ _).trans hn))

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
  intro q
  obtain ⟨C, hC⟩ := hcompare (1 + (d₁.edist q p).toNNReal)
  refine ⟨C, fun x y hx hy ↦ hC x y ?_ ?_⟩
  · simpa only [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal (hfinite q)] using
      (d₁.edist_triangle x q p).trans (add_le_add hx le_rfl)
  · simpa only [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal (hfinite q)] using
      (d₁.edist_triangle y q p).trans (add_le_add hy le_rfl)

end TauCeti
