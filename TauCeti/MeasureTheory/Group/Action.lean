/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to an
exactly invariant measurable set is again invariant (`SMulInvariantMeasure.restrict`), and for a
transitive isometric action all balls of one radius have the same invariant measure
(`measure_ball_eq_measure_ball`). Every linear action on a finite-dimensional real space has
measurable translations (`measurableConstSMul_of_finiteDimensional`).

For a group action preserving a measure `μ`, the symmetric difference of translated sets has
invariant measure (`measure_smul_symmDiff_smul`), inversion symmetry
(`measure_inv_smul_symmDiff_self`), and subadditivity under products and list words
(`measure_mul_smul_symmDiff_le`, `measure_list_prod_smul_symmDiff_le`), together with their
additive counterparts.
-/

public section

open Metric Set

open scoped Pointwise

namespace MeasureTheory

section Restrict

variable {G X : Type*} [SMul G X] {m : MeasurableSpace X} {μ : Measure X}

/-- The restriction of an invariant measure to an exactly invariant measurable set is
invariant. -/
theorem SMulInvariantMeasure.restrict [SMulInvariantMeasure G X μ]
    {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (g • ·) ⁻¹' u = u) :
    SMulInvariantMeasure G X (μ.restrict u) :=
  ⟨fun g v hv => by
    have h : (g • ·) ⁻¹' v ∩ u = (g • ·) ⁻¹' (v ∩ u) := by rw [preimage_inter, huinv g]
    rw [Measure.restrict_apply' hum, Measure.restrict_apply' hum, h,
      SMulInvariantMeasure.measure_preimage_smul g (hv.inter hum)]⟩

end Restrict

section Ball

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [MeasurableSpace X] [MulAction G X]
  [IsIsometricSMul G X] [MulAction.IsPretransitive G X]

/-- For a transitive isometric group action, an invariant measure gives all balls of the same
radius the same measure. -/
theorem measure_ball_eq_measure_ball (μ : Measure X) [SMulInvariantMeasure G X μ] (x y : X)
    (r : ℝ) :
    μ (ball x r) = μ (ball y r) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  rw [← Metric.smul_ball, measure_smul]

end Ball

section Linear

variable {G E : Type*} [Monoid G] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [DistribMulAction G E] [SMulCommClass G ℝ E]

/-- Every linear action on a finite-dimensional real space has measurable translations. -/
theorem measurableConstSMul_of_finiteDimensional : MeasurableConstSMul G E :=
  ⟨fun g => (LinearMap.continuous_of_finiteDimensional
    (DistribMulAction.toModuleEnd ℝ E g)).measurable⟩

end Linear

section SMulSymmDiff

open scoped symmDiff

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- A measure-preserving group action preserves the measure of symmetric differences. -/
@[to_additive (attr := simp)
/-- A measure-preserving additive group action preserves the measure of symmetric differences. -/]
theorem measure_smul_symmDiff_smul (g : G) (s t : Set X) :
    μ ((g • s) ∆ (g • t)) = μ (s ∆ t) := by
  rw [← smul_set_symmDiff, measure_smul]

/-- Translating a set by `g⁻¹` gives a symmetric difference of the same invariant measure as
translating by `g`. -/
@[to_additive
/-- Translating a set by `-g` gives a symmetric difference of the same invariant measure as
translating by `g`. -/]
theorem measure_inv_smul_symmDiff_self (g : G) (s : Set X) :
    μ ((g⁻¹ • s) ∆ s) = μ ((g • s) ∆ s) := by
  rw [measure_inv_smul_symmDiff, symmDiff_comm]

/-- Subadditivity of `μ ((g • s) ∆ s)` under group multiplication. -/
@[to_additive
/-- Subadditivity of `μ ((g +ᵥ s) ∆ s)` under group addition. -/]
theorem measure_mul_smul_symmDiff_le (g h : G) (s : Set X) :
    μ (((g * h) • s) ∆ s) ≤ μ ((h • s) ∆ s) + μ ((g • s) ∆ s) :=
  calc
    μ (((g * h) • s) ∆ s) = μ ((g • (h • s)) ∆ s) := by rw [mul_smul]
    _ ≤ μ ((g • (h • s)) ∆ (g • s)) + μ ((g • s) ∆ s) := measure_symmDiff_le _ (g • s) _
    _ = μ ((h • s) ∆ s) + μ ((g • s) ∆ s) := by rw [measure_smul_symmDiff_smul]

/-- Subadditivity of `μ ((g • s) ∆ s)` along a list product in `G`. -/
@[to_additive
/-- Subadditivity of `μ ((g +ᵥ s) ∆ s)` along a list sum in `G`. -/]
theorem measure_list_prod_smul_symmDiff_le (L : List G) (s : Set X) :
    μ ((L.prod • s) ∆ s) ≤ (L.map fun g ↦ μ ((g • s) ∆ s)).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons, add_comm] using
      (measure_mul_smul_symmDiff_le μ g L.prod s).trans (add_le_add_left ih _)

end SMulSymmDiff

end MeasureTheory
