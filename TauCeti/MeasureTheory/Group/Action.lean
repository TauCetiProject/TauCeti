/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to a
measurable set that is invariant up to null sets is again invariant
(`SMulInvariantMeasure.restrict`), for a transitive isometric action all balls of one radius have
the same invariant measure (`measure_ball_eq_measure_ball`), and on a finite measure space with
measurable singletons every atom has a finite orbit (`finite_orbit_of_measure_singleton_ne_zero`).

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

/-- The restriction of an invariant measure to a measurable set that is invariant up to null
sets is invariant. -/
theorem SMulInvariantMeasure.restrict [SMulInvariantMeasure G X μ]
    {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (g • ·) ⁻¹' u =ᵐ[μ] u) :
    SMulInvariantMeasure G X (μ.restrict u) :=
  ⟨fun g v hv => by
    rw [Measure.restrict_apply' hum, Measure.restrict_apply' hum,
      ← SMulInvariantMeasure.measure_preimage_smul g (hv.inter hum), preimage_inter]
    exact measure_congr (ae_eq_set_inter .rfl (huinv g).symm)⟩

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

section Orbit

/-- If every `g • ·` preserves a finite measure on a space with measurable singletons, any point of
nonzero singleton measure has a finite orbit. -/
theorem finite_orbit_of_measure_singleton_ne_zero {G α : Type*} [SMul G α]
    {_ : MeasurableSpace α} [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    [SMulInvariantMeasure G α μ] {x : α} (hx : μ {x} ≠ 0) :
    Finite (MulAction.orbit G x) := by
  rw [Set.finite_coe_iff]
  by_contra hinf
  refine measure_ne_top μ (MulAction.orbit G x)
    ((Set.not_finite.mp hinf).meas_eq_top ⟨μ {x}, hx, ?_⟩)
  rintro _ ⟨g, rfl⟩
  -- `{x}` lies in the preimage of `{g • x}` under `g • ·`, which has the same measure
  rw [← SMulInvariantMeasure.measure_preimage_smul g (measurableSet_singleton (g • x))]
  exact measure_mono (by simp)

end Orbit

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
    μ (((g * h) • s) ∆ s) ≤ μ ((g • s) ∆ s) + μ ((h • s) ∆ s) :=
  calc
    μ (((g * h) • s) ∆ s) = μ ((g • (h • s)) ∆ s) := by rw [mul_smul]
    _ ≤ μ ((g • (h • s)) ∆ (g • s)) + μ ((g • s) ∆ s) := measure_symmDiff_le _ (g • s) _
    _ = μ ((h • s) ∆ s) + μ ((g • s) ∆ s) := by rw [measure_smul_symmDiff_smul]
    _ = μ ((g • s) ∆ s) + μ ((h • s) ∆ s) := add_comm _ _

/-- Subadditivity of `μ ((g +ᵥ s) ∆ s)` along a list sum in an additive group `A`. -/
theorem measure_list_sum_vadd_symmDiff_le {A X : Type*} [AddGroup A] [AddAction A X]
    [MeasurableSpace X] (μ : Measure X) [VAddInvariantMeasure A X μ] (L : List A) (s : Set X) :
    μ ((L.sum +ᵥ s) ∆ s) ≤ (L.map fun g ↦ μ ((g +ᵥ s) ∆ s)).sum :=
  L.le_sum_of_subadditive (fun g ↦ μ ((g +ᵥ s) ∆ s)) (by simp) fun g h ↦
    measure_add_vadd_symmDiff_le μ g h s

/-- Subadditivity of `μ ((g • s) ∆ s)` along a list product in `G`. -/
@[to_additive existing]
theorem measure_list_prod_smul_symmDiff_le (L : List G) (s : Set X) :
    μ ((L.prod • s) ∆ s) ≤ (L.map fun g ↦ μ ((g • s) ∆ s)).sum :=
  L.apply_prod_le_sum_map (fun g ↦ μ ((g • s) ∆ s)) (by simp) fun g h ↦
    measure_mul_smul_symmDiff_le μ g h s

end SMulSymmDiff

end MeasureTheory
