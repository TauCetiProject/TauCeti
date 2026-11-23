/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to a
measurable set that is invariant up to null sets is again invariant
(`SMulInvariantMeasure.restrict`), for a transitive isometric action all balls of one radius have
the same invariant measure (`measure_ball_eq_measure_ball`), and on a finite measure space with
measurable singletons every atom has a finite orbit (`finite_orbit_of_measure_singleton_ne_zero`).
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

end MeasureTheory
