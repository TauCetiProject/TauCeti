/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to an
exactly invariant measurable set is again invariant (`SMulInvariantMeasure.restrict`), for a
transitive isometric action all balls of one radius have the same invariant measure
(`measure_ball_eq_measure_ball`), and on a finite measure space with measurable singletons any
atom has a finite orbit (`finite_orbit_of_measure_singleton_ne_zero`), so under a group action its
stabilizer has finite index (`finiteIndex_stabilizer_of_measure_singleton_ne_zero`). Every linear
action on a finite-dimensional real space has measurable translations
(`measurableConstSMul_of_finiteDimensional`).
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

section Orbit

/-- Under a measure-preserving monoid action on a finite measure space with measurable singletons,
any point of nonzero singleton measure has a finite orbit. -/
@[to_additive finite_addOrbit_of_measure_singleton_ne_zero /-- Under a measure-preserving additive
monoid action on a finite measure space with measurable singletons, any point of nonzero singleton
measure has a finite orbit. -/]
theorem finite_orbit_of_measure_singleton_ne_zero {M α : Type*} [Monoid M] [MulAction M α]
    {_ : MeasurableSpace α} [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    [SMulInvariantMeasure M α μ] {x : α} (hx : μ {x} ≠ 0) :
    Finite (MulAction.orbit M x) := by
  rw [Set.finite_coe_iff]
  by_contra hinf
  refine measure_ne_top μ (MulAction.orbit M x)
    ((Set.not_finite.mp hinf).meas_eq_top ⟨μ {x}, hx, ?_⟩)
  rintro _ ⟨m, rfl⟩
  rw [← SMulInvariantMeasure.measure_preimage_smul m (measurableSet_singleton (m • x))]
  exact measure_mono (Set.singleton_subset_iff.mpr rfl)

/-- Under a measure-preserving group action on a finite measure space with measurable singletons,
the stabilizer of any point of nonzero singleton measure has finite index. -/
@[to_additive finiteIndex_addStabilizer_of_measure_singleton_ne_zero /-- Under a measure-preserving
additive group action on a finite measure space with measurable singletons, the stabilizer of any
point of nonzero singleton measure has finite index. -/]
theorem finiteIndex_stabilizer_of_measure_singleton_ne_zero {G α : Type*} [Group G] [MulAction G α]
    {_ : MeasurableSpace α} [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    [SMulInvariantMeasure G α μ] {x : α} (hx : μ {x} ≠ 0) :
    (MulAction.stabilizer G x).FiniteIndex := by
  have : Finite (MulAction.orbit G x) := finite_orbit_of_measure_singleton_ne_zero hx
  have : Finite (G ⧸ MulAction.stabilizer G x) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G x)
  exact Subgroup.finiteIndex_of_finite_quotient

end Orbit

section Linear

variable {G E : Type*} [Monoid G] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [DistribMulAction G E] [SMulCommClass G ℝ E]

/-- Every linear action on a finite-dimensional real space has measurable translations. -/
theorem measurableConstSMul_of_finiteDimensional : MeasurableConstSMul G E :=
  ⟨fun g => (LinearMap.continuous_of_finiteDimensional
    (DistribMulAction.toModuleEnd ℝ E g)).measurable⟩

end Linear

end MeasureTheory
