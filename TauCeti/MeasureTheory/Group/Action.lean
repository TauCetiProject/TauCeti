/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
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
For a countable group, pushing forward a measure without atoms to the orbit space gives a measure
without atoms (`nullSingletonClass_map_quotientMk`).

For a monoid `G` carrying a right-invariant probability measure `μ`, such as normalized Haar
measure on a compact group, the law `μ.map (· • x)` of the orbit map at `x` is the same for all
points of an orbit (`map_smul_const_smul`), so for a transitive action it does not depend on the
point at all (`map_smul_const_eq_of_isPretransitive`). For a transitive action every
s-finite invariant measure `ν` equals `ν univ • μ.map (· • x)`
(`eq_measure_univ_smul_map_smul_const`), so any invariant probability measure equals this law.
This identifies, for instance, the uniform law on a sphere, which is invariant under rotations,
with the law of a Haar-random rotation of a fixed unit vector.

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

/-- **Points of the orbit space of a countable action are null.** If `G` is countable and `μ`
vanishes on points of a space with measurable singletons, then the pushforward of `μ` to the orbit
space of `G` vanishes on every point: the preimage of a point is an orbit, a countable set. This
applies to restrictions `μ.restrict s` to a fundamental domain, so a quotient measure has no atoms,
for instance at the elliptic points of a Fuchsian quotient. -/
instance nullSingletonClass_map_quotientMk {G α : Type*} [Group G] [MulAction G α] [Countable G]
    [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α} [NullSingletonClass μ] :
    NullSingletonClass (μ.map (Quotient.mk (MulAction.orbitRel G α))) where
  measure_singleton q := by
    induction q using Quotient.inductionOn with
    | h x =>
      have hpre : Quotient.mk (MulAction.orbitRel G α) ⁻¹' {Quotient.mk _ x} =
          MulAction.orbit G x := by
        ext y
        simp only [mem_preimage, mem_singleton_iff, Quotient.eq, MulAction.orbitRel_apply]
      have hc : (MulAction.orbit G x).Countable := countable_range _
      rw [Measure.map_apply measurable_quotient_mk''
        (measurableSet_quotient.mpr (hpre ▸ hc.measurableSet)), hpre]
      exact hc.measure_zero μ

end Orbit

section OrbitLaw

variable {G X : Type*} [Monoid G] [MulAction G X] [MeasurableSpace G] [MeasurableSpace X]
  [MeasurableMul G] [MeasurableSMul G X] (μ : Measure G) [μ.IsMulRightInvariant]

/-- Under a right-invariant measure on `G`, the law of the orbit map does not change when the base
point is moved within its orbit. -/
theorem map_smul_const_smul (g : G) (x : X) : μ.map (· • g • x) = μ.map (· • x) := by
  have h : (fun h : G ↦ h • g • x) = (· • x) ∘ (· * g) := funext fun h ↦ (mul_smul h g x).symm
  rw [h, ← Measure.map_map (measurable_smul_const x) (measurable_mul_const g),
    map_mul_right_eq_self]

/-- Under a right-invariant measure on `G` and a transitive action, the law of the orbit map is
independent of the base point. -/
theorem map_smul_const_eq_of_isPretransitive [MulAction.IsPretransitive G X] (x y : X) :
    μ.map (· • x) = μ.map (· • y) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  exact (map_smul_const_smul μ g x).symm

omit [MeasurableSMul G X] in
/-- **Uniqueness of invariant measures on a homogeneous space.** If `μ` is a right-invariant
probability measure on a monoid acting transitively on `X`, then every s-finite invariant measure on
`X` is its total mass times the law `μ.map (· • x)` of the orbit map at any point `x`. In
particular `X` carries at most one invariant probability measure, and if one exists it equals this
law. -/
theorem eq_measure_univ_smul_map_smul_const [MeasurableSMul₂ G X] [IsProbabilityMeasure μ]
    [MulAction.IsPretransitive G X] (ν : Measure X) [SFinite ν] [SMulInvariantMeasure G X ν]
    (x : X) : ν = ν univ • μ.map (· • x) := by
  ext s hs
  have hsmul : Measurable fun p : G × X ↦ p.1 • p.2 := measurable_smul
  -- Average the invariance `ν ((g • ·) ⁻¹' s) = ν s` over `g ∼ μ` and swap the integrals: for each
  -- `y`, the inner integral is the law of the orbit map at `y`, which does not depend on `y`.
  calc ν s = ∫⁻ _ : G, ν s ∂μ := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ g, ∫⁻ y, s.indicator (fun _ ↦ 1) (g • y) ∂ν ∂μ := by
      refine lintegral_congr fun g ↦ ?_
      rw [lintegral_indicator_const_comp (measurable_const_smul g) hs, one_mul,
        SMulInvariantMeasure.measure_preimage_smul g hs]
    _ = ∫⁻ y, ∫⁻ g, s.indicator (fun _ ↦ 1) (g • y) ∂μ ∂ν :=
      lintegral_lintegral_swap ((measurable_const.indicator hs).comp hsmul).aemeasurable
    _ = ∫⁻ _ : X, μ.map (· • x) s ∂ν := by
      refine lintegral_congr fun y ↦ ?_
      rw [map_smul_const_eq_of_isPretransitive μ x y,
        Measure.map_apply (measurable_smul_const y) hs,
        lintegral_indicator_const_comp (measurable_smul_const y) hs, one_mul]
    _ = (ν univ • μ.map (· • x)) s := by
      rw [lintegral_const, smul_apply, smul_eq_mul, mul_comm]

end OrbitLaw

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
