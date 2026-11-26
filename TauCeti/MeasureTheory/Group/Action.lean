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
public import Mathlib.Probability.ConditionalProbability

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to a
measurable set that is invariant up to null sets is again invariant
(`SMulInvariantMeasure.restrict`), and so is the conditioned measure
(`SMulInvariantMeasure.cond`); for a measure-preserving action, invariance up to null sets
passes to every set almost everywhere equal to an almost invariant one
(`preimage_smul_ae_eq_self_of_ae_eq`); for a transitive isometric action all balls of one radius
have the same invariant measure (`measure_ball_eq_measure_ball`), and on a finite measure space with
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
-/

public section

open Metric Set

open scoped Pointwise ProbabilityTheory

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

/-- Conditioning an invariant measure on a measurable event that is invariant up to null sets gives
an invariant measure. -/
theorem SMulInvariantMeasure.cond [SMulInvariantMeasure G X μ] {u : Set X} (hum : MeasurableSet u)
    (huinv : ∀ g : G, (g • ·) ⁻¹' u =ᵐ[μ] u) : SMulInvariantMeasure G X μ[|u] := by
  have := SMulInvariantMeasure.restrict hum huinv
  -- `μ[|u]` is `(μ u)⁻¹ • μ.restrict u` by the definition of `ProbabilityTheory.cond`
  rw [ProbabilityTheory.cond]
  infer_instance

/-- For a measure-preserving action, a set almost everywhere equal to a set that is invariant up to
null sets under `g • ·` is also invariant up to null sets under `g • ·`. -/
theorem preimage_smul_ae_eq_self_of_ae_eq [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
    {s t : Set X} (hts : t =ᵐ[μ] s) {g : G} (hs : (g • ·) ⁻¹' s =ᵐ[μ] s) :
    (g • ·) ⁻¹' t =ᵐ[μ] t :=
  (((measurePreserving_smul g μ).quasiMeasurePreserving.preimage_ae_eq hts).trans hs).trans
    hts.symm

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

end MeasureTheory
