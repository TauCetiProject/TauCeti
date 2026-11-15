/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
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

section InvariantRepresentative

variable {G X E : Type*} [Group G] [Countable G] [MulAction G X] [MeasurableSpace X]
  [MeasurableConstSMul G X] {μ : Measure X} [SMulInvariantMeasure G X μ] [TopologicalSpace E]
  [TopologicalSpace.MetrizableSpace E] [Zero E]

/-- **Invariant representatives.** If `f` is almost everywhere strongly measurable and, for each
element `g` of a countable group of measure-preserving maps, `f (g • x) = f x` for almost every
`x`, then `f` agrees almost everywhere with a strongly measurable function `f'` satisfying
`f' (g • x) = f' x` for every `g` and every `x`. -/
theorem AEStronglyMeasurable.exists_stronglyMeasurable_forall_smul_eq {f : X → E}
    (hf : AEStronglyMeasurable f μ) (hinv : ∀ g : G, (fun x ↦ f (g • x)) =ᵐ[μ] f) :
    ∃ f' : X → E, StronglyMeasurable f' ∧ (∀ (g : G) (x : X), f' (g • x) = f' x) ∧
      f' =ᵐ[μ] f := by
  have hf₀ := hf.stronglyMeasurable_mk
  -- The points along whose orbit the representative `hf.mk f` is constant form a measurable,
  -- invariant set of full measure; `f'` is `hf.mk f` there and `0` elsewhere.
  set B : Set X := ⋂ g : G, {x | hf.mk f (g • x) = hf.mk f x} with hB_def
  have hmem (x : X) : x ∈ B ↔ ∀ g : G, hf.mk f (g • x) = hf.mk f x := by simp [hB_def]
  have hB : MeasurableSet B := .iInter fun g ↦
    (hf₀.comp_measurable (measurable_const_smul g)).measurableSet_eq_fun hf₀
  have hBsmul (g : G) {x : X} (hx : x ∈ B) : g • x ∈ B :=
    (hmem _).2 fun h ↦ by rw [smul_smul, (hmem x).1 hx, (hmem x).1 hx]
  have hBae : ∀ᵐ x ∂μ, x ∈ B := by
    simp only [hmem, ae_all_iff]
    intro g
    filter_upwards [(measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk,
      hinv g, hf.ae_eq_mk] with x h₁ h₂ h₃
    exact h₁.symm.trans (h₂.trans h₃)
  refine ⟨B.indicator (hf.mk f), hf₀.indicator hB, fun g x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ B
    · rw [indicator_of_mem (hBsmul g hx), indicator_of_mem hx, (hmem x).1 hx g]
    · have hgx : g • x ∉ B := fun h ↦ hx (by simpa using hBsmul g⁻¹ h)
      rw [indicator_of_notMem hgx, indicator_of_notMem hx]
  · filter_upwards [hBae, hf.ae_eq_mk] with x hx h
    rw [indicator_of_mem hx, h]

end InvariantRepresentative

end MeasureTheory
