/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Besicovitch covering: density points, subspaces and Lebesgue differentiation

For a null-measurable set `s`, the proportion of the complement `sᶜ` in a set of positive finite
measure is one minus the proportion of `s`. Consequently, if the proportion of `s` along
a family of such sets tends to `d`, that of `sᶜ` tends to `1 - d`; in particular `s` has density
one along the family exactly when `sᶜ` has density zero along it. This lets density arguments
estimate the complement, where measures add, and return to density-one points.

For a locally finite measure on a second-countable metric space with its Borel σ-algebra and the
Besicovitch covering property, Mathlib's density theorem
`Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet` identifies the limit of
`μ (s ∩ closedBall x r) / μ (closedBall x r)` almost everywhere for a measurable set.
We extend it to null-measurable sets and record its set form: a null-measurable set agrees almost
everywhere with its set of density-one points. That set is a canonical representative of the
`μ`-a.e. class of `s`, since it depends only on that class.

The Besicovitch covering property passes to subspaces (`Isometry.hasBesicovitchCovering`), so
an open subset of a finite-dimensional real normed space has it too. This lets differentiation
theorems apply to measures that are only locally finite on an open set, such as derivative
measures of functions of locally bounded variation. For such measures, the Besicovitch Vitali
family gives the Lebesgue differentiation theorem along concentric closed balls,
`Besicovitch.ae_tendsto_average_closedBall`.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory

namespace NullMeasurableSet

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- For a null-measurable set `s`, along sets of positive finite measure, if the proportion of
`s` tends to `d` then the proportion of `sᶜ` tends to `1 - d`. -/
theorem tendsto_measure_compl_inter_div (hs : NullMeasurableSet s μ) {l : Filter ι}
    {u : ι → Set α} (hu : ∀ᶠ i in l, μ (u i) ≠ 0 ∧ μ (u i) ≠ ∞) {d : ℝ≥0∞}
    (h : Tendsto (fun i => μ (s ∩ u i) / μ (u i)) l (𝓝 d)) :
    Tendsto (fun i => μ (sᶜ ∩ u i) / μ (u i)) l (𝓝 (1 - d)) := by
  refine (ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)).congr' ?_
  filter_upwards [hu] with i ⟨h0, htop⟩
  have hadd : μ (s ∩ u i) + μ (sᶜ ∩ u i) = μ (u i) := by
    rw [inter_comm s, inter_comm sᶜ, ← sdiff_eq, measure_inter_add_sdiff₀ _ hs]
  rw [← ENNReal.div_self h0 htop, ← ENNReal.sub_div (fun _ _ => h0), ← hadd,
    ENNReal.add_sub_cancel_left (measure_ne_top_of_subset inter_subset_right htop)]

/-- For a null-measurable set `s`, along sets of positive finite measure the proportion of `sᶜ`
tends to zero exactly when the proportion of `s` tends to one. -/
theorem tendsto_measure_compl_inter_div_iff (hs : NullMeasurableSet s μ) {l : Filter ι}
    {u : ι → Set α} (hu : ∀ᶠ i in l, μ (u i) ≠ 0 ∧ μ (u i) ≠ ∞) :
    Tendsto (fun i => μ (sᶜ ∩ u i) / μ (u i)) l (𝓝 0) ↔
      Tendsto (fun i => μ (s ∩ u i) / μ (u i)) l (𝓝 1) := by
  refine ⟨fun h => ?_, fun h => by simpa using hs.tendsto_measure_compl_inter_div hu h⟩
  simpa using hs.compl.tendsto_measure_compl_inter_div hu h

variable [MetricSpace α] [SecondCountableTopology α] [BorelSpace α] [HasBesicovitchCovering α]
  [IsLocallyFiniteMeasure μ]

/-- **Lebesgue's density theorem** for a null-measurable set `s`: at almost every point `x`, the
proportion of `s` in the closed ball around `x` tends to the value at `x` of the indicator of
`s`. This extends `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet` to null-measurable
sets. -/
theorem ae_tendsto_measure_inter_div (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
      (𝓝 (s.indicator 1 x)) := by
  have hmeas : ∀ x r, μ (s ∩ closedBall x r) = μ (toMeasurable μ s ∩ closedBall x r) :=
    fun x r => measure_congr (hs.toMeasurable_ae_eq.symm.inter (ae_eq_refl _))
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
    (measurableSet_toMeasurable μ s),
    indicator_ae_eq_of_ae_eq_set (f := (1 : α → ℝ≥0∞)) hs.toMeasurable_ae_eq]
    with x hx hxs
  simpa only [hmeas, hxs] using hx

/-- A null-measurable set agrees almost everywhere with its set of density points with
respect to `μ`, the points at which its proportion of closed balls tends to one. -/
theorem ae_eq_setOf_tendsto_measure_inter_div (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] {x | Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
      (𝓝 1)} := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hs.ae_tendsto_measure_inter_div] with x hx
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs, Pi.one_apply] at hx
    exact iff_of_true hxs hx
  · simp only [indicator_of_notMem hxs] at hx
    exact iff_of_false hxs fun h => zero_ne_one (tendsto_nhds_unique hx h)

end NullMeasurableSet

end MeasureTheory

/-! ### The Besicovitch covering property for subspaces -/

/-- The Besicovitch covering property passes along isometric embeddings: a satellite
configuration in the domain maps to one in the codomain. -/
theorem Isometry.hasBesicovitchCovering {α β : Type*} [MetricSpace α] [MetricSpace β]
    [HasBesicovitchCovering β] {f : α → β} (hf : Isometry f) : HasBesicovitchCovering α := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := β)
  refine ⟨N, τ, hτ, ⟨fun a => hN.false ?_⟩⟩
  exact
    { c := f ∘ a.c
      r := a.r
      rpos := a.rpos
      h := fun i j hij => by simpa only [Function.comp_apply, hf.dist_eq] using a.h hij
      hlast := fun i hi => by simpa only [Function.comp_apply, hf.dist_eq] using a.hlast i hi
      inter := fun i hi => by simpa only [Function.comp_apply, hf.dist_eq] using a.inter i hi }

/-- A subspace of a metric space with the Besicovitch covering property has it too. -/
instance Subtype.hasBesicovitchCovering {α : Type*} [MetricSpace α] [HasBesicovitchCovering α]
    (p : α → Prop) : HasBesicovitchCovering (Subtype p) :=
  isometry_subtype_coe.hasBesicovitchCovering

/-! ### Differentiation along concentric closed balls -/

namespace Besicovitch

variable {β F : Type*} [MetricSpace β] [MeasurableSpace β] [BorelSpace β]
  [SecondCountableTopology β] [HasBesicovitchCovering β] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

open MeasureTheory

/-- **Lebesgue's differentiation theorem** for a locally finite measure in a space with the
Besicovitch covering property: for a locally integrable function `f`, at almost every point `x`
the averages of `f` over the closed balls around `x` tend to `f x`. -/
theorem ae_tendsto_average_closedBall (μ : Measure β) [IsLocallyFiniteMeasure μ] {f : β → F}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average hf] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt μ x)

end Besicovitch
