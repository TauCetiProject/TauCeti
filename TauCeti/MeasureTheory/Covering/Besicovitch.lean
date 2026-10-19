/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Density points of null-measurable sets

For a null-measurable set `s`, the proportion of the complement `sᶜ` in a set of positive
finite measure is one minus the proportion of `s`. Consequently `s` has density one along a
family of such sets exactly when `sᶜ` has density zero along it. This lets density arguments
estimate the complement, where measures add, and return to density-one points.

For a locally finite measure on a space with the Besicovitch covering property, Mathlib's
density theorem `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet` identifies the
limit of `μ (s ∩ closedBall x r) / μ (closedBall x r)` almost everywhere. We record its set
form: a null-measurable set agrees almost everywhere with its set of density-one points. That
set is a canonical representative of the `μ`-a.e. class of `s`, since it depends only on that
class.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory.NullMeasurableSet

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- For a null-measurable set `s`, along sets of positive finite measure the proportion of `sᶜ`
tends to zero exactly when the proportion of `s` tends to one. -/
theorem tendsto_measure_compl_inter_div_iff (hs : NullMeasurableSet s μ) {l : Filter ι}
    {u : ι → Set α} (hu : ∀ᶠ i in l, μ (u i) ≠ 0 ∧ μ (u i) ≠ ∞) :
    Tendsto (fun i => μ (sᶜ ∩ u i) / μ (u i)) l (𝓝 0) ↔
      Tendsto (fun i => μ (s ∩ u i) / μ (u i)) l (𝓝 1) := by
  have hle : ∀ i, μ (s ∩ u i) / μ (u i) ≤ 1 := fun i =>
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
  have hcompl : ∀ᶠ i in l, μ (sᶜ ∩ u i) / μ (u i) = 1 - μ (s ∩ u i) / μ (u i) := by
    filter_upwards [hu] with i ⟨h0, htop⟩
    have hadd : μ (s ∩ u i) + μ (sᶜ ∩ u i) = μ (u i) := by
      rw [inter_comm s, inter_comm sᶜ, ← sdiff_eq, measure_inter_add_sdiff₀ _ hs]
    rw [← ENNReal.div_self h0 htop, ← ENNReal.sub_div (fun _ _ => h0), ← hadd,
      ENNReal.add_sub_cancel_left (measure_ne_top_of_subset inter_subset_right htop)]
  constructor
  · intro h
    have h' := ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at h'
    refine h'.congr' ?_
    filter_upwards [hcompl] with i hi
    rw [hi, ENNReal.sub_sub_cancel ENNReal.one_ne_top (hle i)]
  · intro h
    have h' := ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at h'
    exact h'.congr' (hcompl.mono fun i hi => hi.symm)

variable [MetricSpace α] [SecondCountableTopology α] [BorelSpace α] [HasBesicovitchCovering α]
  [IsLocallyFiniteMeasure μ]

/-- A null-measurable set agrees almost everywhere with its set of density points with
respect to `μ`, the points at which its proportion of closed balls tends to one. -/
theorem ae_eq_setOf_tendsto_measure_inter_div (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] {x | Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
      (𝓝 1)} := by
  have hmeas : ∀ x r, μ (s ∩ closedBall x r) = μ (toMeasurable μ s ∩ closedBall x r) :=
    fun x r => measure_congr (hs.toMeasurable_ae_eq.symm.inter (ae_eq_refl _))
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ
    (measurableSet_toMeasurable μ s), eventuallyEqSet_iff.1 hs.toMeasurable_ae_eq] with x hx hxs
  simp only [hmeas]
  by_cases hxt : x ∈ toMeasurable μ s
  · simp only [indicator_of_mem hxt, Pi.one_apply] at hx
    exact iff_of_true (hxs.1 hxt) hx
  · simp only [indicator_of_notMem hxt] at hx
    exact iff_of_false (mt hxs.2 hxt) fun h => zero_ne_one (tendsto_nhds_unique hx h)

end MeasureTheory.NullMeasurableSet
