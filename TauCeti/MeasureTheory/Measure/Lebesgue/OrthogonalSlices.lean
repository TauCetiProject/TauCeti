/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Orthogonal line coordinates and Lebesgue sections

For a unit vector `e` in a finite-dimensional real inner product space, the coordinates
`(y, t) ↦ y + t • e`, with `y ∈ (ℝ ∙ e)ᗮ`, preserve product volume. Consequently the volume
of a Lebesgue-measurable set is the integral of the lengths of its parallel line sections.
Replacing a set by a volume-a.e. equal representative changes almost every section only
on a one-dimensional null set. This permits line-section arguments for measurable sets
without choosing a Borel representative permanently.

The coordinate construction uses Mathlib's `Submodule.orthogonalDecomposition` and
`LinearIsometryEquiv.toSpanUnitSingleton`; its normalization follows Mathlib's volume
preservation for linear isometries and for the `L²` product.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal line coordinates preserve the product of transverse and longitudinal volumes. -/
theorem measurePreserving_orthogonalLineEquiv (e : E) (he : ‖e‖ = 1) :
    MeasurePreserving (orthogonalLineEquiv e he) (volume.prod volume) volume := by
  rw [orthogonalLineEquiv_def]
  exact (orthogonalLineIsometry e he).measurePreserving.comp
    (WithLp.volume_preserving_toLp (ℝ ∙ e)ᗮ ℝ)

/-- Volume-a.e. equal sets have a.e. equal parallel sections for almost every transverse point.
The exceptional transverse null set is allowed to depend on the direction. -/
theorem ae_lineSection_eq (e : E) (he : ‖e‖ = 1) {s u : Set E} (h : s =ᵐ[volume] u) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume]
        {t : ℝ | (y : E) + t • e ∈ u} := by
  have hp := (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving.preimage_ae_eq h
  have hsections := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hsections] with y hy
  filter_upwards [hy] with t ht
  simpa only [mem_preimage, orthogonalLineEquiv_apply, mem_ofPred_eq] using ht

/-- Having interval sections up to null sets is independent of the ambient a.e. representative,
for each fixed unit direction. The intervals may be empty or unbounded. -/
theorem ae_lineSection_ordConnected_iff (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (h : s =ᵐ[volume] u) :
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) ↔
    (∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
      {t : ℝ | (y : E) + t • e ∈ u} =ᵐ[volume] I) := by
  have transport {v w : Set E} (hvw : v =ᵐ[volume] w)
      (hv : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
        {t : ℝ | (y : E) + t • e ∈ v} =ᵐ[volume] I) :
      ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, OrdConnected I ∧
        {t : ℝ | (y : E) + t • e ∈ w} =ᵐ[volume] I := by
    filter_upwards [ae_lineSection_eq e he hvw, hv] with y hy hI
    obtain ⟨I, hIc, hIe⟩ := hI
    exact ⟨I, hIc, hy.symm.trans hIe⟩
  exact ⟨transport h, transport h.symm⟩

/-- A Lebesgue-measurable set has Lebesgue-measurable sections on almost every parallel line. -/
theorem ae_nullMeasurableSet_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, NullMeasurableSet {t : ℝ | (y : E) + t • e ∈ s} volume := by
  filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
  have hm : MeasurableSet {t : ℝ | (y : E) + t • e ∈ toMeasurable volume s} :=
    (measurableSet_toMeasurable volume s).preimage
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
  exact hm.nullMeasurableSet.congr hy

/-- The lengths of the parallel sections of a Lebesgue-measurable set form an a.e. measurable
extended nonnegative function on the orthogonal subspace. -/
theorem aemeasurable_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ => volume {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
    ((measurableSet_toMeasurable volume s).preimage
      (measurePreserving_orthogonalLineEquiv e he).measurable)
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_lineSection_eq e he hs.toMeasurable_ae_eq] with y hy
  refine (congrArg volume ?_).trans (measure_congr hy)
  ext t
  simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Cavalieri's formula for Lebesgue-measurable sets in orthogonal line coordinates, with
extended nonnegative values and no finite-volume assumption. -/
theorem volume_eq_lintegral_volume_lineSection (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = ∫⁻ y : (ℝ ∙ e)ᗮ, volume {t : ℝ | (y : E) + t • e ∈ s} := by
  have hp := hs.preimage (measurePreserving_orthogonalLineEquiv e he).quasiMeasurePreserving
  rw [← (measurePreserving_orthogonalLineEquiv e he).measure_preimage hs,
    Measure.prod_apply₀ hp]
  congr 1 with y
  congr 1
  ext t
  simp only [mem_preimage, mem_ofPred_eq, orthogonalLineEquiv_apply]

/-- Finite ambient volume implies finite length of almost every parallel section. -/
theorem ae_volume_lineSection_lt_top (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfinite : volume s ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} < ∞ := by
  apply ae_lt_top' (aemeasurable_volume_lineSection e he hs)
  rwa [← volume_eq_lintegral_volume_lineSection e he hs]

/-- A Lebesgue-measurable set is null exactly when almost every parallel line section is null. -/
theorem volume_eq_zero_iff_ae_volume_lineSection_eq_zero (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    volume s = 0 ↔
      ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, volume {t : ℝ | (y : E) + t • e ∈ s} = 0 := by
  rw [volume_eq_lintegral_volume_lineSection e he hs,
    lintegral_eq_zero_iff' (aemeasurable_volume_lineSection e he hs)]
  rfl

end TauCeti
