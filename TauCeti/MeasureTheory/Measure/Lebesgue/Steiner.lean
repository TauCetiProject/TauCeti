/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Steiner symmetrization of Lebesgue-measurable sets

Steiner symmetrization in a unit direction replaces each parallel line section by the open
centered interval of the same length. We use extended-radius balls in `ℝ`: a null section
becomes empty and an infinite-length section becomes the whole line. Thus the construction
is defined without boundedness or finiteness assumptions.

The symmetral of a Lebesgue-measurable set is Lebesgue-measurable and has the same volume.
It is independent, up to null sets, of the input representative. Symmetrization is monotone,
idempotent, and contracts the volume of symmetric differences, equivalently the `L¹`
distance between indicators. The contraction permits approximation of arbitrary measurable
sets before iterating symmetrizations.

The normalization uses `Real.volume_eball` and the measure-preserving orthogonal coordinates
from `TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices`.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Steiner symmetrization along the unit direction `e`, centered on its orthogonal hyperplane.
The section of length `ℓ` is the open centered interval of radius `ℓ / 2`; this includes
empty intervals for `ℓ = 0` and the whole line for `ℓ = ∞`. -/
def steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E) : Set E :=
  {x | ((orthogonalLineEquiv e he).symm x).2 ∈ Metric.eball (0 : ℝ)
    (volume {t : ℝ | (((orthogonalLineEquiv e he).symm x).1 : E) + t • e ∈ s} / 2)}

/-- The coordinate description of a Steiner symmetral. -/
theorem steinerSymmetrization_def (e : E) (he : ‖e‖ = 1) (s : Set E) :
    steinerSymmetrization e he s =
      {x | ((orthogonalLineEquiv e he).symm x).2 ∈ Metric.eball (0 : ℝ)
        (volume {t : ℝ | (((orthogonalLineEquiv e he).symm x).1 : E) + t • e ∈ s} / 2)} := (rfl)

/-- Membership in a Steiner symmetral in orthogonal line coordinates. -/
@[simp]
theorem mem_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (y : E) + t • e ∈ steinerSymmetrization e he s ↔
      t ∈ Metric.eball (0 : ℝ) (volume {u : ℝ | (y : E) + u • e ∈ s} / 2) := by
  rw [← orthogonalLineEquiv_apply e he y t]
  simp only [steinerSymmetrization, mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]

/-- Every parallel section of the symmetral is the centered interval of the prescribed length. -/
theorem lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      Metric.eball (0 : ℝ) (volume {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
  ext t
  exact mem_steinerSymmetrization e he s y t

/-- Symmetrization preserves the length of every parallel section, even infinite ones. -/
theorem volume_lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1) (s : Set E)
    (y : (ℝ ∙ e)ᗮ) :
    volume {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      volume {t : ℝ | (y : E) + t • e ∈ s} := by
  rw [lineSection_steinerSymmetrization, Real.volume_eball]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- All parallel sections of a Steiner symmetral are intervals. -/
theorem ordConnected_lineSection_steinerSymmetrization (e : E) (he : ‖e‖ = 1)
    (s : Set E) (y : (ℝ ∙ e)ᗮ) :
    OrdConnected {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} := by
  rw [lineSection_steinerSymmetrization]
  exact (convex_eball _ _).ordConnected

/-- Applying the same Steiner symmetrization twice has no further effect. -/
@[simp]
theorem steinerSymmetrization_idem (e : E) (he : ‖e‖ = 1) (s : Set E) :
    steinerSymmetrization e he (steinerSymmetrization e he s) =
      steinerSymmetrization e he s := by
  ext x
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  rw [orthogonalLineEquiv_apply, mem_steinerSymmetrization,
    volume_lineSection_steinerSymmetrization, mem_steinerSymmetrization]

/-- Steiner symmetrization preserves inclusion. -/
theorem steinerSymmetrization_mono (e : E) (he : ‖e‖ = 1) :
    Monotone (steinerSymmetrization e he) := by
  intro s u h x hx
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  rw [orthogonalLineEquiv_apply, mem_steinerSymmetrization] at hx ⊢
  have hlength : volume {v : ℝ | (y : E) + v • e ∈ s} ≤
      volume {v : ℝ | (y : E) + v • e ∈ u} := measure_mono fun v hv ↦ h hv
  exact Metric.eball_subset_eball (ENNReal.div_le_div_right hlength 2) hx

@[simp]
theorem steinerSymmetrization_empty (e : E) (he : ‖e‖ = 1) :
    steinerSymmetrization e he ∅ = ∅ := by
  ext x
  simp [steinerSymmetrization]

@[simp]
theorem steinerSymmetrization_univ (e : E) (he : ‖e‖ = 1) :
    steinerSymmetrization e he univ = univ := by
  ext x
  simp [steinerSymmetrization, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Borel sets have Borel Steiner symmetrals. -/
theorem measurableSet_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : MeasurableSet s) : MeasurableSet (steinerSymmetrization e he s) := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
    (hs.preimage (measurePreserving_orthogonalLineEquiv e he).measurable)
  have hlength : Measurable (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ s}) := by
    have hsection (y : (ℝ ∙ e)ᗮ) :
        Prod.mk y ⁻¹' (orthogonalLineEquiv e he) ⁻¹' s =
          {t : ℝ | (y : E) + t • e ∈ s} := by
      ext t
      simp only [mem_preimage, orthogonalLineEquiv_apply, mem_ofPred_eq]
    simpa only [hsection] using hm
  exact measurableSet_lt
    (((orthogonalLineEquiv e he).symm.continuous.measurable.snd).edist measurable_const)
    ((hlength.comp ((orthogonalLineEquiv e he).symm.continuous.measurable.fst)).div_const 2)

/-- Replacing the input by an a.e. equal set changes the symmetral only on a null set. -/
theorem steinerSymmetrization_ae_eq (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (h : s =ᵐ[volume] u) :
    steinerSymmetrization e he s =ᵐ[volume] steinerSymmetrization e he u := by
  have hcoord : MeasurePreserving (orthogonalLineEquiv e he).symm volume (volume.prod volume) :=
    MeasurePreserving.symm (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv
      (measurePreserving_orthogonalLineEquiv e he)
  have hbase := Measure.quasiMeasurePreserving_fst.comp hcoord.quasiMeasurePreserving
  have hsections := ae_lineSection_eq e he h
  have hlength : (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ s}) =ᵐ[volume]
      (fun y : (ℝ ∙ e)ᗮ ↦ volume {t : ℝ | (y : E) + t • e ∈ u}) :=
    hsections.mono fun y hy ↦ measure_congr hy
  filter_upwards [hbase.ae_eq_comp hlength] with x hx
  simp only [Function.comp_apply] at hx
  simp only [steinerSymmetrization, mem_ofPred_eq, hx]

/-- Steiner symmetrization preserves Lebesgue measurability. -/
theorem nullMeasurableSet_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    NullMeasurableSet (steinerSymmetrization e he s) volume :=
  ((measurableSet_steinerSymmetrization e he
    (measurableSet_toMeasurable volume s)).nullMeasurableSet).congr
      (steinerSymmetrization_ae_eq e he hs.toMeasurable_ae_eq)

/-- Steiner symmetrization preserves volume, with no boundedness or finiteness assumptions. -/
@[simp]
theorem volume_steinerSymmetrization (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) : volume (steinerSymmetrization e he s) = volume s := by
  rw [volume_eq_lintegral_volume_lineSection e he
    (nullMeasurableSet_steinerSymmetrization e he hs),
    volume_eq_lintegral_volume_lineSection e he hs]
  simp only [volume_lineSection_steinerSymmetrization]

/-- Steiner symmetrization contracts the volume of one-sided differences. -/
theorem volume_steinerSymmetrization_sdiff_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    volume (steinerSymmetrization e he s \ steinerSymmetrization e he u) ≤ volume (s \ u) := by
  rw [volume_eq_lintegral_volume_lineSection e he
    ((nullMeasurableSet_steinerSymmetrization e he hs).diff
      (nullMeasurableSet_steinerSymmetrization e he hu)),
    volume_eq_lintegral_volume_lineSection e he (hs.diff hu)]
  apply lintegral_mono
  intro y
  dsimp only
  have hsection (v w : Set E) :
      {t : ℝ | (y : E) + t • e ∈ v \ w} =
        {t : ℝ | (y : E) + t • e ∈ v} \ {t : ℝ | (y : E) + t • e ∈ w} :=
    preimage_sdiff (fun t : ℝ ↦ (y : E) + t • e) v w
  rw [hsection, hsection, lineSection_steinerSymmetrization, lineSection_steinerSymmetrization]
  exact volume_eball_sdiff_le _ _

/-- The volume of the symmetric difference, or `L¹` distance between indicators, does not
increase under Steiner symmetrization. Infinite-volume inputs are permitted. -/
theorem volume_steinerSymmetrization_symmDiff_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    volume (steinerSymmetrization e he s ∆ steinerSymmetrization e he u) ≤ volume (s ∆ u) := by
  rw [measure_symmDiff_eq (nullMeasurableSet_steinerSymmetrization e he hs)
    (nullMeasurableSet_steinerSymmetrization e he hu), measure_symmDiff_eq hs hu]
  exact add_le_add (volume_steinerSymmetrization_sdiff_le e he hs hu)
    (volume_steinerSymmetrization_sdiff_le e he hu hs)

/-- The `L¹` seminorm distance between real indicators contracts under Steiner symmetrization. -/
theorem eLpNorm_indicator_steinerSymmetrization_sub_le (e : E) (he : ‖e‖ = 1) {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) :
    eLpNorm ((steinerSymmetrization e he s).indicator (fun _ ↦ (1 : ℝ)) -
      (steinerSymmetrization e he u).indicator (fun _ ↦ (1 : ℝ))) 1 volume ≤
        eLpNorm (s.indicator (fun _ ↦ (1 : ℝ)) - u.indicator (fun _ ↦ (1 : ℝ))) 1 volume := by
  have hS := nullMeasurableSet_steinerSymmetrization e he hs
  have hU := nullMeasurableSet_steinerSymmetrization e he hu
  rw [eLpNorm_indicator_sub_indicator _ hS hU, eLpNorm_indicator_sub_indicator _ hs hu,
    eLpNorm_indicator_const (hS.symmDiff hU) one_ne_zero ENNReal.one_ne_top,
    eLpNorm_indicator_const (hs.symmDiff hu) one_ne_zero ENNReal.one_ne_top]
  simpa using volume_steinerSymmetrization_symmDiff_le e he hs hu

end TauCeti
