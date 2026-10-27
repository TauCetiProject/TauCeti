/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.SecondMoment

/-!
# Second moments under Steiner symmetrization

Steiner symmetrization decreases the extended second moment about the origin for any
Lebesgue-measurable set. For a set with finite second moment, equality holds exactly when it agrees
almost everywhere with its symmetral. Thus the second moment detects fixed points of an
individual symmetrization step, as needed when identifying limits of successive steps.

Orthogonal coordinates split the squared norm into a transverse constant and the square
of the line coordinate. The strict centered-interval comparison on each line and Tonelli's
theorem then give the ambient comparison, including its equality case.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem lintegral_norm_sq_steinerSymmetrization_le_and_eq_iff
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume)
    (hmoment : (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ≠ ∞) :
    (∫⁻ x in steinerSymmetrization e he s, ENNReal.ofReal (‖x‖ ^ 2)) ≤
      (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ∧
      ((∫⁻ x in steinerSymmetrization e he s, ENNReal.ofReal (‖x‖ ^ 2)) =
        (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ↔ s =ᵐ[volume] steinerSymmetrization e he s) := by
  let S := steinerSymmetrization e he s
  let m (u : Set E) (y : (ℝ ∙ e)ᗮ) :=
    ∫⁻ t : ℝ, u.indicator (fun x ↦ ENNReal.ofReal (‖x‖ ^ 2)) ((y : E) + t • e)
  -- Tonelli transports the ambient moment and its finiteness to almost every line.
  have hS := nullMeasurableSet_steinerSymmetrization e he hs
  have hmeas (u : Set E) (hu : NullMeasurableSet u volume) : AEMeasurable (m u) volume := by
    exact aemeasurable_lintegral_line e he
      ((continuous_norm.pow 2).measurable.ennreal_ofReal.aemeasurable.indicator₀ hu)
  have hformula (u : Set E) (hu : NullMeasurableSet u volume) :
      (∫⁻ x in u, ENNReal.ofReal (‖x‖ ^ 2)) = ∫⁻ y, m u y := by
    rw [← lintegral_indicator₀ hu]
    exact lintegral_eq_lintegral_lintegral_line e he
      ((continuous_norm.pow 2).measurable.ennreal_ofReal.aemeasurable.indicator₀ hu)
  have hsection (u : Set E) (y : (ℝ ∙ e)ᗮ)
      (hu : NullMeasurableSet {t : ℝ | (y : E) + t • e ∈ u} volume) :
      m u y = ∫⁻ t in {t : ℝ | (y : E) + t • e ∈ u}, ENNReal.ofReal (‖y‖ ^ 2 + t ^ 2) := by
    dsimp only [m]
    rw [← lintegral_indicator₀ hu]
    apply lintegral_congr
    intro t
    -- Explicit section membership distinguishes its indicator from the ambient set's indicator.
    by_cases ht : (y : E) + t • e ∈ u
    · rw [indicator_of_mem ht,
        indicator_of_mem (show t ∈ {t : ℝ | (y : E) + t • e ∈ u} from ht),
        norm_add_smul_sq e he]
    · rw [indicator_of_notMem ht,
        indicator_of_notMem (show t ∉ {t : ℝ | (y : E) + t • e ∈ u} from ht)]
  have hmoment' : (∫⁻ y, m s y) ≠ ∞ := by rwa [← hformula s hs]
  have hfinite := ae_lt_top' (hmeas s hs) hmoment'
  have hcomp : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      m S y ≤ m s y ∧
        (m S y = m s y ↔ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume]
          {t : ℝ | (y : E) + t • e ∈ S}) := by
    filter_upwards [ae_nullMeasurableSet_lineSection e he hs,
      ae_nullMeasurableSet_lineSection e he hS, hfinite] with y hy hyS hymoment
    rw [hsection s y hy] at hymoment
    rw [hsection s y hy, hsection S y hyS, lineSection_steinerSymmetrization]
    exact ⟨lintegral_eball_add_sq_le hy _ (sq_nonneg _),
      lintegral_eball_add_sq_eq_iff hy _ (sq_nonneg _) hymoment.ne⟩
  have hle := lintegral_mono_ae (hcomp.mono fun _ h ↦ h.1)
  rw [hformula S hS, hformula s hs]
  refine ⟨hle, ⟨fun heq ↦ ?_, fun heq ↦ ?_⟩⟩
  -- Equality is detected first on almost every line, then by the ambient symmetric difference.
  · have hpoint := (lintegral_eq_iff_ae_eq_of_ae_le
      (ne_top_of_le_ne_top hmoment' hle) (hmeas s hs) (hcomp.mono fun _ h ↦ h.1)).mp heq
    have hlines : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
        {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] {t : ℝ | (y : E) + t • e ∈ S} := by
      filter_upwards [hpoint, hcomp] with y hy hc
      exact hc.2.mp hy
    have hzero : volume (s ∆ S) = 0 := by
      apply (volume_eq_zero_iff_ae_volume_lineSection_eq_zero e he (hs.symmDiff hS)).mpr
      filter_upwards [hlines] with y hy
      exact measure_symmDiff_eq_zero_iff.mpr hy
    exact (measure_symmDiff_eq_zero_iff).mp hzero
  · rw [← hformula S hS, ← hformula s hs]
    exact setLIntegral_congr heq.symm

/-- Steiner symmetrization decreases the second moment about the origin for any
Lebesgue-measurable set, allowing infinite volume and an infinite second moment. -/
theorem lintegral_norm_sq_steinerSymmetrization_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) :
    (∫⁻ x in steinerSymmetrization e he s, ENNReal.ofReal (‖x‖ ^ 2)) ≤
      (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) := by
  by_cases hmoment : (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) = ∞
  · rw [hmoment]
    exact le_top
  · exact (lintegral_norm_sq_steinerSymmetrization_le_and_eq_iff e he hs hmoment).1

/-- Equality of finite second moments holds exactly when the set agrees almost everywhere
with its Steiner symmetral in the given direction. -/
theorem lintegral_norm_sq_steinerSymmetrization_eq_iff (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume)
    (hmoment : (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ≠ ∞) :
    (∫⁻ x in steinerSymmetrization e he s, ENNReal.ofReal (‖x‖ ^ 2)) =
      (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ↔ s =ᵐ[volume] steinerSymmetrization e he s :=
  (lintegral_norm_sq_steinerSymmetrization_le_and_eq_iff e he hs hmoment).2

/-- A finite second moment remains integrable after Steiner symmetrization. -/
theorem integrableOn_norm_sq_steinerSymmetrization (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume)
    (hmoment : IntegrableOn (fun x ↦ ‖x‖ ^ 2) s volume) :
    IntegrableOn (fun x ↦ ‖x‖ ^ 2) (steinerSymmetrization e he s) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable (continuous_norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖)).mp
  exact ne_top_of_le_ne_top
    ((lintegral_ofReal_ne_top_iff_integrable (continuous_norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖)).mpr hmoment)
    (lintegral_norm_sq_steinerSymmetrization_le e he hs)

/-- The real-valued second moment decreases under Steiner symmetrization. -/
theorem integral_norm_sq_steinerSymmetrization_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume)
    (hmoment : IntegrableOn (fun x ↦ ‖x‖ ^ 2) s volume) :
    (∫ x in steinerSymmetrization e he s, ‖x‖ ^ 2) ≤ (∫ x in s, ‖x‖ ^ 2) := by
  have hle := lintegral_norm_sq_steinerSymmetrization_le e he hs
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_norm_sq_steinerSymmetrization e he hs hmoment)
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖),
    ← ofReal_integral_eq_lintegral_ofReal hmoment
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ sq_nonneg ‖x‖)).mp hle

/-- Equality of real-valued second moments characterizes the a.e. fixed points of a Steiner
symmetrization, provided the original second moment is integrable. -/
theorem integral_norm_sq_steinerSymmetrization_eq_iff (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume)
    (hmoment : IntegrableOn (fun x ↦ ‖x‖ ^ 2) s volume) :
    (∫ x in steinerSymmetrization e he s, ‖x‖ ^ 2) = (∫ x in s, ‖x‖ ^ 2) ↔
      s =ᵐ[volume] steinerSymmetrization e he s := by
  have hfinite := (lintegral_ofReal_ne_top_iff_integrable
    (continuous_norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖)).mpr hmoment
  have heq := lintegral_norm_sq_steinerSymmetrization_eq_iff e he hs hfinite
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_norm_sq_steinerSymmetrization e he hs hmoment)
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖),
    ← ofReal_integral_eq_lintegral_ofReal hmoment
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖x‖),
    ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x ↦ sq_nonneg ‖x‖)
      (integral_nonneg fun x ↦ sq_nonneg ‖x‖)] at heq
  exact heq

end TauCeti
