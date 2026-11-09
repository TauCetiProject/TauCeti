/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Slicing.Basic
import TauCeti.Analysis.BoundedVariation.Real

/-!
# Perimeter excess from noninterval line sections

For a finite-volume Lebesgue-measurable set `s` and a unit direction `e`, let `D` be the
set of transverse points whose line sections have positive length. Every such section costs
at least two units of one-dimensional perimeter. A section that does not agree almost
everywhere with an interval costs at least four instead.

Consequently, for any null-measurable family `A` of noninterval sections,

`2 volume D + 2 volume A ≤ perimeter volume ⊤ s`.

The weighted version retains the transverse divergence pairing in the joint slicing inequality.
It localizes the extra cost to `A`, without requiring measurability of the collection of all
noninterval sections.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and §3.11, for one-dimensional variation and slicing.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2, for the interval-section condition.
-/

public section

open MeasureTheory Set TestFunction
open scoped ENNReal Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The weighted perimeters of line sections pay twice for every positive-length section and
an additional two for each section in a null-measurable family `A` of noninterval sections.
The weight is arbitrary and nonnegative; no measurability assumption on it is needed. -/
theorem two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (w : (ℝ ∙ e)ᗮ → ℝ≥0∞) :
    2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}, w y) +
        2 * (∫⁻ y in A, w y) ≤
      ∫⁻ y : (ℝ ∙ e)ᗮ, w y * perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} := by
  let D := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hpoint : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      D.indicator (fun _ ↦ (2 : ℝ≥0∞)) y + A.indicator (fun _ ↦ (2 : ℝ≥0∞)) y ≤
        perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} := by
    filter_upwards [ae_nullMeasurableSet_lineSection e he hs,
      ae_volume_lineSection_lt_top e he hs hfin, hbad] with y hym hyfin hybad
    by_cases hyA : y ∈ A
    · have hfour := Real.four_le_perimeter hym hyfin.ne (hybad hyA)
      have htwo : D.indicator (fun _ ↦ (2 : ℝ≥0∞)) y ≤ 2 := by
        by_cases hyD : y ∈ D <;> simp [hyD]
      calc
        _ ≤ 2 + 2 := add_le_add htwo (by simp [hyA])
        _ = 4 := by norm_num
        _ ≤ _ := hfour
    · by_cases hyD : y ∈ D
      · simpa [hyA, hyD] using Real.two_le_perimeter hym hyD.ne' hyfin.ne
      · simp [hyA, hyD]
  calc
    _ = (∫⁻ y, D.indicator (fun y ↦ 2 * w y) y) +
        ∫⁻ y, A.indicator (fun y ↦ 2 * w y) y := by
      rw [lintegral_indicator₀ hD, lintegral_indicator₀ hA,
        lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ ∫⁻ y, D.indicator (fun y ↦ 2 * w y) y +
        A.indicator (fun y ↦ 2 * w y) y := le_lintegral_add _ _
    _ ≤ _ := lintegral_mono_ae (hpoint.mono fun y hy ↦ by
      have hm := mul_le_mul_left hy (w y)
      by_cases hyD : y ∈ D <;> by_cases hyA : y ∈ A <;>
        simp_all [mul_add, mul_comm])

/-- A localized strengthening of the joint slicing inequality. The transverse test field
retains the pairing with section lengths, while each noninterval section in `A` contributes
an extra `2 √(1 - ‖φ‖²)` to the lower bound for the ambient perimeter. -/
theorem two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    (2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
      2 * (∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2))) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≤ perimeter volume ⊤ s :=
  (add_le_add
    (two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
      hs hfin e he hA hbad (fun y ↦ ENNReal.ofReal √(1 - ‖φ y‖ ^ 2))) le_rfl).trans
    (lintegral_mul_perimeter_lineSection_add_ofReal_integral_le hs hfin e he φ hφ)

/-- The perimeter bounds twice the transverse measure of positive-length sections plus twice
the measure of any null-measurable family of noninterval sections. This extended inequality
also applies when the ambient perimeter is infinite. -/
theorem two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        2 * volume A ≤ perimeter volume ⊤ s := by
  have h := two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
    hs hfin e he hA hbad (fun _ ↦ 1)
  simpa using h.trans (by simpa using lintegral_perimeter_lineSection_le hs hfin e he)

end TauCeti
