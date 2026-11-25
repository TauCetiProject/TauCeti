/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.OneDimensional.EssentialBoundary
public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Regular
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Weighted perimeter on the line

Let `s ⊆ ℝ` be null-measurable with locally finite perimeter in an open set `Ω`. Its essential
boundary points in `Ω` are then locally finite in `Ω`
(`TauCeti.Real.finite_essentialBoundary_inter_of_perimeter_ne_top`), and the variation measure
`|Dχ_s|` on `Ω` is the sum of the unit masses at these points
(`TauCeti.Real.variationMeasure_indicator_eq_sum_dirac`): both measures are outer regular and give
every open `U ⊆ Ω` the value `#(∂ᵉs ∩ U) = P(s; U)`
(`TauCeti.Real.perimeter_eq_encard_essentialBoundary_inter`). Integrating the weight against it,
for every weight `W` (`C¹` for the weighted perimeter, measurable or not for the measure identity):

`P_μ(s; Ω) = Σ_{t ∈ ∂ᵉs ∩ Ω} e^{−W(t)}`

(`TauCeti.Real.weightedPerimeter_eq_tsum_essentialBoundary_inter`), and more generally
`∫_B e^{−W} d|Dχ_s| = Σ_{t ∈ ∂ᵉs ∩ Ω, t ∈ B} e^{−W(t)}` for every `B ⊆ Ω`
(`TauCeti.Real.lintegral_variationMeasure_indicator`). For the standard Gaussian weight,
`e^{−W} = φ` is the standard normal density (`TauCeti.Real.exp_neg_gaussianWeight`), so the
Gaussian perimeter of `s` is `Σ_{t ∈ ∂ᵉs} φ(t)`
(`TauCeti.Real.gaussianPerimeter_eq_tsum_essentialBoundary`).

## References

* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), Section 3 (sets of locally finite perimeter on the line).
-/

public section

open MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Real

variable {s : Set ℝ} {Ω : Opens ℝ}

/-- The sum of the unit masses at the points of `∂ᵉs` in `Ω` gives every open `U ⊆ Ω` the number
of these points in `U`. -/
private theorem sum_dirac_preimage_coe (U : Opens ℝ) (hU : U ≤ Ω) :
    (Measure.sum fun x : ↥(essentialBoundary volume s ∩ Ω) => Measure.dirac (⟨x, x.property.2⟩ : Ω))
        ((↑) ⁻¹' (U : Set ℝ)) = (essentialBoundary volume s ∩ U).encard := by
  have hm : MeasurableSet (((↑) : Ω → ℝ) ⁻¹' (U : Set ℝ)) :=
    measurable_subtypeVal U.isOpen.measurableSet
  rw [Measure.sum_apply _ hm]
  simp_rw [Measure.dirac_apply' _ hm]
  have hpt (x : ↥(essentialBoundary volume s ∩ Ω)) :
      (((↑) : Ω → ℝ) ⁻¹' (U : Set ℝ)).indicator 1 (⟨x, x.property.2⟩ : Ω) =
        (U : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) (x : ℝ) := by
    by_cases hx : (x : ℝ) ∈ (U : Set ℝ) <;> simp [indicator, hx]
  rw [tsum_congr hpt, ← ENNReal.tsum_indicator_one,
    tsum_subtype (essentialBoundary volume s ∩ Ω) fun x => (U : Set ℝ).indicator (fun _ => 1) x]
  congr 1
  ext x
  by_cases hx : x ∈ essentialBoundary volume s ∩ Ω
  · by_cases hxU : x ∈ (U : Set ℝ)
    · simp [indicator, hx, hxU, hx.1]
    · simp [indicator, hx, hxU]
  · have : x ∉ essentialBoundary volume s ∩ U := fun h => hx ⟨h.1, hU h.2⟩
    simp [indicator, hx, this]

/-- The indicator of a null-measurable set is locally integrable on every open set. -/
private theorem indicator_one_locallyIntegrableOn (hs : NullMeasurableSet s) :
    LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) Ω volume :=
  locallyIntegrableOn_indicator_const (hs.mono Measure.restrict_le_self) 1

/-- **The perimeter measure on the line.** For a null-measurable set `s ⊆ ℝ` of locally finite
perimeter in the open set `Ω`, the variation measure `|Dχ_s|` on `Ω` is the sum of the unit
masses at the points of the essential boundary `∂ᵉs` lying in `Ω`. -/
theorem variationMeasure_indicator_eq_sum_dirac (hs : NullMeasurableSet s)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ perimeter volume U s ≠ ∞) :
    variationMeasure volume Ω (s.indicator 1) =
      Measure.sum fun x : ↥(essentialBoundary volume s ∩ Ω) =>
        Measure.dirac (⟨x, x.property.2⟩ : Ω) := by
  set ν := Measure.sum fun x : ↥(essentialBoundary volume s ∩ Ω) =>
    Measure.dirac (⟨x, x.property.2⟩ : Ω)
  have hloc : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, hU⟩ := hfin {x.val} isCompact_singleton (singleton_subset_iff.2 x.property)
    refine ⟨(↑) ⁻¹' ((U ⊓ Ω : Opens ℝ) : Set ℝ),
      ((U ⊓ Ω).isOpen.preimage continuous_subtypeVal).mem_nhds ⟨hxU rfl, x.property⟩, ?_⟩
    rw [sum_dirac_preimage_coe _ inf_le_right]
    have := (finite_essentialBoundary_inter_of_perimeter_ne_top (Ω := U ⊓ Ω) hs
      (ne_top_of_le_ne_top hU (perimeter_mono (inf_le_left : U ⊓ Ω ≤ U)))).encard_lt_top
    exact lt_top_iff_ne_top.2 fun h => this.ne (by simpa using h)
  refine (eq_variationMeasure (indicator_one_locallyIntegrableOn hs)
    (by simpa only [perimeter_def] using hfin) fun U hU => ?_).symm
  rw [sum_dirac_preimage_coe U hU, ← perimeter_def, perimeter_eq_encard_essentialBoundary_inter hs]

/-- **Integrals against the perimeter measure on the line.** For a null-measurable set `s ⊆ ℝ` of
locally finite perimeter in `Ω`, integrating against `|Dχ_s|` sums over the essential boundary
points of `s` in `Ω`. -/
theorem lintegral_variationMeasure_indicator (hs : NullMeasurableSet s)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ perimeter volume U s ≠ ∞)
    (f : Ω → ℝ≥0∞) :
    ∫⁻ x, f x ∂variationMeasure volume Ω (s.indicator 1) =
      ∑' x : ↥(essentialBoundary volume s ∩ Ω), f ⟨x, x.property.2⟩ := by
  rw [variationMeasure_indicator_eq_sum_dirac hs hfin, lintegral_sum_measure]
  simp only [lintegral_dirac]

/-- **The weighted perimeter on the line.** For a `C¹` weight `W` on `ℝ` and a null-measurable set
`s ⊆ ℝ` of locally finite perimeter in the open set `Ω`,
`P_μ(s; Ω) = Σ_{t ∈ ∂ᵉs ∩ Ω} e^{−W(t)}`. -/
theorem weightedPerimeter_eq_tsum_essentialBoundary_inter {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W)
    (hs : NullMeasurableSet s)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ perimeter volume U s ≠ ∞) :
    weightedPerimeter W Ω s =
      ∑' x : ↥(essentialBoundary volume s ∩ Ω), ENNReal.ofReal (Real.exp (-W x)) := by
  rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW
    (indicator_one_locallyIntegrableOn hs) (by simpa only [perimeter_def] using hfin),
    lintegral_variationMeasure_indicator hs hfin]

/-- On the line, the Gaussian density `e^{−W}` is the standard normal density `φ`. -/
theorem exp_neg_gaussianWeight (x : ℝ) :
    Real.exp (-gaussianWeight ℝ x) = gaussianPDFReal 0 1 x := by
  rw [exp_neg_gaussianWeight_of_norm_eq rfl, Real.norm_eq_abs, sq_abs, Module.finrank_self,
    gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero, Nat.cast_one]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), one_div]
  congr 1
  · norm_num
  · congr 1
    ring

/-- **The Gaussian perimeter on the line.** A null-measurable set `s ⊆ ℝ` of locally finite
perimeter has Gaussian perimeter `Σ_{t ∈ ∂ᵉs} φ(t)`. -/
theorem gaussianPerimeter_eq_tsum_essentialBoundary (hs : NullMeasurableSet s)
    (hfin : ∀ K : Set ℝ, IsCompact K → ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ perimeter volume U s ≠ ∞) :
    gaussianPerimeter s =
      ∑' x : ↥(essentialBoundary volume s), ENNReal.ofReal (gaussianPDFReal 0 1 x) := by
  rw [gaussianPerimeter_def, weightedPerimeter_eq_tsum_essentialBoundary_inter
    (contDiff_gaussianWeight) hs fun K hK _ => hfin K hK]
  simp only [Opens.coe_top, exp_neg_gaussianWeight]
  exact (Equiv.subtypeEquivRight fun x => by simp).tsum_eq
    fun x : ↥(essentialBoundary volume s) => ENNReal.ofReal (gaussianPDFReal 0 1 x)

end TauCeti.Real
