/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
public import TauCeti.MeasureTheory.Function.Coarea.DistributionFunction
public import TauCeti.Analysis.Calculus.Sard.Radial

/-!
# Critical values of Schwarz rearrangements

The real-valued Schwarz rearrangement of the positive part of a Lipschitz function with respect
to any additive Haar measure has a Lebesgue-null set of critical values. Thus almost every level
contains neither zero-gradient points nor nondifferentiability points. This is the radial
critical-value input to the reciprocal-gradient coarea formula for the distribution function of a
rearrangement.

Consequently, if the superlevel sets `{h > t}` have finite volume for `t > 0`, then at almost
every level `t > 0` the reciprocal-gradient level integral of the rearrangement `h*` is exactly
minus the derivative of the distribution function `μ_h(t) = |{h > t}|` of `h`:

`∫_{{h* = t} ∩ {Dh* ≠ 0}} ‖Dh*‖⁻¹ dHⁿ⁻¹ = -μ_h'(t)`

(`LipschitzWith.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv`).
For `h` itself only the inequality `≤` holds in general
(`MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv`). The Pólya–Szegő
inequality for Lipschitz functions compares the two statements level by level.

The representative is the canonical `schwarzRearrangement` followed by `ENNReal.toReal`.
For integrable inputs the extended rearrangement is finite almost everywhere, by
`MeasureTheory.Integrable.ae_schwarzRearrangement_ofReal_ne_top`. The critical-value assertion
itself needs no integrability hypothesis and retains the same totalization conventions as
`TauCeti.lipschitzWith_toReal_schwarzRearrangement`.

## References

* Bianchi–Gardner–Gronchi–Kiderlen, *The Pólya–Szegő inequality for smoothing rearrangements*,
  arXiv:2206.09833, proof of Theorem 5.8.
-/

public section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {K : ℝ≥0} {h : E → ℝ}

/-- The totalized critical values of the real Schwarz rearrangement of the positive part of a
Lipschitz function with respect to any additive Haar measure form a Lebesgue-null set. In
particular, images of nondifferentiability points are included in this exceptional set. -/
theorem volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero
    (hh : LipschitzWith K h) (μ : Measure E) [μ.IsAddHaarMeasure] :
    volume ((fun x ↦ (TauCeti.schwarzRearrangement μ
      (fun y ↦ ENNReal.ofReal (h y)) x).toReal) ''
      {x | fderiv ℝ (fun z ↦ (TauCeti.schwarzRearrangement μ
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x = 0}) = 0 := by
  have hLip := TauCeti.lipschitzWith_toReal_schwarzRearrangement μ hh
  apply hLip.volume_image_setOf_fderiv_eq_zero_of_norm_eq
  intro x y hxy
  exact congrArg ENNReal.toReal (TauCeti.schwarzRearrangement_eq_of_norm_eq μ _ hxy)

/-- **Level integrals of a rearranged Lipschitz function.** Let `h` be Lipschitz with superlevel
sets `{h > t}` of finite volume for `t > 0`, and let `h*` be the real Schwarz rearrangement of its
positive part. At almost every `t > 0`, the reciprocal-gradient level integral of `h*` equals minus
the derivative of the distribution function `μ_h(t) = |{h > t}|` of `h`:

`∫_{{h* = t} ∩ {Dh* ≠ 0}} ‖Dh*‖⁻¹ dHⁿ⁻¹ = -μ_h'(t)`. -/
theorem ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ (fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x ≠ 0} ∩
          (fun z ↦ (TauCeti.schwarzRearrangement volume
            (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t},
        ‖fderiv ℝ (fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] =
        ENNReal.ofReal (-deriv (fun s ↦ volume.real {x | s < h x}) t) := by
  -- The real rearrangement has the same distribution function as `h` at positive levels.
  have hdist (s : ℝ) (hs : 0 < s) : volume {x | s < (TauCeti.schwarzRearrangement volume
      (fun y ↦ ENNReal.ofReal (h y)) x).toReal} = volume {x | s < h x} :=
    TauCeti.addHaar_setOf_lt_toReal_schwarzRearrangement
      (TauCeti.ae_schwarzRearrangement_ofReal_ne_top hh.continuous.aemeasurable (hfin 1 one_pos))
      hs.le
  have hv := TauCeti.lipschitzWith_toReal_schwarzRearrangement volume hh
  filter_upwards [ae_setLIntegral_inv_enorm_fderiv_eq_ofReal_neg_deriv
    hv.continuous.measurable.aemeasurable (fun t ht ↦ hdist t ht ▸ hfin t ht)
    (hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume)] with t ht htpos
  rw [ht htpos]
  congr 2
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioi_mem_nhds htpos] with s hs
  rw [measureReal_def, measureReal_def, hdist s hs]

end LipschitzWith
