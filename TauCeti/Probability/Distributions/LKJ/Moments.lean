/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Determinant
import TauCeti.Probability.Distributions.LKJ.PartialCorrelation

/-!
# Determinant moments of the LKJ law

For an LKJ correlation matrix of positive shape `η`, a real determinant power `q` is
integrable in dimensions at least two exactly when `-η < q`. On this sharp domain its
expectation is the ratio of LKJ normalizing constants

`lkjNormalizer p (η + q) / lkjNormalizer p η`.

The value follows directly by multiplying the LKJ density by the determinant power, which shifts
its exponent from `η - 1` to `η + q - 1`. Sharpness follows from the independent centered-Beta
partial-correlation representation of the LKJ law and the construction's exact integrability
threshold.

In dimensions zero and one, the LKJ law is concentrated at the identity and every determinant
power is constantly one.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η q : ℝ}

/-- **Determinant moments of the LKJ law.** If `η > 0` and `q > -η`, then the expectation of
`det R ^ q` is the ratio of the LKJ normalizers at the shifted and original shapes. This includes
dimensions zero and one. -/
theorem integral_rpow_det_lkjMeasure (hη : 0 < η) (hq : -η < q) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ q ∂lkjMeasure p η =
      lkjNormalizer p (η + q) / lkjNormalizer p η := by
  rw [lkjMeasure_of_pos hη]
  have hlkjPDF : lkjPDF p η = fun R ↦ ENNReal.ofReal (lkjPDFReal p η R) := by
    funext R
    rw [lkjPDF_def]
  rw [hlkjPDF, TauCeti.Probability.integral_withDensity_ofReal
    (measurable_lkjPDFReal p η).aemeasurable (ae_of_all _ (lkjPDFReal_nonneg hη))]
  rw [lkjPDFReal_eq_indicator]
  simp only [smul_eq_mul]
  have hindicator :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
            (fun A ↦ (A : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
              lkjNormalizer p η) R * (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) =
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
            (fun R ↦ ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
              lkjNormalizer p η) * (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) := by
    funext R
    rw [Set.indicator_mul_left]
  rw [hindicator, integral_indicator (measurableSet_posDefMatrix p)]
  have hcombine : ∀ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef →
        ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η) *
            (R : Matrix (Fin p) (Fin p) ℝ).det ^ q =
          (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η + q - 1) /
            lkjNormalizer p η := by
    intro R hR
    rw [div_mul_eq_mul_div, ← Real.rpow_add hR.det_pos]
    congr 2
    ring
  rw [setIntegral_congr_fun (measurableSet_posDefMatrix p) hcombine, integral_div,
    setIntegral_rpow_det_correlationLebesgue p (by linarith),
    div_eq_mul_inv]

private theorem map_det_lkjMeasure_eq_map_det_partialCorrelationGram (hη : 0 < η) :
    (lkjMeasure p η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det) =
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)).map
        (fun z ↦ (partialCorrelationGram z).det) := by
  have hdet :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ).det) =
        Matrix.det ∘ (Subtype.val : selfAdjoint.submodule ℝ
          (Matrix (Fin p) (Fin p) ℝ) → Matrix (Fin p) (Fin p) ℝ) := rfl
  rw [hdet, ← Measure.map_map (by fun_prop) measurable_subtype_coe, map_coe_lkjMeasure hη,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Sharp determinant-power integrability for the LKJ law.** In dimension at least two and at
positive shape `η`, `det R ^ q` is integrable exactly for `q > -η`. Equality at the endpoint is
on the divergent side. -/
@[simp]
theorem integrable_rpow_det_lkjMeasure_iff (hp : 2 ≤ p) (hη : 0 < η) (q : ℝ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) (lkjMeasure p η) ↔ -η < q := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  let _ (ij : strictLowerTriangle p) :=
    isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
  have hdet :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) =
        (fun x : ℝ ↦ x ^ q) ∘
          fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det := rfl
  rw [hdet, ← (integrable_map_measure (g := fun x : ℝ ↦ x ^ q) (by fun_prop)
      (by fun_prop : AEMeasurable
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det) (lkjMeasure p η))),
    map_det_lkjMeasure_eq_map_det_partialCorrelationGram hη,
    integrable_map_measure (g := fun x : ℝ ↦ x ^ q) (by fun_prop)
      (by fun_prop : AEMeasurable (fun z ↦ (partialCorrelationGram z).det)
        (Measure.pi fun ij : strictLowerTriangle p ↦
          (betaMeasure (lkjPartialCorrelationShape p η ij)
            (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)))]
  have hcomp :
      (fun x : ℝ ↦ x ^ q) ∘
          (fun z : strictLowerTriangle p → ℝ ↦ (partialCorrelationGram z).det) =
        fun z : strictLowerTriangle p → ℝ ↦ (partialCorrelationGram z).det ^ q := by
    funext z
    rfl
  rw [hcomp]
  have hp' : ¬p ≤ 1 := by omega
  simpa only [lkjPartialCorrelationShape_eq, hp', false_or] using
    (integrable_rpow_det_partialCorrelationGram_pi_betaMeasure_lkj_iff
      (p := p) (q := q) hη)

/-- In dimensions zero and one, every determinant power under the positive-shape LKJ law is
integrable. -/
theorem integrable_rpow_det_lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) (q : ℝ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) (lkjMeasure p η) := by
  rw [lkjMeasure_of_le_one hp hη]
  exact integrable_dirac (by simp)

/-- In dimensions zero and one, every real determinant-power moment under a positive-shape LKJ
law equals one. -/
theorem integral_rpow_det_lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) (q : ℝ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ q ∂lkjMeasure p η = 1 := by
  rw [lkjMeasure_of_le_one hp hη, integral_dirac]
  simp

end TauCeti.Probability
