/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Symmetric
public import TauCeti.Probability.Distributions.LKJ.Basic
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Constructing the LKJ law from independent Beta variables

For positive shape `η`, attach to each strict lower-triangular position in column `j` an
independent symmetric Beta variable with shape `η + (p - j - 2) / 2`, centered onto `(-1, 1)`.
The partial-correlation Gram construction sends their product law to `lkjMeasure p η`.

The proof first writes the product law as a Lebesgue density on the open partial-correlation
cube. The Jacobian of the partial-correlation parametrization and the determinant power in the
LKJ density combine to exactly that product density. A final affine coordinate map identifies
Lebesgue measure on strict lower entries with `correlationLebesgue`.

## Main declarations

* `TauCeti.Probability.lkjPartialCorrelationMeasure` is the product law of the independent
  centered symmetric Beta partial correlations.
* `TauCeti.Probability.map_correlationMatrix_lkjPartialCorrelationMeasure` identifies its image
  under the partial-correlation construction with the LKJ law.
* `TauCeti.Probability.map_partialCorrelationGram_lkjPartialCorrelationMeasure` gives the same
  construction as a law on raw matrices.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The product law of independent centered symmetric Beta partial correlations for the LKJ law
of dimension `p` and shape `η`.

The coordinate in zero-based column `j` has symmetric Beta shape
`lkjPartialCorrelationShape p η ij = η + (p - j - 2) / 2`, before the affine centering
`x ↦ -1 + 2x`. -/
def lkjPartialCorrelationMeasure (p : ℕ) (η : ℝ) :
    Measure (strictLowerTriangle p → ℝ) :=
  Measure.pi fun ij ↦
    (betaMeasure (lkjPartialCorrelationShape p η ij)
      (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)

/-- The independent partial-correlation law is a probability measure at positive LKJ shape. -/
theorem isProbabilityMeasure_lkjPartialCorrelationMeasure {p : ℕ} {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (lkjPartialCorrelationMeasure p η) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure
      (betaMeasure (lkjPartialCorrelationShape p η ij)
        (lkjPartialCorrelationShape p η ij)) :=
    isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
  unfold lkjPartialCorrelationMeasure
  infer_instance

private def partialCorrelationCube (p : ℕ) : Set (strictLowerTriangle p → ℝ) :=
  {z | ∀ ij, |z ij| < 1}

private theorem measurableSet_partialCorrelationCube (p : ℕ) :
    MeasurableSet (partialCorrelationCube p) := by
  have hpi : MeasurableSet
      (Set.univ.pi fun _ : strictLowerTriangle p ↦ Set.Ioo (-1 : ℝ) 1) :=
    .univ_pi fun _ ↦ measurableSet_Ioo
  convert hpi using 1
  ext z
  simp only [partialCorrelationCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_const, Set.mem_Ioo]
  exact forall_congr' fun _ ↦ abs_lt

private theorem isOpen_partialCorrelationCube (p : ℕ) : IsOpen (partialCorrelationCube p) := by
  rw [show partialCorrelationCube p =
    Set.univ.pi (fun _ : strictLowerTriangle p ↦ Set.Ioo (-1 : ℝ) 1) by
      ext z
      simp only [partialCorrelationCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
        forall_const, Set.mem_Ioo]
      exact forall_congr' fun _ ↦ abs_lt]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo

private theorem hasFDerivWithinAt_partialCorrelationCoordinates
    {p : ℕ} {z : strictLowerTriangle p → ℝ} (hz : z ∈ partialCorrelationCube p) :
    HasFDerivWithinAt (correlationCoordinatesOfPartialCorrelation (p := p))
      (fderiv ℝ correlationCoordinatesOfPartialCorrelation z) (partialCorrelationCube p) z :=
  ((contDiffOn_correlationCoordinatesOfPartialCorrelation.differentiableOn
    (by simp)).differentiableAt ((isOpen_partialCorrelationCube p).mem_nhds hz)).hasFDerivAt
      |>.hasFDerivWithinAt

private def partialCorrelationCoordinatePDF (p : ℕ) (η : ℝ)
    (ij : strictLowerTriangle p) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((1 - z ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1) /
      beta (1 / 2) (lkjPartialCorrelationShape p η ij))

private theorem measurable_partialCorrelationCoordinatePDF (p : ℕ) (η : ℝ)
    (ij : strictLowerTriangle p) : Measurable (partialCorrelationCoordinatePDF p η ij) := by
  unfold partialCorrelationCoordinatePDF
  fun_prop

private theorem lkjPartialCorrelationMeasure_eq_withDensity {p : ℕ} {η : ℝ} (hη : 0 < η) :
    lkjPartialCorrelationMeasure p η =
      (volume.restrict (partialCorrelationCube p)).withDensity
        (fun z ↦ ∏ ij, partialCorrelationCoordinatePDF p η ij (z ij)) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure
      ((betaMeasure (lkjPartialCorrelationShape p η ij)
        (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) := by
    let _ : IsProbabilityMeasure
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)) :=
      isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
        (lkjPartialCorrelationShape_pos hη ij)
    infer_instance
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure
      ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
        (partialCorrelationCoordinatePDF p η ij)) := by
    change IsProbabilityMeasure
      ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
        (fun z ↦ ENNReal.ofReal
          ((1 - z ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1) /
            beta (1 / 2) (lkjPartialCorrelationShape p η ij))))
    rw [← map_centered_betaMeasure_eq_withDensity (lkjPartialCorrelationShape_pos hη ij)]
    infer_instance
  rw [lkjPartialCorrelationMeasure]
  simp_rw [map_centered_betaMeasure_eq_withDensity (lkjPartialCorrelationShape_pos hη _)]
  change Measure.pi (fun ij ↦
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
        (partialCorrelationCoordinatePDF p η ij)) = _
  rw [pi_withDensity _ (measurable_partialCorrelationCoordinatePDF p η),
    ← Measure.restrict_pi_pi, ← volume_pi]
  congr 2
  ext z
  simp only [partialCorrelationCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_const, Set.mem_Ioo]
  exact forall_congr' fun _ ↦ abs_lt.symm

private def partialCorrelationJacobian (p : ℕ) (z : strictLowerTriangle p → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ ij : strictLowerTriangle p,
    Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2))

private theorem measurable_partialCorrelationJacobian (p : ℕ) :
    Measurable (partialCorrelationJacobian p) := by
  unfold partialCorrelationJacobian
  fun_prop

private def lkjCoordinateDensity (p : ℕ) (η : ℝ) (x : strictLowerTriangle p → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
      lkjNormalizer p η)

private theorem measurable_lkjCoordinateDensity (p : ℕ) (η : ℝ) :
    Measurable (lkjCoordinateDensity p η) := by
  unfold lkjCoordinateDensity
  fun_prop

private theorem jacobian_mul_lkjCoordinateDensity {p : ℕ} {η : ℝ} (hη : 0 < η)
    {z : strictLowerTriangle p → ℝ} (hz : z ∈ partialCorrelationCube p) :
    partialCorrelationJacobian p z *
        lkjCoordinateDensity p η (correlationCoordinatesOfPartialCorrelation z) =
      ∏ ij, partialCorrelationCoordinatePDF p η ij (z ij) := by
  have hres (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  have hbeta (ij : strictLowerTriangle p) :
      0 < beta (1 / 2) (lkjPartialCorrelationShape p η ij) :=
    beta_pos (by norm_num) (lkjPartialCorrelationShape_pos hη ij)
  have hjac : 0 ≤ ∏ ij : strictLowerTriangle p,
      Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2) := by positivity
  rw [partialCorrelationJacobian, lkjCoordinateDensity,
    ← ENNReal.ofReal_mul hjac]
  unfold partialCorrelationCoordinatePDF
  rw [← ENNReal.ofReal_prod_of_nonneg fun ij _ ↦
    div_nonneg (Real.rpow_nonneg (hres ij).le _) (hbeta ij).le]
  apply congrArg ENNReal.ofReal
  rw [Finset.prod_div_distrib, prod_beta_lkjPartialCorrelationShape,
    ← lkjPartialCorrelationKernel_def]
  rw [← jacobian_mul_det_rpow (p := p) (η := η) hz]
  ring

private theorem map_partialCorrelationCoordinates_lkjPartialCorrelationMeasure
    {p : ℕ} {η : ℝ} (hη : 0 < η) :
    (lkjPartialCorrelationMeasure p η).map
        (correlationCoordinatesOfPartialCorrelation (p := p)) =
      (volume.restrict (posDefCorrelationRegion p)).withDensity
        (lkjCoordinateDensity p η) := by
  let f := correlationCoordinatesOfPartialCorrelation (p := p)
  have hf : Measurable f := continuous_correlationCoordinatesOfPartialCorrelation.measurable
  have hmap :
      ((volume.restrict (partialCorrelationCube p)).withDensity
        (partialCorrelationJacobian p)).map f =
        volume.restrict (posDefCorrelationRegion p) := by
    have hcov := map_withDensity_abs_det_fderiv_eq_addHaar
      (volume : Measure (strictLowerTriangle p → ℝ))
      (measurableSet_partialCorrelationCube p).nullMeasurableSet
      (fun _ hz ↦ hasFDerivWithinAt_partialCorrelationCoordinates hz)
      injOn_correlationCoordinatesOfPartialCorrelation
    rw [show (volume.restrict (partialCorrelationCube p)).withDensity
        (partialCorrelationJacobian p) =
        (volume.restrict (partialCorrelationCube p)).withDensity
          (fun z ↦ ENNReal.ofReal
            |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det|) by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_partialCorrelationCube p)] with z hz
      rw [partialCorrelationJacobian,
        abs_det_fderiv_correlationCoordinatesOfPartialCorrelation hz]]
    rw [show partialCorrelationCube p =
        {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} by rfl,
      image_correlationCoordinatesOfPartialCorrelation] at hcov
    change ((volume.restrict (partialCorrelationCube p)).withDensity
        (fun z ↦ ENNReal.ofReal
          |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det|)).map
        (correlationCoordinatesOfPartialCorrelation (p := p)) =
      volume.restrict (posDefCorrelationRegion p) at hcov
    simpa [f] using hcov
  rw [lkjPartialCorrelationMeasure_eq_withDensity hη]
  exact Measure.map_withDensity_eq_withDensity hf
    (measurable_partialCorrelationJacobian p)
    (measurable_lkjCoordinateDensity p η) hmap <|
      (ae_restrict_mem (measurableSet_partialCorrelationCube p)).mono fun z hz ↦
        jacobian_mul_lkjCoordinateDensity hη hz

/-- **Independent-Beta construction of the LKJ law.** The correlation matrix obtained from
independent centered symmetric Beta partial correlations has the LKJ law. -/
theorem map_correlationMatrix_lkjPartialCorrelationMeasure {p : ℕ} {η : ℝ} (hη : 0 < η) :
    (lkjPartialCorrelationMeasure p η).map
        (fun z ↦ correlationMatrix p (correlationCoordinatesOfPartialCorrelation z)) =
      lkjMeasure p η := by
  have hcomp : (fun z ↦ correlationMatrix p (correlationCoordinatesOfPartialCorrelation z)) =
      correlationMatrix p ∘ correlationCoordinatesOfPartialCorrelation := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop)
    continuous_correlationCoordinatesOfPartialCorrelation.measurable,
    map_partialCorrelationCoordinates_lkjPartialCorrelationMeasure hη,
    ← withDensity_indicator (measurableSet_posDefCorrelationRegion p)]
  have hweight : (posDefCorrelationRegion p).indicator (lkjCoordinateDensity p η) =
      lkjPDF p η ∘ correlationMatrix p := by
    funext x
    by_cases hx : x ∈ posDefCorrelationRegion p
    · rw [Set.indicator_of_mem hx, Function.comp_apply, lkjCoordinateDensity,
        lkjPDF_of_posDef p η (mem_posDefCorrelationRegion.1 hx)]
    · rw [Set.indicator_of_notMem hx, Function.comp_apply,
        lkjPDF_of_not_posDef p η (mt mem_posDefCorrelationRegion.2 hx)]
  rw [hweight, Measure.map_withDensity_comp (correlationMatrix p).continuous.measurable
    (measurable_lkjPDF p η), (measurePreserving_correlationMatrix p).map_eq,
    ← lkjMeasure_of_pos hη]

/-- The raw Gram matrix built from independent centered symmetric Beta partial correlations has
the image of the LKJ law under the coercion from self-adjoint matrices to matrices. -/
theorem map_partialCorrelationGram_lkjPartialCorrelationMeasure {p : ℕ} {η : ℝ} (hη : 0 < η) :
    (lkjPartialCorrelationMeasure p η).map partialCorrelationGram =
      (lkjMeasure p η).map
        (Subtype.val : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →
          Matrix (Fin p) (Fin p) ℝ) := by
  let _ := isProbabilityMeasure_lkjPartialCorrelationMeasure (p := p) hη
  rw [← map_correlationMatrix_lkjPartialCorrelationMeasure hη,
    Measure.map_map continuous_subtype_val.measurable (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [ae_abs_le_one_pi_centered_betaMeasure
    (fun ij ↦ lkjPartialCorrelationShape_pos hη ij)] with z hz
  exact (coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation hz).symm

end TauCeti.Probability
