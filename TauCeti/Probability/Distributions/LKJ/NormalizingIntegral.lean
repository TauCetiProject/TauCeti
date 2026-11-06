/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral

/-!
# The LKJ normalizing integral

The density of the LKJ law of shape `η` on `p × p` correlation matrices is proportional to
`det R ^ (η - 1)`. This file proves that `TauCeti.Probability.lkjNormalizer` is the integral it is
named for: for `0 < η`,

`∫ x in posDefCorrelationRegion p, det (correlationMatrix p x) ^ (η - 1) = lkjNormalizer p η`,

both in strictly lower correlation coordinates and against the reference measure
`TauCeti.correlationLebesgue p`. The proof changes variables to partial correlations
(`TauCeti.setIntegral_comp_correlationCoordinatesOfPartialCorrelation`), where the determinant and
the Jacobian both factor into powers of the residual variances `1 - z ^ 2`, so that the integrand
becomes the product kernel `TauCeti.Probability.lkjPartialCorrelationKernel`, whose integral over
the open cube is `TauCeti.Probability.integral_lkjPartialCorrelationKernel`.

## Main declarations

* `TauCeti.Probability.setIntegral_rpow_det_posDefCorrelationRegion`,
  `TauCeti.Probability.integrableOn_rpow_det_posDefCorrelationRegion` — the normalizing integral
  in correlation coordinates.
* `TauCeti.Probability.setIntegral_rpow_det_correlationLebesgue`,
  `TauCeti.Probability.integrableOn_rpow_det_correlationLebesgue` — the same integral against
  `TauCeti.correlationLebesgue p`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- On the open cube the Jacobian-weighted power of the determinant is the LKJ partial-correlation
product kernel. -/
private theorem jacobian_mul_det_rpow {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    (∏ ij : strictLowerTriangle p, Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2)) •
        (correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
      lkjPartialCorrelationKernel p η z := by
  have hpos (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  rw [lkjPartialCorrelationKernel_def,
    coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation fun ij ↦ (hz ij).le,
    det_partialCorrelationGram fun ij ↦ (hz ij).le,
    ← Real.finsetProd_rpow _ _ (fun ij _ ↦ (hpos ij).le), smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ ↦ ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hpos ij).le,
    ← Real.rpow_add (hpos ij)]
  congr 1
  have hlt : ij.1.2.val < ij.1.1.val := ij.2
  have hp : ij.1.1.val < p := ij.1.1.isLt
  have hcol : p - 1 - ij.1.2.val = (p - ij.1.2.val - 2) + 1 := by omega
  rw [lkjPartialCorrelationShape_def, hcol]
  push_cast
  ring

/-- The open partial-correlation cube as a product of open intervals. -/
private theorem partialCorrelationCube_eq_pi :
    {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} = univ.pi fun _ ↦ Ioo (-1) 1 := by
  ext z
  simp [abs_lt]

private theorem measurableSet_partialCorrelationCube :
    MeasurableSet {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} := by
  rw [partialCorrelationCube_eq_pi]
  exact .univ_pi fun _ ↦ measurableSet_Ioo

variable (p) in
/-- For positive shape `η`, the power `det R ^ (η - 1)` of the determinant of a correlation
matrix is integrable over the positive-definite correlation region. -/
theorem integrableOn_rpow_det_posDefCorrelationRegion (hη : 0 < η) :
    IntegrableOn (fun x ↦ (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
      (posDefCorrelationRegion p) := by
  rw [← integrableOn_comp_correlationCoordinatesOfPartialCorrelation_iff,
    integrableOn_congr_fun (fun z hz ↦ jacobian_mul_det_rpow hz)
      measurableSet_partialCorrelationCube, partialCorrelationCube_eq_pi]
  exact integrableOn_lkjPartialCorrelationKernel hη

variable (p) in
/-- **The LKJ normalizing constant as an integral.** For positive shape `η`, the integral of
`det R ^ (η - 1)` over the coordinates of the positive-definite correlation matrices is
`lkjNormalizer p η`. -/
theorem setIntegral_rpow_det_posDefCorrelationRegion (hη : 0 < η) :
    ∫ x in posDefCorrelationRegion p,
        (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
      lkjNormalizer p η := by
  rw [← setIntegral_comp_correlationCoordinatesOfPartialCorrelation,
    setIntegral_congr_fun measurableSet_partialCorrelationCube
      fun z hz ↦ jacobian_mul_det_rpow hz, partialCorrelationCube_eq_pi]
  exact integral_lkjPartialCorrelationKernel hη

variable (p) in
/-- For positive shape `η`, the power `det R ^ (η - 1)` is integrable over the positive-definite
correlation matrices with respect to the reference measure `TauCeti.correlationLebesgue p`. -/
theorem integrableOn_rpow_det_correlationLebesgue (hη : 0 < η) :
    IntegrableOn (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
      {R | (R : Matrix (Fin p) (Fin p) ℝ).PosDef} (correlationLebesgue p) :=
  ((measurePreserving_correlationMatrix p).integrableOn_comp_preimage
    (measurableEmbedding_correlationMatrix p)).1 <| by
      rw [preimage_correlationMatrix_setOf_posDef]
      exact integrableOn_rpow_det_posDefCorrelationRegion p hη

variable (p) in
/-- For positive shape `η`, the integral of `det R ^ (η - 1)` over the positive-definite
correlation matrices with respect to `TauCeti.correlationLebesgue p` is `lkjNormalizer p η`. -/
theorem setIntegral_rpow_det_correlationLebesgue (hη : 0 < η) :
    ∫ R in {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) ∂correlationLebesgue p = lkjNormalizer p η := by
  rw [← (measurePreserving_correlationMatrix p).setIntegral_preimage_emb
    (measurableEmbedding_correlationMatrix p), preimage_correlationMatrix_setOf_posDef]
  exact setIntegral_rpow_det_posDefCorrelationRegion p hη

end TauCeti.Probability
