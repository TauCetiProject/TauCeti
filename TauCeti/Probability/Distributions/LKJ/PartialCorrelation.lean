/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.Normalizer
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
public import Mathlib.Probability.Distributions.Beta
import TauCeti.Probability.Distributions.Beta.Symmetric
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Topology.Constructions.Pi

/-!
# Independent partial correlations of the LKJ law

In partial-correlation coordinates the LKJ density of shape `η > 0` factors into independent
one-dimensional densities. The partial correlation in zero-based column `j` of a `p × p`
correlation matrix is a centered symmetric Beta variable of shape `η + (p - j - 2) / 2`: if `X`
has law `Beta(η + (p - j - 2) / 2, η + (p - j - 2) / 2)`, then the partial correlation has the
law of `-1 + 2 * X`.

This file proves both directions of this correspondence as identities of measures on the
strictly lower correlation coordinates, where the LKJ law has density
`det R ^ (η - 1) / lkjNormalizer p η` on the positive-definite correlation region with respect to
Lebesgue measure. These coordinates are identified with unit-diagonal symmetric matrices by
`TauCeti.correlationMatrix`, which carries Lebesgue measure to `TauCeti.correlationLebesgue p`.

The proof is a change of variables through `TauCeti.correlationCoordinatesOfPartialCorrelation`.
On the open cube the determinant and the Jacobian both factor into powers of the residual
variances `1 - z ^ 2`, and the normalizer factors into the matching Beta constants. Thus the
product of the Beta densities equals the Jacobian times the LKJ density pointwise, and no integral
needs to be evaluated.

## Main results

* `TauCeti.Probability.map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure`: the
  correlation matrix built from independent centered symmetric Beta partial correlations has the
  LKJ density, in correlation coordinates;
  `map_correlationMatrix_map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure` states
  the same with respect to `TauCeti.correlationLebesgue p`.
* `TauCeti.Probability.map_partialCorrelationOfCorrelationCoordinates_withDensity`: conversely,
  the partial correlations of a correlation matrix with the LKJ density are independent centered
  symmetric Beta variables.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

private theorem natCast_sub_col (ij : strictLowerTriangle p) :
    ((p - ij.1.2.1 - 2 : ℕ) : ℝ) = (p : ℝ) - ij.1.2.val - 2 := by
  have : ij.1.2.val + 2 ≤ p := by
    have := ij.2
    have := ij.1.1.isLt
    omega
  push_cast [Nat.sub_sub, Nat.cast_sub this]
  ring

private theorem shape_pos (hη : 0 < η) (ij : strictLowerTriangle p) :
    0 < η + ((p : ℝ) - ij.1.2.val - 2) / 2 := by
  rw [← natCast_sub_col]
  positivity

/-- Independent centered symmetric Beta partial correlations lie in the open cube. -/
private theorem ae_abs_lt_one_pi_betaMeasure (hη : 0 < η) :
    ∀ᵐ z ∂Measure.pi (fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x)),
      ∀ ij, |z ij| < 1 := by
  let _ (ij : strictLowerTriangle p) :
      IsProbabilityMeasure (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
        (η + ((p : ℝ) - ij.1.2.val - 2) / 2)) :=
    isProbabilityMeasureBeta (shape_pos hη ij) (shape_pos hη ij)
  refine Filter.eventually_all.2 fun ij ↦ ?_
  have hij : ∀ᵐ z ∂(betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
      (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x), |z| < 1 := by
    refine (ae_map_iff (by fun_prop) (by measurability)).2 ?_
    filter_upwards [ae_mem_Ioo_betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
      (η + ((p : ℝ) - ij.1.2.val - 2) / 2)] with x hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact (Measure.tendsto_eval_ae_ae (i := ij) (μ := fun ij : strictLowerTriangle p ↦
    (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
      (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x))).eventually hij

/-- On the open cube, the Jacobian of the partial-correlation map times the LKJ density is the
product of the centered symmetric Beta densities of the partial correlations. -/
private theorem prod_sqrt_pow_mul_lkj_density {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| < 1) :
    (∏ ij : strictLowerTriangle p, Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2)) *
        ((correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η) =
      ∏ ij : strictLowerTriangle p,
        (1 - z ij ^ 2) ^ (η + ((p : ℝ) - ij.1.2.val - 2) / 2 - 1) /
          beta (1 / 2) (η + ((p : ℝ) - ij.1.2.val - 2) / 2) := by
  have hpos (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  rw [coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation fun ij ↦ (hz ij).le,
    det_partialCorrelationGram fun ij ↦ (hz ij).le,
    ← Real.finsetProd_rpow _ _ fun ij _ ↦ (hpos ij).le, lkjNormalizer_eq_prod_strictLowerTriangle,
    ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ ↦ ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hpos ij).le, mul_div_assoc',
    ← Real.rpow_add (hpos ij), natCast_sub_col]
  congr 2
  ring

/-- **Independent-Beta construction of the LKJ law.** If the partial correlation in zero-based
column `j` is `-1 + 2 * X` for independent `X ~ Beta(η + (p - j - 2) / 2, η + (p - j - 2) / 2)`,
then the resulting correlation matrix has density `det R ^ (η - 1) / lkjNormalizer p η` on the
positive-definite correlation region, in strictly lower correlation coordinates. Dimensions are
cast to the reals before subtraction and division. -/
theorem map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure (hη : 0 < η) :
    (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x)).map
        correlationCoordinatesOfPartialCorrelation =
      (volume.restrict (posDefCorrelationRegion p)).withDensity fun x ↦
        ENNReal.ofReal ((correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
          lkjNormalizer p η) := by
  set D : strictLowerTriangle p → ℝ → ENNReal := fun ij ↦ (Ioo (-1) 1).indicator fun t ↦
    ENNReal.ofReal ((1 - t ^ 2) ^ (η + ((p : ℝ) - ij.1.2.val - 2) / 2 - 1) /
      beta (1 / 2) (η + ((p : ℝ) - ij.1.2.val - 2) / 2))
  set cube := {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1}
  have hcube : MeasurableSet cube := isOpen_setOf_forall_abs_lt_one.measurableSet
  have hD (ij : strictLowerTriangle p) : Measurable (D ij) :=
    (Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioo
  have hfactor (ij : strictLowerTriangle p) :
      (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
        (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x) =
        volume.withDensity (D ij) :=
    betaMeasure_map_centered_eq_withDensity (shape_pos hη ij)
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (volume.withDensity (D ij)) := by
    rw [← hfactor]
    have := isProbabilityMeasureBeta (shape_pos hη ij) (shape_pos hη ij)
    infer_instance
  simp_rw [hfactor]
  rw [pi_withDensity _ hD, ← volume_pi]
  refine Measure.map_withDensity_eq_withDensity
    (jac := cube.indicator fun z ↦ ENNReal.ofReal
      (∏ ij : strictLowerTriangle p, Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2)))
    continuous_correlationCoordinatesOfPartialCorrelation.measurable
    ((Measurable.ennreal_ofReal (by fun_prop)).indicator hcube) (by fun_prop) ?_
    (Filter.Eventually.of_forall fun z ↦ ?_)
  · rw [withDensity_indicator hcube]
    exact map_withDensity_correlationCoordinatesOfPartialCorrelation
  · by_cases hz : z ∈ cube
    · have hpos (ij : strictLowerTriangle p) :
          0 ≤ (1 - z ij ^ 2) ^ (η + ((p : ℝ) - ij.1.2.val - 2) / 2 - 1) /
            beta (1 / 2) (η + ((p : ℝ) - ij.1.2.val - 2) / 2) :=
        div_nonneg (Real.rpow_nonneg (by nlinarith [abs_lt.1 (hz ij), sq_abs (z ij)]) _)
          (beta_pos (by norm_num) (shape_pos hη ij)).le
      have hmem (ij : strictLowerTriangle p) : z ij ∈ Ioo (-1) 1 := abs_lt.1 (hz ij)
      rw [indicator_of_mem hz, ← ENNReal.ofReal_mul (by positivity),
        prod_sqrt_pow_mul_lkj_density hz, ENNReal.ofReal_prod_of_nonneg fun ij _ ↦ hpos ij]
      exact Finset.prod_congr rfl fun ij _ ↦ by simp only [D, indicator_of_mem (hmem ij)]
    · obtain ⟨ij, hij⟩ := not_forall.1 hz
      rw [indicator_of_notMem hz, zero_mul]
      have hij' : z ij ∉ Ioo (-1) 1 := fun h ↦ hij (abs_lt.2 h)
      exact (Finset.prod_eq_zero (Finset.mem_univ ij)
        (by simp only [D, indicator_of_notMem hij'])).symm

/-- **Independent-Beta construction of the LKJ law, as random matrices.** The correlation matrix
built from independent centered symmetric Beta partial correlations, with the shapes of
`TauCeti.Probability.map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure`, has density
`det R ^ (η - 1) / lkjNormalizer p η` on the positive-definite cone with respect to
`TauCeti.correlationLebesgue p`. -/
theorem map_correlationMatrix_map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure
    (hη : 0 < η) :
    ((Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x)).map
        correlationCoordinatesOfPartialCorrelation).map (correlationMatrix p) =
      (correlationLebesgue p).withDensity
        ({R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator fun R ↦
          ENNReal.ofReal ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η)) := by
  have hdet : Continuous fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ).det :=
    (continuous_id.matrix_det).comp continuous_subtype_val
  rw [map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure hη,
    ← withDensity_indicator (measurableSet_posDefCorrelationRegion p),
    ← map_correlationMatrix_withDensity
      ((Measurable.ennreal_ofReal (by fun_prop)).indicator (measurableSet_posDefMatrix p))]
  congr 2
  funext x
  by_cases hx : x ∈ posDefCorrelationRegion p
  · rw [indicator_of_mem hx, indicator_of_mem (mem_posDefCorrelationRegion.1 hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (mt mem_posDefCorrelationRegion.2 hx)]

/-- **Independence of the LKJ partial correlations.** The partial correlations of a correlation
matrix whose strictly lower coordinates have density `det R ^ (η - 1) / lkjNormalizer p η` on the
positive-definite correlation region are independent. The one in zero-based column `j` is
`-1 + 2 * X` for `X ~ Beta(η + (p - j - 2) / 2, η + (p - j - 2) / 2)`. Dimensions are cast to the
reals before subtraction and division. -/
theorem map_partialCorrelationOfCorrelationCoordinates_withDensity (hη : 0 < η) :
    ((volume.restrict (posDefCorrelationRegion p)).withDensity fun x ↦
        ENNReal.ofReal ((correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
          lkjNormalizer p η)).map partialCorrelationOfCorrelationCoordinates =
      Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x) := by
  rw [← map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure hη,
    Measure.map_map measurable_partialCorrelationOfCorrelationCoordinates
      continuous_correlationCoordinatesOfPartialCorrelation.measurable]
  conv_rhs => rw [← Measure.map_id (μ := Measure.pi _)]
  refine Measure.map_congr ?_
  filter_upwards [ae_abs_lt_one_pi_betaMeasure hη] with z hz
  exact partialCorrelationOfCorrelationCoordinates_correlationCoordinatesOfPartialCorrelation hz

end TauCeti.Probability
