/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
public import TauCeti.Probability.Distributions.LKJ.Normalizer
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The LKJ integral in partial-correlation coordinates

The partial-correlation parametrization turns the LKJ determinant density, together with its
Jacobian, into a product of one-dimensional symmetric beta kernels.  This file evaluates that
product over the open partial-correlation cube and identifies its value with `lkjNormalizer`.

For a coordinate in zero-based column `j`, put `k = p - 1 - j`.  There are exactly `k`
coordinates in that column, and their common symmetric-beta shape is
`eta + (k - 1) / 2`. Fubini's theorem therefore gives one beta factor for each coordinate;
grouping by columns recovers the defining product for the LKJ normalizer.

Changing variables to partial correlations, where the determinant and the Jacobian both factor
into powers of the residual variances `1 - z ^ 2`, turns the integral of `det R ^ (η - 1)` over
the positive-definite correlation matrices into this product integral. So for `0 < η`

`∫ x in posDefCorrelationRegion p, det (correlationMatrix p x) ^ (η - 1) = lkjNormalizer p η`,

both in strictly lower correlation coordinates and against the reference measure
`TauCeti.correlationLebesgue p`.

## Main declarations

* `TauCeti.Probability.lkjPartialCorrelationShape` — the beta shape attached to a strict lower
  coordinate;
* `TauCeti.Probability.lkjPartialCorrelationKernel` — the product kernel in partial-correlation
  coordinates;
* `TauCeti.Probability.integrableOn_lkjPartialCorrelationKernel` and
  `TauCeti.Probability.lkjPartialCorrelationKernel_nonneg` — its integrability and nonnegativity
  on the open cube;
* `TauCeti.Probability.prod_beta_lkjPartialCorrelationShape` — the LKJ normalizer as a product of
  one beta factor per coordinate;
* `TauCeti.Probability.integral_lkjPartialCorrelationKernel` — its integral over the open cube.
* `TauCeti.Probability.prod_sqrt_pow_smul_rpow_det_eq_lkjPartialCorrelationKernel` — on the open
  cube, the Jacobian times the determinant power is the product kernel.
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

open scoped BigOperators

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The symmetric-beta shape belonging to a strict lower partial-correlation coordinate.

In zero-based column `j`, the number `k = p - 1 - j` is both the number of coordinates in that
column and the index of the corresponding factor in `lkjNormalizer`. -/
def lkjPartialCorrelationShape (p : ℕ) (η : ℝ) (ij : strictLowerTriangle p) : ℝ :=
  η + (((p - 1 - ij.1.2.val : ℕ) : ℝ) - 1) / 2

/-- The formula for the symmetric-beta shape of a partial-correlation coordinate. -/
theorem lkjPartialCorrelationShape_def (p : ℕ) (η : ℝ) (ij : strictLowerTriangle p) :
    lkjPartialCorrelationShape p η ij =
      η + (((p - 1 - ij.1.2.val : ℕ) : ℝ) - 1) / 2 := by
  rfl

/-- The shape of a partial-correlation coordinate in zero-based column `j` is
`η + (p - j - 2) / 2`, with the dimension and column cast to the reals before subtraction. -/
theorem lkjPartialCorrelationShape_eq (p : ℕ) (η : ℝ) (ij : strictLowerTriangle p) :
    lkjPartialCorrelationShape p η ij = η + ((p : ℝ) - ij.1.2.val - 2) / 2 := by
  have hcol : ij.1.2.val + 1 < p := by omega
  rw [lkjPartialCorrelationShape_def, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The product of the unnormalized symmetric-beta kernels in partial-correlation coordinates.

The intended domain is the open cube on which every coordinate lies in `(-1, 1)`.  The formula is
left total outside that cube. -/
def lkjPartialCorrelationKernel (p : ℕ) (η : ℝ)
    (z : strictLowerTriangle p → ℝ) : ℝ :=
  ∏ ij, (1 - z ij ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1)

/-- The defining product for the LKJ partial-correlation kernel. -/
theorem lkjPartialCorrelationKernel_def (p : ℕ) (η : ℝ)
    (z : strictLowerTriangle p → ℝ) :
    lkjPartialCorrelationKernel p η z =
      ∏ ij, (1 - z ij ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1) := by
  rfl

/-- Every partial-correlation shape is positive when the LKJ shape parameter is positive. -/
theorem lkjPartialCorrelationShape_pos {p : ℕ} {η : ℝ} (hη : 0 < η)
    (ij : strictLowerTriangle p) : 0 < lkjPartialCorrelationShape p η ij := by
  have hcol : ij.1.2.val + 1 < p := by omega
  have hk : 1 ≤ p - 1 - ij.1.2.val := by omega
  unfold lkjPartialCorrelationShape
  have hk' : (1 : ℝ) ≤ (p - 1 - ij.1.2.val : ℕ) := by exact_mod_cast hk
  positivity

/-- The LKJ partial-correlation kernel is nonnegative on the open coordinate cube. -/
theorem lkjPartialCorrelationKernel_nonneg {p : ℕ} {η : ℝ}
    {z : strictLowerTriangle p → ℝ}
    (hz : z ∈ Set.univ.pi (fun _ : strictLowerTriangle p ↦ Ioo (-1 : ℝ) 1)) :
    0 ≤ lkjPartialCorrelationKernel p η z := by
  rw [lkjPartialCorrelationKernel_def]
  exact Finset.prod_nonneg fun ij _ ↦ Real.rpow_nonneg (by
    obtain ⟨hl, hu⟩ := hz ij (Set.mem_univ ij)
    nlinarith [mul_pos (show 0 < z ij + 1 by linarith)
      (show 0 < 1 - z ij by linarith)]) _

/-- For positive `η`, the LKJ partial-correlation kernel is integrable on the open coordinate
cube. -/
theorem integrableOn_lkjPartialCorrelationKernel {p : ℕ} {η : ℝ} (hη : 0 < η) :
    IntegrableOn (lkjPartialCorrelationKernel p η)
      (Set.univ.pi (fun _ : strictLowerTriangle p ↦ Ioo (-1 : ℝ) 1)) := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  unfold lkjPartialCorrelationKernel
  exact Integrable.fintype_prod fun ij ↦
    integrableOn_Ioo_one_sub_sq_rpow (lkjPartialCorrelationShape_pos hη ij)

/-- The LKJ normalizer has one factor `B(1 / 2, a)` for each partial-correlation coordinate,
where `a` is its column-dependent shape. -/
theorem prod_beta_lkjPartialCorrelationShape (p : ℕ) (η : ℝ) :
    (∏ ij : strictLowerTriangle p, beta (1 / 2) (lkjPartialCorrelationShape p η ij)) =
      lkjNormalizer p η := by
  unfold lkjPartialCorrelationShape
  rw [← Fintype.prod_fiberwise'
    (fun ij : strictLowerTriangle p ↦ ij.1.2)
    (fun j : Fin p ↦ beta (1 / 2)
      (η + (((p - 1 - j.val : ℕ) : ℝ) - 1) / 2))]
  simp_rw [Finset.prod_const, Finset.card_univ, card_strictLowerTriangle_column]
  calc
    _ = ∏ k ∈ Finset.range p,
        beta (1 / 2) (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^ (p - 1 - k) := by
      simpa only using Fin.prod_univ_eq_prod_range
        (fun k : ℕ ↦ beta (1 / 2) (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^
          (p - 1 - k)) p
    _ = lkjNormalizer p η := by
      rw [lkjNormalizer_eq_prod_columns]
      rcases p with _ | p
      · simp
      · rw [Finset.prod_range_succ]
        simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, zero_sub, pow_zero, mul_one]
        rw [Finset.prod_Ico_eq_prod_range]
        congr 1
        ext k
        have h : p + 1 - (1 + k) = p - k := by omega
        rw [h]

/-- The partial-correlation product kernel integrates over the open cube to the LKJ normalizing
constant.  Each coordinate contributes `B(1/2, a)`, where `a` is its column-dependent shape. -/
theorem integral_lkjPartialCorrelationKernel {p : ℕ} {η : ℝ} (hη : 0 < η) :
    ∫ z in Set.univ.pi (fun _ : strictLowerTriangle p ↦ Ioo (-1 : ℝ) 1),
        lkjPartialCorrelationKernel p η z = lkjNormalizer p η := by
  simp_rw [lkjPartialCorrelationKernel_def]
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod
    (fun ij : strictLowerTriangle p ↦
      fun x : ℝ ↦ (1 - x ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1))]
  simp_rw [integral_Ioo_one_sub_sq_rpow (lkjPartialCorrelationShape_pos hη _)]
  exact prod_beta_lkjPartialCorrelationShape p η

/-! ### The normalizing integral -/

variable {p : ℕ} {η : ℝ}

/-- On the open cube the Jacobian-weighted power of the determinant is the LKJ
partial-correlation kernel: both factor into one-dimensional powers of the residual variances
`1 - z ij ^ 2`. -/
theorem prod_sqrt_pow_smul_rpow_det_eq_lkjPartialCorrelationKernel
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    (∏ ij : strictLowerTriangle p, Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2)) •
        (correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
      lkjPartialCorrelationKernel p η z := by
  have hpos (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  rw [coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation fun ij ↦ (hz ij).le,
    det_partialCorrelationGram fun ij ↦ (hz ij).le,
    ← Real.finsetProd_rpow _ _ (fun ij _ ↦ (hpos ij).le), smul_eq_mul, ← Finset.prod_mul_distrib,
    lkjPartialCorrelationKernel_def]
  refine Finset.prod_congr rfl fun ij _ ↦ ?_
  have hcol : ij.1.2.val + 1 < p := by omega
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hpos ij).le,
    ← Real.rpow_add (hpos ij), lkjPartialCorrelationShape_def,
    show p - ij.1.2.1 - 2 = p - 1 - ij.1.2.1 - 1 by omega,
    Nat.cast_sub (show 1 ≤ p - 1 - ij.1.2.1 by omega), Nat.cast_one]
  congr 1
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
    integrableOn_congr_fun
      (fun z hz ↦ prod_sqrt_pow_smul_rpow_det_eq_lkjPartialCorrelationKernel hz)
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
      fun z hz ↦ prod_sqrt_pow_smul_rpow_det_eq_lkjPartialCorrelationKernel hz,
    partialCorrelationCube_eq_pi]
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
