/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
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

## Main declarations

* `TauCeti.Probability.lkjPartialCorrelationShape` — the beta shape attached to a strict lower
  coordinate;
* `TauCeti.Probability.lkjPartialCorrelationKernel` — the product kernel in partial-correlation
  coordinates;
* `TauCeti.Probability.integrableOn_lkjPartialCorrelationKernel` and
  `TauCeti.Probability.lkjPartialCorrelationKernel_nonneg` — its integrability and nonnegativity
  on the open cube;
* `TauCeti.Probability.integral_lkjPartialCorrelationKernel` — its integral over the open cube.

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

private theorem prod_beta_lkjPartialCorrelationShape (p : ℕ) (η : ℝ) :
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

end TauCeti.Probability
