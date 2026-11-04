/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation
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

private theorem lkjPartialCorrelationShape_pos {p : ℕ} {η : ℝ} (hη : 0 < η)
    (ij : strictLowerTriangle p) : 0 < lkjPartialCorrelationShape p η ij := by
  have hcol : ij.1.2.val + 1 < p := by omega
  have hk : 1 ≤ p - 1 - ij.1.2.val := by omega
  unfold lkjPartialCorrelationShape
  have hk' : (1 : ℝ) ≤ (p - 1 - ij.1.2.val : ℕ) := by exact_mod_cast hk
  positivity

private theorem integral_Ioo_one_sub_sq_rpow {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioo (-1 : ℝ) 1, (1 - x ^ 2) ^ (a - 1) = beta (1 / 2) a := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hchange :
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (a - 1)) =
        2 * ∫ t in (0 : ℝ)..1, (1 - (-1 + 2 * t) ^ 2) ^ (a - 1) := by
    rw [← smul_eq_mul]
    symm
    convert intervalIntegral.smul_integral_comp_add_mul
      (f := fun x : ℝ ↦ (1 - x ^ 2) ^ (a - 1)) (a := 0) (b := 1) 2 (-1) using 1;
      norm_num
  rw [hchange]
  have hintegrand :
      (∫ t in (0 : ℝ)..1, (1 - (-1 + 2 * t) ^ 2) ^ (a - 1)) =
        (4 : ℝ) ^ (a - 1) *
          ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (a - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_le zero_le_one] using ht
    have ht0 : 0 ≤ t := ht'.1.le
    have ht1 : 0 ≤ 1 - t := by linarith [ht'.2]
    dsimp only
    rw [show 1 - (-1 + 2 * t) ^ 2 = 4 * (t * (1 - t)) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg ht0 ht1), Real.mul_rpow ht0 ht1]
  rw [hintegrand, integral_rpow_mul_one_sub_rpow ha ha]
  have hpow : 2 * (4 : ℝ) ^ (a - 1) = (2 : ℝ) ^ (2 * a - 1) := by
    calc
      _ = 2 * (2 : ℝ) ^ (2 * a - 2) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast 2 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2
        ring
      _ = _ := by
        rw [show 2 * a - 1 = (2 * a - 2) + 1 by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        ring
  calc
    2 * ((4 : ℝ) ^ (a - 1) * beta a a) =
        (2 * (4 : ℝ) ^ (a - 1)) * beta a a := by ring
    _ = (2 : ℝ) ^ (2 * a - 1) * beta a a := by rw [hpow]
    _ = beta (1 / 2) a := (beta_one_half_left_eq_two_rpow_mul_beta_self ha).symm

private def strictLowerTriangleColumnEquiv {p : ℕ} (j : Fin p) :
    {ij : strictLowerTriangle p // ij.1.2 = j} ≃ Set.Ioi j where
  toFun ij := ⟨ij.1.1.1, by simpa [ij.2] using ij.1.2⟩
  invFun i := ⟨⟨(i.1, j), i.2⟩, rfl⟩
  left_inv ij := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl ij.2.symm
  right_inv i := by
    apply Subtype.ext
    rfl

private theorem card_strictLowerTriangle_column {p : ℕ} (j : Fin p) :
    Fintype.card {ij : strictLowerTriangle p // ij.1.2 = j} = p - 1 - j.val := by
  rw [Fintype.card_congr (strictLowerTriangleColumnEquiv j), Fintype.card_Ioi, Fin.card_Ioi]

private theorem prod_beta_lkjPartialCorrelationShape (p : ℕ) (η : ℝ) :
    (∏ ij : strictLowerTriangle p, beta (1 / 2) (lkjPartialCorrelationShape p η ij)) =
      lkjNormalizer p η := by
  unfold lkjPartialCorrelationShape
  rw [← Fintype.prod_fiberwise'
    (fun ij : strictLowerTriangle p ↦ ij.1.2)
    (fun j : Fin p ↦ beta (1 / 2)
      (η + (((p - 1 - j.val : ℕ) : ℝ) - 1) / 2))]
  simp_rw [Finset.prod_const, Finset.card_univ, card_strictLowerTriangle_column]
  change (∏ j : Fin p, (fun k : ℕ ↦
    beta (1 / 2) (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^ (p - 1 - k)) j) = _
  rw [Fin.prod_univ_eq_prod_range
    (fun k : ℕ ↦ beta (1 / 2) (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^
      (p - 1 - k)) p]
  rw [Finset.prod_range_reflect
    (fun k : ℕ ↦ beta (1 / 2) (η + (((k : ℕ) : ℝ) - 1) / 2) ^ k) p]
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Finset.prod_range_eq_mul_Ico _ (Nat.pos_of_ne_zero hp)]
    simp only [pow_zero, one_mul]
    exact (lkjNormalizer_def p η).symm

/-- The partial-correlation product kernel integrates over the open cube to the LKJ normalizing
constant.  Each coordinate contributes `B(1/2, a)`, where `a` is its column-dependent shape. -/
theorem integral_lkjPartialCorrelationKernel {p : ℕ} {η : ℝ} (hη : 0 < η) :
    ∫ z in Set.univ.pi (fun _ : strictLowerTriangle p ↦ Ioo (-1 : ℝ) 1),
        lkjPartialCorrelationKernel p η z = lkjNormalizer p η := by
  rw [volume_pi, Measure.restrict_pi_pi]
  change (∫ z : strictLowerTriangle p → ℝ,
    ∏ ij, (1 - z ij ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1)
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioo (-1 : ℝ) 1))) = _
  rw [integral_fintype_prod_eq_prod
    (fun ij : strictLowerTriangle p ↦
      fun x : ℝ ↦ (1 - x ^ 2) ^ (lkjPartialCorrelationShape p η ij - 1))]
  simp_rw [integral_Ioo_one_sub_sq_rpow (lkjPartialCorrelationShape_pos hη _)]
  exact prod_beta_lkjPartialCorrelationShape p η

end TauCeti.Probability
