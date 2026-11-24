/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Moments.SubGaussian.ExponentialMoments
import TauCeti.Probability.Moments.SubGaussian.LinearForms
import TauCeti.Probability.Moments.SubGaussian.SquaredSum
public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Probability.Independence.Matrix
import TauCeti.Probability.Moments.SampleMean

/-!
# Lower tails in a fixed matrix direction

For a real random matrix with independent rows, a uniform sub-Gaussian proxy for a direction
and a lower bound on its row second moments imply an exponential lower tail for the Euclidean
norm of the image. Independent centered entries with second moments bounded below supply
these hypotheses in every unit direction, even when the coordinate laws differ.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Corollary 2.7.
* R. Vershynin, *High-Dimensional Probability* (2018), §4.6.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
  {P : Measure Ω} {A : Ω → Matrix m n ℝ} {c : ℝ≥0}

/-- For independent rows, the image of a fixed vector has an exponential lower tail if the
row evaluations have a common sub-Gaussian variance proxy and their average second moment
is bounded below by `v`. The bound also holds for an empty row index. -/
theorem measureReal_norm_toEuclideanLin_lt_le_of_rows [DecidableEq n]
    (hind : iIndepFun (fun i ω ↦ (A ω).row i) P) (x : EuclideanSpace ℝ n)
    (hsub : ∀ i, HasSubgaussianMGF (fun ω ↦ A ω i ⬝ᵥ x) c P)
    {v : ℝ}
    (hmom : (Fintype.card m : ℝ) * v ≤ ∑ i, ∫ ω, (A ω i ⬝ᵥ x) ^ 2 ∂P) :
    P.real {ω | ‖toEuclideanLin (A ω) x‖ < Real.sqrt (v * Fintype.card m) / 2} ≤
      2 * Real.exp (-(1 / 1536) *
        min (v ^ 2 / (4 * (c : ℝ) ^ 2)) (v / (2 * (c : ℝ))) * Fintype.card m) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  by_cases hv : 0 ≤ v
  swap
  · have hsqrt : Real.sqrt (v * Fintype.card m) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) (by positivity))
    simp only [hsqrt, zero_div, not_lt.mpr (norm_nonneg _), Set.ofPred_false, measureReal_empty]
    positivity
  let d : ℝ := Fintype.card m
  let Y (i : m) (ω : Ω) := A ω i ⬝ᵥ x
  have hY : iIndepFun Y P :=
    hind.comp (fun _ (w : n → ℝ) ↦ w ⬝ᵥ x) (fun _ ↦ by fun_prop)
  have hd : 0 ≤ d := by positivity
  have htail := hY.measureReal_abs_sum_sq_sub_integral_gt_le hsub
    (t := v * d / 2) (by positivity)
  have hsubsets : {ω | ‖toEuclideanLin (A ω) x‖ < Real.sqrt (v * d) / 2} ⊆
      {ω | v * d / 2 < |∑ i, (Y i ω ^ 2 - ∫ ω', Y i ω' ^ 2 ∂P)|} := by
    intro ω hω
    have hnorm : ‖toEuclideanLin (A ω) x‖ ^ 2 = ∑ i, Y i ω ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Matrix.toLpLin_apply, Matrix.mulVec, Y,
        toEuclideanLin]
    have hω' : ‖toEuclideanLin (A ω) x‖ < Real.sqrt (v * d) / 2 := hω
    have hsq := pow_lt_pow_left₀ hω' (norm_nonneg _) two_ne_zero
    rw [hnorm, div_pow, Real.sq_sqrt (mul_nonneg hv hd)] at hsq
    rw [Set.mem_ofPred_eq, sum_sub_distrib, lt_abs]
    right
    have hmean : v * d ≤ ∑ i, ∫ ω', Y i ω' ^ 2 ∂P := by
      rw [mul_comm v d]
      exact hmom
    linarith only [hsq, hmean, mul_nonneg hv hd]
  have hrate : min ((v * d / 2) ^ 2 / ((c : ℝ) ^ 2 * d)) (v * d / 2 / c) =
      d * min (v ^ 2 / (4 * (c : ℝ) ^ 2)) (v / (2 * (c : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hd]
    congr 1
    · by_cases hd₀ : d = 0
      · simp [hd₀]
      by_cases hc₀ : (c : ℝ) = 0
      · simp [hc₀]
      field_simp
      norm_num
    · ring
  exact (measureReal_mono hsubsets (measure_ne_top _ _)).trans
    (htail.trans_eq (by rw [hrate]; congr 2; ring))

/-- Independent sub-Gaussian entries with second moments at least `v` give an exponential
lower tail for the Euclidean image norm in any fixed unit direction. The coordinate laws
may vary by entry. -/
theorem measureReal_norm_toEuclideanLin_lt_le [DecidableEq n]
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) c P)
    {v : ℝ} (hvar : ∀ i j, v ≤ ∫ ω, (A ω i j) ^ 2 ∂P)
    {x : EuclideanSpace ℝ n} (hx : ‖x‖ = 1) :
    P.real {ω | ‖toEuclideanLin (A ω) x‖ < Real.sqrt (v * Fintype.card m) / 2} ≤
      2 * Real.exp (-(1 / 1536) *
        min (v ^ 2 / (4 * (c : ℝ) ^ 2)) (v / (2 * (c : ℝ))) * Fintype.card m) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hxi : ∑ j, x j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hx, one_pow]
  have hrows := hind.matrix_row (fun i j ↦ (hA i j).aemeasurable)
  have hrow (i : m) : iIndepFun (fun j ω ↦ A ω i j) P :=
    hind.precomp (g := fun j : n ↦ (i, j)) (fun _ _ h ↦ congrArg Prod.snd h)
  refine hrows.measureReal_norm_toEuclideanLin_lt_le_of_rows x ?_ ?_
  · intro i
    have hproxy : ∑ j, ‖x j‖₊ ^ 2 * c = c := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow, coe_nnNorm,
        Real.norm_eq_abs, sq_abs, ← sum_mul, hxi, one_mul]
    simpa only [hproxy] using (hrow i).hasSubgaussianMGF_dotProduct (hA i) x
  · calc
      _ = ∑ _i : m, v := by simp [nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun i _ ↦ by
        simp only [dotProduct, mul_comm (A _ _ _) (x _)]
        rw [TauCeti.integral_sq_sum_mul_of_pairwise_indepFun
          (fun j ↦ (hA i j).memLp 2) (fun j ↦ (hA i j).integral_eq_zero)
          (fun _ _ hij ↦ (hrow i).indepFun hij)]
        calc
          v = ∑ j, x j ^ 2 * v := by rw [← sum_mul, hxi, one_mul]
          _ ≤ _ := sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hvar i j) (sq_nonneg _)

end ProbabilityTheory.iIndepFun
