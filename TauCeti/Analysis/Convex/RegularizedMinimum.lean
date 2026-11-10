/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
import Mathlib.Algebra.Order.Module.Basic

/-!
# Smooth concave regularization of the minimum

Convolution of absolute value with an even probability bump gives a smooth convex function
that agrees with absolute value outside the transition interval. The induced binary minimum
is smooth, concave, monotone in each argument, and agrees exactly with minimum for separated
inputs. Its two partial derivatives are nonnegative and sum to one, supporting smooth gluing
with a common upper Hessian bound.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff NNReal

namespace Real

private noncomputable def absoluteValueBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩

/-- Smooth absolute value obtained from an even probability kernel of radius `δ`. -/
noncomputable def regularizedAbs (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  (absoluteValueBump δ hδ).normed volume ⋆[lsmul ℝ ℝ, volume] (fun t : ℝ ↦ |t|)

private theorem abs_lipschitz : LipschitzWith 1 (fun t : ℝ ↦ |t|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y

/-- Normalized bump convolution makes the regularized absolute value smooth. -/
theorem contDiff_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (regularizedAbs δ hδ) :=
  (absoluteValueBump δ hδ).hasCompactSupport_normed.contDiff_convolution_left _
    (absoluteValueBump δ hδ).contDiff_normed abs_lipschitz.continuous.locallyIntegrable

/-- Regularization preserves the unit Lipschitz bound of absolute value. -/
theorem lipschitzWith_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    LipschitzWith 1 (regularizedAbs δ hδ) :=
  abs_lipschitz.normed_convolution (μ := volume) (absoluteValueBump δ hδ)

private theorem integral_bump_mul_id (φ : ContDiffBump (0 : ℝ)) :
    ∫ t : ℝ, φ.normed volume t * t = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ ↦ φ.normed volume t * t) volume
  simp only [φ.normed_neg, mul_neg, integral_neg] at h
  linarith

private theorem integrable_bump_mul_id (φ : ContDiffBump (0 : ℝ)) :
    Integrable (fun t : ℝ ↦ φ.normed volume t * t) :=
  ((φ.contDiff_normed (n := 0)).continuous.mul continuous_id).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.mul_right

private theorem integrable_bump_mul_abs_sub (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    Integrable (fun t : ℝ ↦ φ.normed volume t * |x - t|) := by
  exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable
    abs_lipschitz.continuous x

/-- The even mollifier preserves symmetry under negation. -/
theorem regularizedAbs_neg (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    regularizedAbs δ hδ (-x) = regularizedAbs δ hδ x := by
  let φ := absoluteValueBump δ hδ
  change (∫ t : ℝ, φ.normed volume t * |-x - t|) =
    ∫ t : ℝ, φ.normed volume t * |x - t|
  rw [← integral_neg_eq_self (fun t : ℝ ↦ φ.normed volume t * |-x - t|) volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp only
    rw [φ.normed_neg]
    congr 1
    rw [show -x - -t = -(x - t) by ring, abs_neg]

/-- Outside the transition interval the regularization agrees exactly with absolute value. -/
theorem regularizedAbs_eq_abs (δ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : δ ≤ |x|) : regularizedAbs δ hδ x = |x| := by
  have hpos (x : ℝ) (hx : δ ≤ x) : regularizedAbs δ hδ x = x := by
    let φ := absoluteValueBump δ hδ
    change (∫ t : ℝ, φ.normed volume t * |x - t|) = x
    have heq : (fun t : ℝ ↦ φ.normed volume t * |x - t|) =
        fun t : ℝ ↦ φ.normed volume t * x - φ.normed volume t * t := by
      funext t
      by_cases ht : φ.normed volume t = 0
      · simp [ht]
      · have ht' : |t| < δ := by
          have hmem : t ∈ Function.support (φ.normed volume) := ht
          rw [φ.support_normed_eq] at hmem
          simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, φ, absoluteValueBump] using hmem
        rw [abs_of_nonneg (by linarith [le_abs_self t])]
        ring
    rw [heq, integral_sub (φ.integrable_normed.mul_const _) (integrable_bump_mul_id φ),
      integral_mul_const, φ.integral_normed, integral_bump_mul_id, one_mul, sub_zero]
  rcases le_total 0 x with hx0 | hx0
  · simpa only [abs_of_nonneg hx0] using hpos x (by simpa [abs_of_nonneg hx0] using hx)
  · rw [← regularizedAbs_neg δ hδ x, hpos (-x) (by simpa [abs_of_nonpos hx0] using hx),
      abs_of_nonpos hx0]

/-- Convexity places the regularized absolute value above absolute value. -/
theorem abs_le_regularizedAbs (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    |x| ≤ regularizedAbs δ hδ x := by
  let φ := absoluteValueBump δ hδ
  have heq : (∫ t : ℝ, φ.normed volume t * (x - t)) = x := by
    simp_rw [mul_sub]
    rw [integral_sub (φ.integrable_normed.mul_const _) (integrable_bump_mul_id φ),
      integral_mul_const, φ.integral_normed, integral_bump_mul_id, one_mul, sub_zero]
  calc
    |x| = |∫ t : ℝ, φ.normed volume t * (x - t)| := congrArg abs heq.symm
    _ ≤
        ∫ t : ℝ, |φ.normed volume t * (x - t)| := abs_integral_le_integral_abs
    _ = regularizedAbs δ hδ x := by
      simp only [abs_mul, abs_of_nonneg (φ.nonneg_normed _)]
      rfl

/-- The value error of regularized absolute value is at most the smoothing radius. -/
theorem regularizedAbs_le_abs_add (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    regularizedAbs δ hδ x ≤ |x| + δ := by
  have h := (absoluteValueBump δ hδ).dist_normed_convolution_le (μ := volume)
    abs_lipschitz.continuous.aestronglyMeasurable (fun y hy ↦
      (abs_lipschitz.dist_le_mul y x).trans (by
        simpa only [NNReal.coe_one, one_mul, absoluteValueBump] using (Metric.mem_ball.mp hy).le))
  change dist (regularizedAbs δ hδ x) (abs x) ≤ δ at h
  rw [Real.dist_eq] at h
  linarith [le_abs_self (regularizedAbs δ hδ x - |x|)]

/-- Nonnegative convolution preserves convexity of absolute value. -/
theorem convexOn_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    ConvexOn ℝ univ (regularizedAbs δ hδ) := by
  let φ := absoluteValueBump δ hδ
  change ConvexOn ℝ univ (fun x ↦ ∫ t : ℝ, φ.normed volume t * |x - t|)
  apply integral_convexOn_of_integrand_ae convex_univ
  · apply Filter.Eventually.of_forall
    intro t
    have hc : ConvexOn ℝ (univ : Set ℝ) (fun x ↦ |x - t|) := by
      simpa only [Real.norm_eq_abs, preimage_univ, Function.comp_def, sub_eq_add_neg] using
        (convexOn_norm (E := ℝ) convex_univ).translate_left (-t)
    simpa only [smul_eq_mul] using hc.smul (φ.nonneg_normed t)
  · exact fun x _ ↦ integrable_bump_mul_abs_sub φ x

/-- The derivative of the smooth regularization has magnitude at most one. -/
theorem abs_deriv_regularizedAbs_le_one (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    |deriv (regularizedAbs δ hδ) x| ≤ 1 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    norm_deriv_le_of_lipschitz (x₀ := x) (lipschitzWith_regularizedAbs δ hδ)

/-- Convexity makes the ordinary second derivative nonnegative. -/
theorem deriv2_regularizedAbs_nonneg (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    0 ≤ deriv (deriv (regularizedAbs δ hδ)) x := by
  have hm := (convexOn_regularizedAbs δ hδ).monotoneOn_deriv
    (fun x _ ↦ (contDiff_regularizedAbs δ hδ).differentiable (by simp) x)
  exact (show Monotone (deriv (regularizedAbs δ hδ)) from fun x y hxy ↦
    hm (mem_univ x) (mem_univ y) hxy).deriv_nonneg

/-- Smooth minimum with transition width `δ`, lying below the actual minimum. -/
noncomputable def regularizedMin (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) : ℝ :=
  (x + y - regularizedAbs δ hδ (x - y)) / 2

/-- The binary regularized minimum is jointly smooth in its two inputs. -/
theorem contDiff_regularizedMin (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ regularizedMin δ hδ p.1 p.2) :=
  ((contDiff_fst.add contDiff_snd).sub
    ((contDiff_regularizedAbs δ hδ).comp (contDiff_fst.sub contDiff_snd))).div_const 2

/-- Interchanging the inputs leaves the regularized minimum unchanged. -/
theorem regularizedMin_comm (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    regularizedMin δ hδ x y = regularizedMin δ hδ y x := by
  unfold regularizedMin
  rw [show y - x = -(x - y) by ring, regularizedAbs_neg]
  ring

/-- A common additive constant passes through the regularized minimum. -/
theorem regularizedMin_add (δ : ℝ) (hδ : 0 < δ) (x y t : ℝ) :
    regularizedMin δ hδ (x + t) (y + t) = regularizedMin δ hδ x y + t := by
  unfold regularizedMin
  rw [show x + t - (y + t) = x - y by ring]
  ring

private theorem min_formula (x y : ℝ) : min x y = (x + y - |x - y|) / 2 := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, abs_sub_comm] using
    inf_eq_half_smul_add_sub_abs_sub' ℝ x y

/-- The regularized minimum lies below the actual binary minimum. -/
theorem regularizedMin_le_min (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    regularizedMin δ hδ x y ≤ min x y := by
  rw [min_formula]
  unfold regularizedMin
  linarith [abs_le_regularizedAbs δ hδ (x - y)]

/-- Its lower error from the binary minimum is at most half the transition width. -/
theorem min_sub_le_regularizedMin (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    min x y - δ / 2 ≤ regularizedMin δ hδ x y := by
  rw [min_formula]
  unfold regularizedMin
  linarith [regularizedAbs_le_abs_add δ hδ (x - y)]

/-- Separated inputs select the smaller input exactly. -/
theorem regularizedMin_eq_min (δ : ℝ) (hδ : 0 < δ) {x y : ℝ}
    (hxy : δ ≤ |x - y|) : regularizedMin δ hδ x y = min x y := by
  rw [regularizedMin, regularizedAbs_eq_abs δ hδ hxy, min_formula]

/-- Differentiation in the first input gives the first nonnegative selector weight. -/
theorem hasDerivAt_regularizedMin_left (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    HasDerivAt (fun t ↦ regularizedMin δ hδ t y)
      ((1 - deriv (regularizedAbs δ hδ) (x - y)) / 2) x := by
  have ha := ((contDiff_regularizedAbs δ hδ).differentiable (by simp) (x - y)).hasDerivAt
  simpa +instances only [regularizedMin, Function.comp_def, Pi.sub_apply, id_eq, mul_one] using
    (((hasDerivAt_id x).add_const y).sub
      (ha.comp x ((hasDerivAt_id x).sub_const y))).div_const 2

/-- Differentiation in the second input gives the second nonnegative selector weight. -/
theorem hasDerivAt_regularizedMin_right (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    HasDerivAt (regularizedMin δ hδ x)
      ((1 + deriv (regularizedAbs δ hδ) (x - y)) / 2) y := by
  have ha := ((contDiff_regularizedAbs δ hδ).differentiable (by simp) (x - y)).hasDerivAt
  change HasDerivAt (fun t ↦ (x + t - regularizedAbs δ hδ (x - t)) / 2) _ y
  simpa +instances only [regularizedMin, Function.comp_def, Pi.sub_apply, id_eq,
    mul_neg, mul_one, sub_neg_eq_add] using
    (((hasDerivAt_id y).const_add x).sub
      (ha.comp y ((hasDerivAt_id y).const_sub x))).div_const 2

/-- The two partial derivatives are nonnegative and sum to one. -/
theorem regularizedMin_partial_derivatives (δ : ℝ) (hδ : 0 < δ) (x y : ℝ) :
    0 ≤ deriv (fun t ↦ regularizedMin δ hδ t y) x ∧
    0 ≤ deriv (regularizedMin δ hδ x) y ∧
    deriv (fun t ↦ regularizedMin δ hδ t y) x +
      deriv (regularizedMin δ hδ x) y = 1 := by
  rw [(hasDerivAt_regularizedMin_left δ hδ x y).deriv,
    (hasDerivAt_regularizedMin_right δ hδ x y).deriv]
  have h := abs_le.mp (abs_deriv_regularizedAbs_le_one δ hδ (x - y))
  exact ⟨by linarith, by linarith, by ring⟩

/-- The regularized minimum is monotone in its first input. -/
theorem monotone_regularizedMin_left (δ : ℝ) (hδ : 0 < δ) (y : ℝ) :
    Monotone (fun x ↦ regularizedMin δ hδ x y) :=
  monotone_of_deriv_nonneg
    (fun x ↦ (hasDerivAt_regularizedMin_left δ hδ x y).differentiableAt)
    (fun x ↦ (regularizedMin_partial_derivatives δ hδ x y).1)

/-- The regularized minimum is monotone in its second input. -/
theorem monotone_regularizedMin_right (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    Monotone (regularizedMin δ hδ x) :=
  monotone_of_deriv_nonneg
    (fun y ↦ (hasDerivAt_regularizedMin_right δ hδ x y).differentiableAt)
    (fun y ↦ (regularizedMin_partial_derivatives δ hδ x y).2.1)

/-- Convexity of regularized absolute value makes the binary minimum concave. -/
theorem concaveOn_regularizedMin (δ : ℝ) (hδ : 0 < δ) :
    ConcaveOn ℝ univ (fun p : ℝ × ℝ ↦ regularizedMin δ hδ p.1 p.2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (convexOn_regularizedAbs δ hδ).2
    (mem_univ (x.1 - x.2)) (mem_univ (y.1 - y.2)) ha hb hab
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul, regularizedMin] at h ⊢
  rw [show a * x.1 + b * y.1 - (a * x.2 + b * y.2) =
    a * (x.1 - x.2) + b * (y.1 - y.2) by ring]
  nlinarith

end Real
