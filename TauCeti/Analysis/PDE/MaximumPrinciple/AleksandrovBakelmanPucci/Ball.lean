/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
public import TauCeti.Analysis.PDE.TorsionFunction.Ball
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The equality case of the Aleksandrov–Bakelman–Pucci estimate on the unit ball

On `ℝⁿ = EuclideanSpace ℝ ι`, `n ≥ 1`, let `v` be the torsion function of the unit ball `B`, the
concave paraboloid

`v(x) = (1 - ‖x‖²) / (2n)` (`TauCeti.PDE.ballTorsionFunction`),

which solves `-Δv = 1` in `B` and vanishes on the unit sphere. It is the negative of the convex
function `u = (‖x‖² - 1) / (2n)`, with `Δu = 1`, and attains its maximum `1 / (2n)` at the
origin. Its gradient, Hessian and Laplacian are computed in
`TauCeti/Analysis/PDE/TorsionFunction/Ball.lean`. This file computes the remaining quantities in
the Aleksandrov–Bakelman–Pucci argument for `v` on the unit ball `B`, and shows that the measure
inequality at its heart is an equality here.

All declarations are in the `TauCeti.PDE` namespace.

* Since `v` is concave, every affine function tangent to it lies above it, so its upper contact
  set on any set `Ω` is all of `Ω` (`upperContactSet_ballTorsionFunction`).
* Its gradient is `∇v(x) = -x / n` (`gradient_ballTorsionFunction`), so the gradient image of the
  contact set `B` is the ball of radius `1 / n` (`image_gradient_ballTorsionFunction_ball`).
* Its Hessian operator is `-1 / n` times the identity (`hessianOperator_ballTorsionFunction`), so
  `|det D²v| = n⁻ⁿ` (`abs_det_hessianOperator_ballTorsionFunction`) and `Δv = -1`
  (`sum_fderiv_fderiv_ballTorsionFunction`, `laplacian_ballTorsionFunction`).
* Hence, for every additive Haar measure `μ`, both sides of the change-of-variables inequality
  `μ (∇v(Γ⁺)) ≤ ∫_{Γ⁺} |det D²v| dμ`
  (`addHaar_image_gradient_le_lintegral_abs_det_hessianOperator`) are `n⁻ⁿ μ(B)`
  (`addHaar_image_gradient_ballTorsionFunction_ball` and
  `setLIntegral_abs_det_hessianOperator_ballTorsionFunction_ball`): the inequality is an equality
  (`addHaar_image_gradient_upperContactSet_ballTorsionFunction_ball`), since the gradient
  `x ↦ -x / n` is injective with constant Jacobian determinant.
* The Aleksandrov–Bakelman–Pucci estimate (`le_add_mul_eLpNorm_negPart_div_det_rpow`), with
  `a = I`, `D* = 1` and `f = -1`, bounds `v` by `diam B / (n |B|^{1/n}) · |B|^{1/n} = 2 / n`
  (`ballTorsionFunction_le_two_div_card`), consistent with the true maximum `1 / (2n)`
  (`ballTorsionFunction_zero`, `ballTorsionFunction_le`). The loss of the factor `4` comes from
  the first step of the argument, which only uses that the gradient image contains the ball of
  radius `v(0) / diam B = 1 / (4n)` (`ball_subset_image_gradient_upperContactSet`), not the whole
  ball of radius `1 / n`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Lemmas 9.2 and 9.3, Theorem 9.1).
-/

public section

noncomputable section

open InnerProductSpace Laplacian Metric MeasureTheory Module Set
open scoped ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-- **The torsion function lies below each of its tangent planes**:
`v(x) = v(y) + ⟪∇v(y), x - y⟫ - ‖x - y‖² / (2n)`. -/
theorem ballTorsionFunction_eq_add_inner_sub (x y : EuclideanSpace ℝ ι) :
    ballTorsionFunction ι x = ballTorsionFunction ι y +
      ⟪∇ (ballTorsionFunction ι) y, x - y⟫_ℝ - ‖x - y‖ ^ 2 / (2 * Fintype.card ι) := by
  simp only [gradient_ballTorsionFunction, ballTorsionFunction_apply, real_inner_smul_left,
    norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm y x]
  ring

/-- **The upper contact set of the torsion function is the whole set**: since `v` is concave, the
tangent plane at every point of `Ω` lies above `v` on all of `Ω`. -/
@[simp]
theorem upperContactSet_ballTorsionFunction (Ω : Set (EuclideanSpace ℝ ι)) :
    upperContactSet (ballTorsionFunction ι) Ω = Ω := by
  refine Subset.antisymm upperContactSet_subset fun y hy =>
    mem_upperContactSet.2 ⟨hy, ∇ (ballTorsionFunction ι) y, fun x _ => ?_⟩
  rw [ballTorsionFunction_eq_add_inner_sub x y]
  have : 0 ≤ ‖x - y‖ ^ 2 / (2 * Fintype.card ι) := by positivity
  linarith

/-- **The gradient image of the unit ball** under the torsion function is the ball of radius
`1 / n`. -/
theorem image_gradient_ballTorsionFunction_ball [Nonempty ι] :
    ∇ (ballTorsionFunction ι) '' ball 0 1 = ball 0 (Fintype.card ι : ℝ)⁻¹ := by
  have hn : (Fintype.card ι : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  rw [gradient_ballTorsionFunction_eq, image_smul, smul_ball (neg_ne_zero.2 hn), smul_zero,
    norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_one]

variable (μ : Measure (EuclideanSpace ℝ ι)) [μ.IsAddHaarMeasure]

/-- The measure of the gradient image of the unit ball under the torsion function is `n⁻ⁿ μ(B)`.
In dimension `0` both sides are the measure of the single point of the space. -/
theorem addHaar_image_gradient_ballTorsionFunction_ball :
    μ (∇ (ballTorsionFunction ι) '' ball 0 1) =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹ ^ Fintype.card ι) * μ (ball 0 1) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- The space is a single point, which is the ball and its gradient image.
    have h0 (y : EuclideanSpace ℝ ι) : y = 0 := by
      ext i
      exact isEmptyElim i
    have hball : ball (0 : EuclideanSpace ℝ ι) 1 = {0} := Set.ext fun y => by simp [h0 y]
    simp [hball]
  rw [image_gradient_ballTorsionFunction_ball, Measure.addHaar_ball_of_pos μ 0 (by positivity),
    finrank_euclideanSpace]

omit [μ.IsAddHaarMeasure] in
/-- The integral of the absolute Hessian determinant of the torsion function over the unit ball
is `n⁻ⁿ μ(B)`. -/
theorem setLIntegral_abs_det_hessianOperator_ballTorsionFunction_ball :
    ∫⁻ y in ball 0 1, ENNReal.ofReal |(hessianOperator (ballTorsionFunction ι) y).det| ∂μ =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹ ^ Fintype.card ι) * μ (ball 0 1) := by
  simp_rw [abs_det_hessianOperator_ballTorsionFunction]
  exact setLIntegral_const _ _

/-- **The equality case of the Aleksandrov measure estimate.** For the torsion function on the unit
ball, the change-of-variables inequality
`μ (∇v(Γ⁺)) ≤ ∫_{Γ⁺} |det D²v| dμ`
(`TauCeti.PDE.addHaar_image_gradient_le_lintegral_abs_det_hessianOperator`) over the upper contact
set `Γ⁺` is an equality, both sides being `n⁻ⁿ μ(B)`. -/
theorem addHaar_image_gradient_upperContactSet_ballTorsionFunction_ball :
    μ (∇ (ballTorsionFunction ι) '' upperContactSet (ballTorsionFunction ι) (ball 0 1)) =
      ∫⁻ y in upperContactSet (ballTorsionFunction ι) (ball 0 1),
        ENNReal.ofReal |(hessianOperator (ballTorsionFunction ι) y).det| ∂μ := by
  rw [upperContactSet_ballTorsionFunction, addHaar_image_gradient_ballTorsionFunction_ball,
    setLIntegral_abs_det_hessianOperator_ballTorsionFunction_ball]

/-- **The Aleksandrov–Bakelman–Pucci estimate for the torsion function.** On the unit ball, with
`a = I`, `D* = 1` and `f = -1`, the estimate
`TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow` gives
`v ≤ diam B / (n |B|^{1/n}) · |B|^{1/n} = 2 / n`. The true maximum is `1 / (2n)`
(`TauCeti.PDE.ballTorsionFunction_le`). -/
theorem ballTorsionFunction_le_two_div_card {x : EuclideanSpace ℝ ι}
    (hx : x ∈ ball 0 1) : ballTorsionFunction ι x ≤ 2 / Fintype.card ι := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension `0` both sides are `0`, by the convention `t / 0 = 0`.
    simp [ballTorsionFunction_apply]
  have hB0 : volume (ball (0 : EuclideanSpace ℝ ι) 1) ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hBtop : volume (ball (0 : EuclideanSpace ℝ ι) 1) ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ ι) 1)) :=
    isFiniteMeasure_restrict.2 hBtop
  have h := le_add_mul_eLpNorm_negPart_div_det_rpow (a := fun _ => 1) (f := fun _ => -1) (m := 0)
    isBounded_ball isOpen_ball (contDiff_ballTorsionFunction (k := 0)).continuous.continuousOn
    contDiff_ballTorsionFunction.contDiffOn (fun _ _ => Matrix.PosDef.one)
    (fun y _ => by
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      exact (sum_fderiv_fderiv_ballTorsionFunction y).ge)
    (by
      rw [upperContactSet_ballTorsionFunction]
      simpa using memLp_const (1 : ℝ))
    (fun z hz =>
      (ballTorsionFunction_eq_zero_of_mem_sphere (frontier_ball_subset_sphere hz)).le) hx
  -- The right-hand side is `diam B / (n |B|^{1/n}) · |B|^{1/n} = 2 / n`.
  have hconst : (fun _ : EuclideanSpace ℝ ι => ((-1 : ℝ))⁻ / (1 : Matrix ι ι ℝ).det ^
      (Fintype.card ι : ℝ)⁻¹) = fun _ => 1 := by
    funext; simp
  have hnorm : (eLpNorm (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)) (Fintype.card ι)
      (volume.restrict (ball 0 1))).toReal =
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹ := by
    simp [eLpNorm_const, hB0, ENNReal.toReal_rpow]
  have hvol : 0 < (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos hB0 hBtop) _
  simp only [hconst, upperContactSet_ballTorsionFunction, hnorm, diam_ball_eq _ zero_le_one,
    mul_one, zero_add] at h
  rwa [div_mul_eq_mul_div, mul_div_mul_right _ _ hvol.ne'] at h

end PDE

end TauCeti
