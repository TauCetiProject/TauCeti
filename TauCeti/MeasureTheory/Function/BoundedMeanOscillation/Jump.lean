/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.Average

/-!
# Functions with a jump do not have vanishing mean oscillation

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, and let `f : E → F`. Suppose that near a point `x₀`, `f` takes a constant value `y₀`
on one side of the hyperplane `{y | ⟪v, y - x₀⟫ = 0}` through `x₀`, `v ≠ 0`, and a constant value
`y₁` on the other side; nothing is assumed on the hyperplane itself. Then the mean oscillation of
`f` on every small ball centred at `x₀` is at least `‖y₁ - y₀‖ / 2ⁿ⁺¹`
(`TauCeti.ofReal_le_setLAverage_enorm_sub_setAverage_ball_of_jump`), so the VMO modulus of `f` is
at least this constant at every positive scale (`TauCeti.ofReal_le_vmoModulus_of_jump`), and `f`
does not have vanishing mean oscillation as soon as `y₀ ≠ y₁` (`TauCeti.not_memVMO_of_jump`). On
the real line this says that a step function `x ↦ if c < x then y₁ else y₀`, `y₀ ≠ y₁`, is not in
`VMO` (`TauCeti.not_memVMO_ite_lt`), although it is bounded and hence of bounded mean oscillation.

Since vanishing mean oscillation only depends on the almost-everywhere class of `f`
(`TauCeti.MemVMO.congr_ae`), the same holds for every function almost everywhere equal to such an
`f`.

Coefficients with a jump are the standard examples on which the `W^{1,p}` and `W^{2,p}` theories
for coefficients of vanishing mean oscillation are tested: on such a coefficient the theory makes
no claim.

## The bound

Write `B = B(x₀, r)` and let `m` be the average of `f` over `B`. The point `m` is at distance at
least `‖y₁ - y₀‖ / 2` from `y₀` or from `y₁`. The ball `B` contains the two balls of radius `r / 2`
centred at `x₀ ± (r / 2) e`, `e = v / ‖v‖`, each of measure `2⁻ⁿ μ(B)`, and each lies strictly on
one side of the hyperplane, where `f` is constant. On the corresponding half `‖f - m‖` is at least
`‖y₁ - y₀‖ / 2`.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  {f : E → F} {x₀ v : E} {y₀ y₁ : F}

/-- The ball of radius `r / 2` centred at `x₀ + (r / 2) w`, for a unit vector `w`, lies in the
ball `B(x₀, r)`, strictly on the side of the hyperplane `{⟪w, y - x₀⟫ = 0}` into which `w`
points. -/
private theorem ball_subset_ball_and_forall_inner_pos {w : E} (hw : ‖w‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    ball (x₀ + (r / 2) • w) (r / 2) ⊆ ball x₀ r ∧
      ∀ y ∈ ball (x₀ + (r / 2) • w) (r / 2), 0 < ⟪w, y - x₀⟫ := by
  have hz : ‖(r / 2) • w‖ = r / 2 := by
    rw [norm_smul, hw, mul_one, Real.norm_of_nonneg (by positivity)]
  refine ⟨ball_subset_ball' (by rw [dist_self_add_left, hz]; linarith), fun y hy => ?_⟩
  rw [mem_ball, dist_eq_norm] at hy
  have hsplit : y - x₀ = (y - (x₀ + (r / 2) • w)) + (r / 2) • w := by abel
  have hinner : ⟪w, (r / 2) • w⟫ = r / 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hw]
    ring
  have hle := abs_real_inner_le_norm w (y - (x₀ + (r / 2) • w))
  rw [hw, one_mul] at hle
  rw [hsplit, inner_add_right, hinner]
  linarith [neg_abs_le ⟪w, y - (x₀ + (r / 2) • w)⟫]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- One half of the bound: if `f = y'` on the side of the hyperplane into which the unit vector
`w` points, and `y'` is at distance at least `‖y₁ - y₀‖ / 2` from the average `m` of `f` over
`B(x₀, r)`, then the mean oscillation of `f` on `B(x₀, r)` is at least `‖y₁ - y₀‖ / 2ⁿ⁺¹`. -/
private theorem ofReal_le_setLAverage_enorm_sub_of_side {w : E} (hw : ‖w‖ = 1) {r : ℝ}
    (hr : 0 < r) {y' : F} (hside : ∀ y ∈ ball x₀ r, 0 < ⟪w, y - x₀⟫ → f y = y')
    {m : F} (hfar : ‖y₁ - y₀‖ / 2 ≤ ‖y' - m‖) :
    ENNReal.ofReal (‖y₁ - y₀‖ / 2 ^ (finrank ℝ E + 1)) ≤
      ⨍⁻ y in ball x₀ r, ‖f y - m‖ₑ ∂μ := by
  obtain ⟨hsub, hpos⟩ := ball_subset_ball_and_forall_inner_pos (x₀ := x₀) hw hr
  have hlow := mul_ofReal_div_pow_le_setLAverage_ball (μ := μ) (g := fun y => ‖f y - m‖ₑ)
    (δ := ENNReal.ofReal (‖y₁ - y₀‖ / 2)) (by positivity : 0 < r / 2) hsub fun y hy => by
      rw [hside y (hsub hy) (hpos y hy), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hfar
  refine le_of_eq_of_le ?_ hlow
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [show r / 2 / r = 2⁻¹ by field_simp, inv_pow, pow_succ]
  field_simp

variable [NormedSpace ℝ F]

/-- **The mean oscillation across a jump.** Let `v ≠ 0` and `r > 0`, and let `f = y₀` at the points
`y` of the ball `B(x₀, r)` with `⟪v, y - x₀⟫ < 0`, and `f = y₁` at those with `⟪v, y - x₀⟫ > 0`.
Then the mean oscillation of `f` on `B(x₀, r)` is at least `‖y₁ - y₀‖ / 2ⁿ⁺¹`, with `n` the
dimension of `E`. -/
theorem ofReal_le_setLAverage_enorm_sub_setAverage_ball_of_jump (hv : v ≠ 0) {r : ℝ}
    (hr : 0 < r) (h₀ : ∀ y ∈ ball x₀ r, ⟪v, y - x₀⟫ < 0 → f y = y₀)
    (h₁ : ∀ y ∈ ball x₀ r, 0 < ⟪v, y - x₀⟫ → f y = y₁) :
    ENNReal.ofReal (‖y₁ - y₀‖ / 2 ^ (finrank ℝ E + 1)) ≤
      ⨍⁻ y in ball x₀ r, ‖f y - ⨍ z in ball x₀ r, f z ∂μ‖ₑ ∂μ := by
  set m := ⨍ z in ball x₀ r, f z ∂μ
  -- The unit normal `e = v / ‖v‖` has the sign of `v` against every vector.
  set e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm hv
  have hinner (y : E) : ⟪e, y - x₀⟫ = ‖v‖⁻¹ * ⟪v, y - x₀⟫ := real_inner_smul_left _ _ _
  have hv' : 0 < ‖v‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hv)
  by_cases hm : ‖y₁ - y₀‖ / 2 ≤ ‖y₁ - m‖
  · refine ofReal_le_setLAverage_enorm_sub_of_side he hr (fun y hy hpos => h₁ y hy ?_) hm
    rw [hinner] at hpos
    exact pos_of_mul_pos_right hpos hv'.le
  · refine ofReal_le_setLAverage_enorm_sub_of_side (w := -e) (by rw [norm_neg, he]) hr
      (fun y hy hpos => h₀ y hy ?_) ?_
    · rw [inner_neg_left, hinner, neg_pos] at hpos
      exact neg_of_mul_neg_right hpos hv'.le
    · -- `m` is far from `y₀`, since it is close to `y₁`.
      have htri : ‖y₁ - y₀‖ ≤ ‖y₁ - m‖ + ‖y₀ - m‖ := by
        simpa [norm_sub_rev m y₀] using norm_sub_le_norm_sub_add_norm_sub y₁ m y₀
      linarith

/-- **The VMO modulus across a jump.** Let `v ≠ 0` and `δ > 0`, and let `f = y₀` at the points `y`
of the ball `B(x₀, δ)` with `⟪v, y - x₀⟫ < 0`, and `f = y₁` at those with `⟪v, y - x₀⟫ > 0`. Then
at every scale `r > 0` the VMO modulus of `f` is at least `‖y₁ - y₀‖ / 2ⁿ⁺¹`, with `n` the
dimension of `E`. -/
theorem ofReal_le_vmoModulus_of_jump (hv : v ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h₀ : ∀ y ∈ ball x₀ δ, ⟪v, y - x₀⟫ < 0 → f y = y₀)
    (h₁ : ∀ y ∈ ball x₀ δ, 0 < ⟪v, y - x₀⟫ → f y = y₁) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (‖y₁ - y₀‖ / 2 ^ (finrank ℝ E + 1)) ≤ vmoModulus f μ r := by
  have hsub : ball x₀ (min r δ) ⊆ ball x₀ δ := ball_subset_ball (min_le_right r δ)
  exact (ofReal_le_setLAverage_enorm_sub_setAverage_ball_of_jump hv (lt_min hr hδ)
    (fun y hy => h₀ y (hsub hy)) (fun y hy => h₁ y (hsub hy))).trans
    (setLAverage_enorm_sub_setAverage_le_vmoModulus f μ x₀ (min_le_left r δ))

/-- **A function with a jump does not have vanishing mean oscillation.** Let `v ≠ 0` and
`δ > 0`, and let `f = y₀` at the points `y` of the ball `B(x₀, δ)` with `⟪v, y - x₀⟫ < 0`, and
`f = y₁` at those with `⟪v, y - x₀⟫ > 0`. If `y₀ ≠ y₁`, then `f` does not have vanishing mean
oscillation. -/
theorem not_memVMO_of_jump (hv : v ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h₀ : ∀ y ∈ ball x₀ δ, ⟪v, y - x₀⟫ < 0 → f y = y₀)
    (h₁ : ∀ y ∈ ball x₀ δ, 0 < ⟪v, y - x₀⟫ → f y = y₁) (hne : y₀ ≠ y₁) :
    ¬ MemVMO f μ := by
  intro h
  set c := ENNReal.ofReal (‖y₁ - y₀‖ / 2 ^ (finrank ℝ E + 1))
  have hc : c ≠ 0 := by
    have : 0 < ‖y₁ - y₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
    simp only [c, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  obtain ⟨r, hr, hle⟩ := (memVMO_iff.1 h).2 (c / 2) (ENNReal.half_pos hc)
  exact (ENNReal.half_lt_self hc ENNReal.ofReal_ne_top).not_ge
    ((ofReal_le_vmoModulus_of_jump (μ := μ) hv hδ h₀ h₁ hr).trans hle)

/-- **Step functions on the real line do not have vanishing mean oscillation.** For `y₀ ≠ y₁` and
an additive Haar measure `μ` on `ℝ`, such as Lebesgue measure, the step function equal to `y₀` on
`(-∞, c]` and to `y₁` on `(c, ∞)` does not have vanishing mean oscillation. -/
theorem not_memVMO_ite_lt {μ : Measure ℝ} [μ.IsAddHaarMeasure] (c : ℝ) (hne : y₀ ≠ y₁) :
    ¬ MemVMO (fun x : ℝ => if c < x then y₁ else y₀) μ := by
  refine not_memVMO_of_jump (x₀ := c) (v := 1) one_ne_zero one_pos (fun y _ hy => ?_)
    (fun y _ hy => ?_) hne
  · simp only [RCLike.inner_apply, conj_trivial, mul_one, sub_neg] at hy
    simp [not_lt.2 hy.le]
  · simp only [RCLike.inner_apply, conj_trivial, mul_one, sub_pos] at hy
    simp [hy]

end TauCeti
