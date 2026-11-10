/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The defect energy of a ball centred at a zero of the spinor component

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β`, and its **defect energy** on a set
`B` is

`E_r(B) = (r / 4) ∫_B |1 - |χ|²| = (r / 4) ∫_B |1 - |α|² - |β|²|`.

Write `w₊ = max (1 - |α|²) 0`. Among Taubes's coarse a priori estimates, which hold with a
constant `C` independent of `r` and of the solution, are

* `|α|² + |β|² ≤ 1 + C / r`, of which only `|α|² ≤ 1 + C / r` is used here,
* `|β|² ≤ (C / r) w₊ + C / r²`,
* `|∇_a α|² ≤ C r w₊ + C`.

Since `w₊ ≤ 1`, the last bound gives `|∇_a α| = O(√r)`. By the gauge-invariant inequality
`|d |α|²| ≤ 2 |α| |∇_a α|` (`TauCeti.SeibergWitten.norm_fderiv_norm_sq_le_mul_norm_covariantDeriv`)
and the mean value inequality, `|α|²` therefore grows at most linearly, at rate `O(√r)`, away from
a zero of `α` (`TauCeti.SeibergWitten.norm_sq_le_mul_dist_of_eq_zero`). On the ball of radius
`ρ = c₀ / √r` about a zero, with `256 C c₀² ≤ 1`, this keeps `|α|² ≤ 1 / 4`, while `|β|² ≤ 1 / 4`
once `r ≥ 8 C`, so the defect density is at least one half there
(`TauCeti.SeibergWitten.inv_two_le_one_sub_norm_sq_sub_norm_sq_of_eq_zero`). Hence

`E_r(B_ρ) ≥ (r / 8) Vol(B_ρ)`

(`TauCeti.SeibergWitten.ofReal_mul_measure_le_setLIntegral_of_eq_zero`). For an additive Haar
measure on a space of dimension four, `Vol(B_ρ) = Vol(B₁) ρ⁴`, and the radius `ρ = c₀ / √r` gives

`E_r(B_{c₀ / √r}) ≥ c₁ / r`,  `c₁ = c₀⁴ Vol(B₁) / 8`

(`TauCeti.SeibergWitten.ofReal_div_le_setLIntegral_of_eq_zero`). This is the lower bound at the
smallest scale which Taubes's monotonicity inequality for the defect energy propagates to the
quadratic lower bound `E_r(B_σ) + A σ⁴ ≥ c′ σ²` at a zero of `α`, for all radii `c₀ / √r ≤ σ ≤ 1`
(`TauCeti.mul_sq_le_add_of_le_mul_deriv_add`). The constants `c₀` and `c₁` depend only on `C` and
on the measure of the unit ball, not on `r` or on the solution.

The statements are local: the hypotheses are only required on the ball itself. As in
`TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent`, the space `E` plays the role of a coordinate
chart, `α` is a section of the trivial line with connection form `a = i b`, and `β` takes values
in an arbitrary normed group. The measure in the integral is arbitrary; the volume of the ball is
computed only for an additive Haar measure.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_mul_dist_of_eq_zero`: `|α(y)|² ≤ 2 A G |y - x₀|` on a convex
  set containing a zero `x₀`, if `|α| ≤ A` and `|∇_a α| ≤ G` there.
* `TauCeti.SeibergWitten.inv_two_le_one_sub_norm_sq_sub_norm_sq_of_eq_zero`: under the coarse
  bounds, `1 - |α|² - |β|² ≥ 1 / 2` on the ball of radius `ρ` about a zero, when `256 C r ρ² ≤ 1`.
* `TauCeti.SeibergWitten.ofReal_mul_measure_le_setLIntegral_of_eq_zero`:
  `E_r(B_ρ) ≥ (r / 8) μ(B_ρ)`.
* `TauCeti.SeibergWitten.ofReal_mul_measure_ball_le_setLIntegral_of_eq_zero`: the Haar measure
  form `E_r(B_ρ) ≥ (r / 8) ρⁿ μ(B₁)` in dimension `n`.
* `TauCeti.SeibergWitten.ofReal_div_le_setLIntegral_of_eq_zero`: in dimension four,
  `E_r(B_{c₀ / √r}) ≥ c₁ / r`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Metric MeasureTheory Module

namespace TauCeti.SeibergWitten

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {β : E → F} {x₀ : E}

/-- **Linear growth of `|α|²` away from a zero.** Let `s` be a convex set containing a zero `x₀`
of `α`. If `|α| ≤ A` and `|∇_a α| ≤ G` on `s`, then `|α(y)|² ≤ 2 A G |y - x₀|` on `s`. -/
theorem norm_sq_le_mul_dist_of_eq_zero {s : Set E} {A G : ℝ} (hs : Convex ℝ s) (hx₀ : x₀ ∈ s)
    (hα : ∀ y ∈ s, DifferentiableAt ℝ α y) (hA : ∀ y ∈ s, ‖α y‖ ≤ A)
    (hG : ∀ y ∈ s, ‖covariantDeriv b α y‖ ≤ G) (h₀ : α x₀ = 0) {y : E} (hy : y ∈ s) :
    ‖α y‖ ^ 2 ≤ 2 * A * G * dist y x₀ := by
  have hd : ∀ z ∈ s, DifferentiableAt ℝ (fun y ↦ ‖α y‖ ^ 2) z := fun z hz ↦
    (hα z hz).hasFDerivAt.norm_sq.differentiableAt
  have hbound : ∀ z ∈ s, ‖fderiv ℝ (fun y ↦ ‖α y‖ ^ 2) z‖ ≤ 2 * A * G := by
    intro z hz
    refine (norm_fderiv_norm_sq_le_mul_norm_covariantDeriv (b := b) (hα z hz)).trans ?_
    have hA₀ : 0 ≤ A := (norm_nonneg _).trans (hA z hz)
    gcongr
    exacts [hA z hz, hG z hz]
  simpa [h₀, dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderiv_le hd hbound hx₀ hy

/-- **The spinor is small near a zero of `α`.** Suppose that, on the closed ball of radius `ρ`
about a zero `x₀` of `α`, the coarse large-parameter bounds `|α|² ≤ 1 + C / r` (a consequence of
`|α|² + |β|² ≤ 1 + C / r`), `|β|² ≤ (C / r) w₊ + C / r²` and `|∇_a α|² ≤ C r w₊ + C` hold, where
`w₊ = max (1 - |α|²) 0`. If `r ≥ 1`, `r ≥ 8 C` and `256 C r ρ² ≤ 1`, then
`1 - |α|² - |β|² ≥ 1 / 2` on that ball. -/
theorem inv_two_le_one_sub_norm_sq_sub_norm_sq_of_eq_zero {C r ρ : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hrC : 8 * C ≤ r) (hρ : 256 * C * r * ρ ^ 2 ≤ 1)
    (hα : ∀ y ∈ closedBall x₀ ρ, DifferentiableAt ℝ α y)
    (hmod : ∀ y ∈ closedBall x₀ ρ, ‖α y‖ ^ 2 ≤ 1 + C / r)
    (hβ : ∀ y ∈ closedBall x₀ ρ, ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖α y‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ closedBall x₀ ρ,
      ‖covariantDeriv b α y‖ ^ 2 ≤ C * r * max (1 - ‖α y‖ ^ 2) 0 + C)
    (h₀ : α x₀ = 0) {y : E} (hy : y ∈ closedBall x₀ ρ) :
    2⁻¹ ≤ 1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2 := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hCr : C / r ≤ 1 := (div_le_one hr₀).2 (by linarith)
  -- The vacuum defect `w₊ = max (1 - |α|²) 0` is at most one.
  have hw : ∀ z, max (1 - ‖α z‖ ^ 2) 0 ≤ 1 := fun z ↦ max_le (by nlinarith [norm_nonneg (α z)])
    zero_le_one
  have hw₀ : ∀ z, 0 ≤ max (1 - ‖α z‖ ^ 2) 0 := fun z ↦ le_max_right _ _
  -- The bounds `|α| ≤ √2` and `|∇_a α| ≤ √(2 C r)` on the ball.
  have hA : ∀ z ∈ closedBall x₀ ρ, ‖α z‖ ≤ √2 := fun z hz ↦
    Real.le_sqrt_of_sq_le (by linarith [hmod z hz])
  have hG : ∀ z ∈ closedBall x₀ ρ, ‖covariantDeriv b α z‖ ≤ √(2 * C * r) := fun z hz ↦
    Real.le_sqrt_of_sq_le (by nlinarith [hgrad z hz, hw z, hw₀ z, mul_nonneg hC hr₀.le])
  have hgrowth := norm_sq_le_mul_dist_of_eq_zero (convex_closedBall x₀ ρ)
    (mem_closedBall_self (dist_nonneg.trans hy)) hα hA hG h₀ hy
  -- On the ball, `2 √2 √(2 C r) |y - x₀| ≤ 1 / 4`, since its square is `16 C r |y - x₀|² ≤ 1 / 16`.
  have hdist : dist y x₀ ≤ ρ := hy
  have hd₀ : 0 ≤ dist y x₀ := dist_nonneg
  have hsq : (2 * √2 * √(2 * C * r) * dist y x₀) ^ 2 = 16 * (C * r) * dist y x₀ ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt zero_le_two,
      Real.sq_sqrt (by positivity)]
    ring
  have hsmall : 2 * √2 * √(2 * C * r) * dist y x₀ ≤ 1 / 4 := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
    rw [hsq]
    have : dist y x₀ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hd₀ hdist 2
    nlinarith [mul_nonneg hC hr₀.le]
  -- `|β|² ≤ C / r + C / r² ≤ 2 C / r ≤ 1 / 4`.
  have hβsmall : ‖β y‖ ^ 2 ≤ 1 / 4 := by
    have hCr' : C / r ^ 2 ≤ C / r :=
      div_le_div_of_nonneg_left hC hr₀ (by nlinarith)
    have h8 : C / r ≤ 1 / 8 := by
      rw [div_le_iff₀ hr₀]
      linarith
    have := hβ y hy
    nlinarith [hw y, mul_le_mul_of_nonneg_left (hw y) (div_nonneg hC hr₀.le)]
  linarith

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **The defect energy of a small ball about a zero.** Under the coarse large-parameter bounds
on the closed ball of radius `ρ` about a zero `x₀` of `α`, with `r ≥ 1`, `r ≥ 8 C` and
`256 C r ρ² ≤ 1`, the defect energy `E_r = (r / 4) ∫ |1 - |α|² - |β|²|` of that ball is at least
`r / 8` times its measure, for every measure `μ`. -/
theorem ofReal_mul_measure_le_setLIntegral_of_eq_zero {μ : Measure E} {C r ρ : ℝ} (hC : 0 ≤ C)
    (hr : 1 ≤ r) (hrC : 8 * C ≤ r) (hρ : 256 * C * r * ρ ^ 2 ≤ 1)
    (hα : ∀ y ∈ closedBall x₀ ρ, DifferentiableAt ℝ α y)
    (hmod : ∀ y ∈ closedBall x₀ ρ, ‖α y‖ ^ 2 ≤ 1 + C / r)
    (hβ : ∀ y ∈ closedBall x₀ ρ, ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖α y‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ closedBall x₀ ρ,
      ‖covariantDeriv b α y‖ ^ 2 ≤ C * r * max (1 - ‖α y‖ ^ 2) 0 + C)
    (h₀ : α x₀ = 0) :
    ENNReal.ofReal (r / 8) * μ (closedBall x₀ ρ) ≤
      ∫⁻ y in closedBall x₀ ρ, ENNReal.ofReal (r / 4 * |1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2|) ∂μ := by
  rw [← setLIntegral_const]
  refine setLIntegral_mono' measurableSet_closedBall fun y hy ↦ ENNReal.ofReal_le_ofReal ?_
  have := inv_two_le_one_sub_norm_sq_sub_norm_sq_of_eq_zero hC hr hrC hρ hα hmod hβ hgrad h₀ hy
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  calc r / 8 = r / 4 * 2⁻¹ := by ring
    _ ≤ r / 4 * |1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2| := by
      gcongr
      exact this.trans (le_abs_self _)

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- **The defect energy of a small ball about a zero, for a Haar measure.** For an additive Haar
measure `μ` on a space of dimension `n`, under the hypotheses of
`ofReal_mul_measure_le_setLIntegral_of_eq_zero` and `ρ ≥ 0`, the defect energy of the closed
ball of radius `ρ` about the zero is at least `(r / 8) ρⁿ μ(B₁)`, where `B₁` is the unit ball. -/
theorem ofReal_mul_measure_ball_le_setLIntegral_of_eq_zero {μ : Measure E} [μ.IsAddHaarMeasure]
    {C r ρ : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (hrC : 8 * C ≤ r) (hρ₀ : 0 ≤ ρ)
    (hρ : 256 * C * r * ρ ^ 2 ≤ 1)
    (hα : ∀ y ∈ closedBall x₀ ρ, DifferentiableAt ℝ α y)
    (hmod : ∀ y ∈ closedBall x₀ ρ, ‖α y‖ ^ 2 ≤ 1 + C / r)
    (hβ : ∀ y ∈ closedBall x₀ ρ, ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖α y‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ closedBall x₀ ρ,
      ‖covariantDeriv b α y‖ ^ 2 ≤ C * r * max (1 - ‖α y‖ ^ 2) 0 + C)
    (h₀ : α x₀ = 0) :
    ENNReal.ofReal (r / 8 * ρ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ∫⁻ y in closedBall x₀ ρ, ENNReal.ofReal (r / 4 * |1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2|) ∂μ := by
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  refine le_of_eq_of_le ?_
    (ofReal_mul_measure_le_setLIntegral_of_eq_zero (μ := μ) hC hr hrC hρ hα hmod hβ hgrad h₀)
  rw [Measure.addHaar_closedBall μ x₀ hρ₀, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]

/-- **The defect energy at the smallest scale.** Let `μ` be an additive Haar measure on a space of
dimension four, and let `c₀ ≥ 0` with `256 C c₀² ≤ 1`. Under the coarse large-parameter bounds on
the closed ball of radius `c₀ / √r` about a zero `x₀` of `α`, with `r ≥ 1` and `r ≥ 8 C`, the
defect energy of that ball satisfies

`E_r(B_{c₀ / √r}) ≥ c₁ / r`,  `c₁ = c₀⁴ μ(B₁) / 8`.

The constant `c₁` does not depend on `r` or on the fields. -/
theorem ofReal_div_le_setLIntegral_of_eq_zero {μ : Measure E} [μ.IsAddHaarMeasure]
    (hE : finrank ℝ E = 4) {C r c₀ : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (hrC : 8 * C ≤ r)
    (hc₀ : 0 ≤ c₀) (hc₀C : 256 * C * c₀ ^ 2 ≤ 1)
    (hα : ∀ y ∈ closedBall x₀ (c₀ / √r), DifferentiableAt ℝ α y)
    (hmod : ∀ y ∈ closedBall x₀ (c₀ / √r), ‖α y‖ ^ 2 ≤ 1 + C / r)
    (hβ : ∀ y ∈ closedBall x₀ (c₀ / √r),
      ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖α y‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ closedBall x₀ (c₀ / √r),
      ‖covariantDeriv b α y‖ ^ 2 ≤ C * r * max (1 - ‖α y‖ ^ 2) 0 + C)
    (h₀ : α x₀ = 0) :
    ENNReal.ofReal (c₀ ^ 4 * μ.real (ball 0 1) / 8 / r) ≤
      ∫⁻ y in closedBall x₀ (c₀ / √r),
        ENNReal.ofReal (r / 4 * |1 - ‖α y‖ ^ 2 - ‖β y‖ ^ 2|) ∂μ := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hsq : √r ^ 2 = r := Real.sq_sqrt hr₀.le
  have hsqrt : 0 < √r := Real.sqrt_pos.2 hr₀
  -- At the radius `ρ = c₀ / √r`, `256 C r ρ² = 256 C c₀²` and `(r / 8) ρ⁴ = c₀⁴ / (8 r)`.
  have hρ : 256 * C * r * (c₀ / √r) ^ 2 ≤ 1 := by
    rw [div_pow, hsq, mul_div_assoc', mul_div_right_comm, mul_div_cancel_right₀ _ hr₀.ne']
    linarith
  have hρ4 : r / 8 * (c₀ / √r) ^ 4 = c₀ ^ 4 / 8 / r := by
    rw [div_pow, show √r ^ 4 = (√r ^ 2) ^ 2 by ring, hsq]
    field_simp
  refine le_of_eq_of_le ?_ (ofReal_mul_measure_ball_le_setLIntegral_of_eq_zero (μ := μ) hC hr hrC
    (div_nonneg hc₀ hsqrt.le) hρ hα hmod hβ hgrad h₀)
  rw [hE, hρ4, ← ofReal_measureReal (measure_ball_lt_top (μ := μ)).ne,
    ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end TauCeti.SeibergWitten
