/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Hyperbolic tangent identities, regularity and calculus, and bounds on `sinh`

Mathlib's `Analysis/Complex/Trigonometric.lean` defines `Real.sinh`, `Real.cosh` and `Real.tanh`
and proves the two addition formulae `Real.sinh_add` and `Real.cosh_add`, but records none for
`Real.tanh`; `Analysis/SpecialFunctions/Artanh.lean` inverts `Real.tanh` on `(-1, 1)` and proves
that the inverse is strictly monotone, but does not state the monotonicity of `Real.tanh`
itself, nor its continuity, smoothness, derivative or limits at `±∞`. This file supplies these,
together with the identity `√(1 - tanh x ^ 2) = (cosh x)⁻¹`, the square of `Real.sinh (r / 2)`
in terms of the exponentials `exp (± r / 2)`, and the Gaussian bound
`sinh x ≤ x * exp (x ^ 2 / 6)` for `0 ≤ x`, the odd companion of Mathlib's
`Real.cosh_le_exp_half_sq`, with the bound it gives on `(1 - exp (-l)) / l`.

## Main declarations

* `Real.tanh_add` — `tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b)`: the hyperbolic
  tangent of a sum is the Möbius sum of the hyperbolic tangents.
* `Real.tanh_strictMono` and `Real.tanh_lt_tanh_iff` — `Real.tanh` is strictly monotone, so it
  compares two real numbers exactly as they compare, and is positive on the positive reals.
* `Real.tanh_nonneg`, `Real.tanh_neg_iff`, `Real.continuous_tanh` and `Real.contDiff_tanh` —
  `Real.tanh` is nonnegative on `[0, ∞)`, negative exactly on `(-∞, 0)`, continuous and smooth.
* `Real.sqrt_one_sub_tanh_sq` — `√(1 - tanh x ^ 2) = (cosh x)⁻¹`, the hyperbolic secant.
* `Real.hasDerivAt_tanh`, `Real.deriv_tanh` and `Real.one_sub_tanh_sq` — the derivative of
  `Real.tanh` is `1 / cosh x ^ 2 = 1 - tanh x ^ 2`.
* `Real.tendsto_tanh_atTop` and `Real.tendsto_tanh_atBot` — `Real.tanh` tends to `±1` at `±∞`.
* `Real.hasDerivAt_inv_cosh` — the derivative of `(cosh x)⁻¹` is `-tanh x * (cosh x)⁻¹`.
* `Real.one_add_tanh`, `Real.one_sub_tanh`, `Real.one_add_tanh_le` and `Real.one_sub_tanh_le` —
  `1 ± tanh x = exp (± x) / cosh x`, so `Real.tanh` approaches `∓1` at the rate `2 * exp (± 2 x)`.
* `Real.tendsto_cosh_atTop` and `Real.tendsto_cosh_atBot` — `Real.cosh` tends to infinity at both
  ends of the line.
* `Real.hasDerivAt_log_cosh` and `Real.abs_sub_log_two_le_log_cosh` — `log (cosh x)` has
  derivative `tanh x` and is at least `|x| - log 2`, so it is a smooth version of `|x|`.
* `Real.tendsto_cosh_sub_div_cosh_add_atTop` — `cosh (x - a) / cosh (x + a) → exp (-(2 * a))` as
  `x → ∞`.
* `Complex.cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two` —
  `cosh (α - θ) / (2 * cosh α * cosh θ) = (1 - tanh α * tanh θ) / 2` over `ℂ`, when
  `cosh α * cosh θ ≠ 0`.
* `Real.four_mul_sinh_half_sq` — `4 * sinh (r / 2) ^ 2 = (exp (r / 2) - exp (-(r / 2))) ^ 2`.
* `Real.sinh_le_mul_exp_sq_div_six` — `sinh x ≤ x * exp (x ^ 2 / 6)` for `0 ≤ x`. It bounds the
  exponential moment `∫₀¹ exp (-λ x) dx = 2 exp (-λ / 2) sinh (λ / 2) / λ` of the uniform
  distribution on `[0, 1]`, which is what makes the volume of a simplex cut from a cube
  exponentially small below its centre.
* `Real.one_sub_exp_neg_div_le_exp` — `(1 - exp (-l)) / l ≤ exp (-(l / 2) + l ^ 2 / 24)`: the
  resulting bound on that exponential moment, for every real `l`.

The formula `Real.tanh_add` is the quotient of the other two, both sides carrying the factor
`cosh a * cosh b`, which is nonzero because `Real.cosh` is positive.

Where it is used: `TauCeti/Analysis/SpecialFunctions/Artanh.lean` inverts it into the additive
law of `Real.artanh`, which carries the Möbius addition of `(-1, 1)` to the addition of `ℝ`;
that law is in turn what makes the hyperbolic distance of the complex unit disc a metric.
The complex identity `Complex.cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two` rewrites the
projection parameter at which the two stabilization constants of the Ocneanu trace agree, in
`TauCeti/Algebra/TypeAHeckeAlgebra/Hyperbolic.lean`.
-/

public section

namespace Real

/-- **Addition formula for the hyperbolic tangent.** `Real.tanh (a + b)` is the Möbius sum
`(tanh a + tanh b) / (1 + tanh a * tanh b)`.

The pinned Mathlib has `Real.sinh_add` and `Real.cosh_add` but no addition formula for
`Real.tanh`. This one is their quotient, both sides of which carry the same factor: by those two
formulae `tanh a + tanh b = sinh (a + b) / (cosh a * cosh b)` and
`1 + tanh a * tanh b = cosh (a + b) / (cosh a * cosh b)`, and the right-hand denominator is
positive, so dividing cancels `cosh a * cosh b` and leaves `tanh (a + b)`. -/
theorem tanh_add (a b : ℝ) :
    tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b) := by
  have ha : cosh a ≠ 0 := (cosh_pos a).ne'
  have hb : cosh b ≠ 0 := (cosh_pos b).ne'
  have hc : cosh (a + b) ≠ 0 := (cosh_pos _).ne'
  have hnum : tanh a + tanh b
      = sinh (a + b) / (cosh a * cosh b) := by
    rw [sinh_add, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp
  have hden : 1 + tanh a * tanh b
      = cosh (a + b) / (cosh a * cosh b) := by
    rw [cosh_add, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp
  have hne : 1 + tanh a * tanh b ≠ 0 := by
    rw [hden]
    exact div_ne_zero hc (mul_ne_zero ha hb)
  rw [eq_div_iff hne, hnum, hden, tanh_eq_sinh_div_cosh (a + b)]
  field_simp

/-- The positive square root of `1 - tanh x ^ 2` is the hyperbolic secant. -/
@[simp]
theorem sqrt_one_sub_tanh_sq (x : ℝ) :
    √(1 - tanh x ^ 2) = (cosh x)⁻¹ := by
  simpa only [artanh_tanh, one_div, inv_inv] using
    (congrArg (fun y : ℝ ↦ y⁻¹)
      (cosh_artanh ⟨neg_one_lt_tanh x, tanh_lt_one x⟩)).symm

/-- **The hyperbolic tangent is strictly monotone.** It is inverted on its range `(-1, 1)` by
the strictly monotone `Real.artanh`, so it cannot reverse a strict inequality. -/
theorem tanh_strictMono : StrictMono tanh := by
  intro a b hab
  have ha : tanh a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_tanh a, tanh_lt_one a⟩
  have hb : tanh b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_tanh b, tanh_lt_one b⟩
  by_contra h
  rw [not_lt] at h
  have hba := (artanh_le_artanh_iff hb ha).mpr h
  rw [artanh_tanh, artanh_tanh] at hba
  exact absurd hab (not_lt.mpr hba)

/-- The hyperbolic tangent compares two real numbers exactly as they compare. -/
@[simp]
theorem tanh_lt_tanh_iff {a b : ℝ} : tanh a < tanh b ↔ a < b :=
  tanh_strictMono.lt_iff_lt

/-- The hyperbolic tangent is nonnegative on the nonnegative reals. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  simpa only [tanh_zero] using tanh_strictMono.monotone hx

/-- The hyperbolic tangent is negative exactly on the negative reals. -/
@[simp]
theorem tanh_neg_iff {x : ℝ} : tanh x < 0 ↔ x < 0 := by
  simpa only [tanh_zero] using @tanh_lt_tanh_iff x 0

/-- The hyperbolic tangent is continuous: it is the quotient of `exp x - exp (-x)` by the
positive function `exp x + exp (-x)`. -/
@[continuity, fun_prop]
theorem continuous_tanh : Continuous tanh := by
  simp_rw [funext tanh_eq]
  exact (by fun_prop : Continuous fun x ↦ exp x - exp (-x)).div (by fun_prop)
    fun x ↦ (add_pos (exp_pos x) (exp_pos (-x))).ne'

/-- The hyperbolic tangent is smooth: it is the quotient of `sinh` by the positive function
`cosh`. -/
@[fun_prop]
theorem contDiff_tanh {n : WithTop ℕ∞} : ContDiff ℝ n tanh := by
  simp_rw [funext tanh_eq_sinh_div_cosh]
  exact contDiff_sinh.div contDiff_cosh fun x ↦ (cosh_pos x).ne'

/-- `1 - tanh x ^ 2 = 1 / cosh x ^ 2`: the derivative of `Real.tanh` written through `Real.tanh`.
-/
theorem one_sub_tanh_sq (x : ℝ) : 1 - tanh x ^ 2 = 1 / cosh x ^ 2 := by
  have h := cosh_sq_sub_sinh_sq x
  have hc := (cosh_pos x).ne'
  rw [tanh_eq_sinh_div_cosh]
  field_simp
  linarith

/-- The derivative of the hyperbolic tangent is `1 / cosh x ^ 2`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h : HasDerivAt (fun y ↦ sinh y / cosh y) _ x :=
    (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  rw [← funext tanh_eq_sinh_div_cosh] at h
  convert h using 1
  rw [← sq, ← sq, cosh_sq_sub_sinh_sq]

/-- The derivative of the hyperbolic tangent is `1 / cosh x ^ 2`. -/
@[simp]
theorem deriv_tanh (x : ℝ) : deriv tanh x = 1 / cosh x ^ 2 :=
  (hasDerivAt_tanh x).deriv

/-- The derivative of `(cosh x)⁻¹` is `-tanh x * (cosh x)⁻¹`, so `(cosh x)⁻¹` solves
`v' = -tanh(x) v`. -/
theorem hasDerivAt_inv_cosh (x : ℝ) :
    HasDerivAt (fun y ↦ (cosh y)⁻¹) (-tanh x * (cosh x)⁻¹) x := by
  have hc := (cosh_pos x).ne'
  convert (hasDerivAt_cosh x).inv hc using 1
  rw [tanh_eq_sinh_div_cosh]
  field_simp

/-- The hyperbolic tangent tends to `1` at `+∞`. -/
theorem tendsto_tanh_atTop : Filter.Tendsto tanh Filter.atTop (nhds 1) := by
  -- Divide numerator and denominator of `tanh x = (exp x - exp (-x)) / (exp x + exp (-x))` by
  -- `exp x`; then `exp (-x) ^ 2` tends to zero.
  have h (x : ℝ) : tanh x = (1 - exp (-x) ^ 2) / (1 + exp (-x) ^ 2) := by
    have hx := (exp_pos x).ne'
    rw [tanh_eq, exp_neg]
    field_simp
  have hsq := tendsto_exp_neg_atTop_nhds_zero.pow 2
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub hsq).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add hsq) (by norm_num)
  rw [funext h]
  convert hlim using 2
  norm_num

/-- The hyperbolic tangent tends to `-1` at `-∞`. -/
theorem tendsto_tanh_atBot : Filter.Tendsto tanh Filter.atBot (nhds (-1)) := by
  simpa [Function.comp_def, tanh_neg] using
    (tendsto_tanh_atTop.comp Filter.tendsto_neg_atBot_atTop).neg

/-- `1 + tanh x = exp x / cosh x`, since `cosh x + sinh x = exp x`. -/
theorem one_add_tanh (x : ℝ) : 1 + tanh x = exp x / cosh x := by
  have := (cosh_pos x).ne'
  rw [tanh_eq_sinh_div_cosh, ← cosh_add_sinh]
  field_simp

/-- `1 - tanh x = exp (-x) / cosh x`, since `cosh x - sinh x = exp (-x)`. -/
theorem one_sub_tanh (x : ℝ) : 1 - tanh x = exp (-x) / cosh x := by
  have := (cosh_pos x).ne'
  rw [tanh_eq_sinh_div_cosh, ← cosh_sub_sinh]
  field_simp

/-- The hyperbolic tangent approaches `-1` exponentially fast:
`1 + tanh x ≤ 2 * exp (2 * x)`. -/
theorem one_add_tanh_le (x : ℝ) : 1 + tanh x ≤ 2 * exp (2 * x) := by
  rw [one_add_tanh, div_le_iff₀ (cosh_pos x), cosh_eq]
  have h : exp (2 * x) * exp (-x) = exp x := by rw [← exp_add]; ring_nf
  nlinarith [mul_pos (exp_pos (2 * x)) (exp_pos x)]

/-- The hyperbolic tangent approaches `1` exponentially fast:
`1 - tanh x ≤ 2 * exp (-(2 * x))`. -/
theorem one_sub_tanh_le (x : ℝ) : 1 - tanh x ≤ 2 * exp (-(2 * x)) := by
  simpa [tanh_neg, sub_eq_add_neg] using one_add_tanh_le (-x)

/-- The square of `sinh (r / 2)` in terms of `exp (± r / 2)`:
`4 * sinh (r / 2) ^ 2 = (exp (r / 2) - exp (-(r / 2))) ^ 2`. -/
theorem four_mul_sinh_half_sq (r : ℝ) :
    4 * sinh (r / 2) ^ 2 = (exp (r / 2) - exp (-(r / 2))) ^ 2 := by
  rw [sinh_eq]
  ring

/-- `sinh x ≤ x * exp (x ^ 2 / 6)` for `0 ≤ x`, the odd companion of `Real.cosh_le_exp_half_sq`.
The constant `6` is sharp: the cubic terms of the two power series agree. -/
theorem sinh_le_mul_exp_sq_div_six {x : ℝ} (hx : 0 ≤ x) :
    sinh x ≤ x * exp (x ^ 2 / 6) := by
  -- Compare the power series `∑ x ^ (2 k + 1) / (2 k + 1)!` and
  -- `∑ x ^ (2 k + 1) / (6 ^ k * k !)` termwise, using
  -- `Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one`.
  rw [sinh_eq_tsum, exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ, ← tsum_mul_left]
  refine x.hasSum_sinh.summable.tsum_le_tsum (fun k ↦ ?_)
    ((NormedSpace.expSeries_summable' (x ^ 2 / 6)).mul_left x)
  have h : x * ((k.factorial : ℝ)⁻¹ • (x ^ 2 / 6) ^ k) =
      x ^ (2 * k + 1) / ((6 ^ k * k.factorial : ℕ) : ℝ) := by
    push_cast
    rw [smul_eq_mul, div_pow, ← pow_mul, pow_succ]
    field_simp
  rw [h]
  gcongr
  exact Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one k

/-- `(1 - exp (-l)) / l ≤ exp (-(l / 2) + l ^ 2 / 24)` for every real `l`. For `l ≠ 0` the
left side is the exponential moment `∫₀¹ exp (-l x) dx`; at `l = 0` it is `0`. -/
theorem one_sub_exp_neg_div_le_exp (l : ℝ) :
    (1 - exp (-l)) / l ≤ exp (-(l / 2) + l ^ 2 / 24) := by
  -- Write the left side as `exp (-(l / 2)) * (2 * sinh (l / 2) / l)`. The factor
  -- `2 * sinh (l / 2) / l` is even in `l`, so `Real.sinh_le_mul_exp_sq_div_six` at `|l| / 2`
  -- bounds it by `exp (l ^ 2 / 24)`.
  have h1 : 1 - exp (-l) = exp (-(l / 2)) * (2 * sinh (l / 2)) := by
    have ha : exp (-(l / 2)) * exp (l / 2) = 1 := by rw [← exp_add]; simp
    have hb : exp (-l) = exp (-(l / 2)) ^ 2 := by rw [← exp_nat_mul]; ring_nf
    rw [sinh_eq]
    linear_combination -ha - hb
  have hsq : (l / 2) ^ 2 / 6 = l ^ 2 / 24 := by ring
  rw [h1, exp_add, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  rcases lt_trichotomy l 0 with hl | rfl | hl
  · have h := sinh_le_mul_exp_sq_div_six (by linarith : 0 ≤ -(l / 2))
    rw [sinh_neg, neg_sq, hsq] at h
    rw [div_le_iff_of_neg hl]
    linarith
  · simp
  · have h := sinh_le_mul_exp_sq_div_six (half_pos hl).le
    rw [hsq] at h
    rw [div_le_iff₀ hl]
    linarith

/-- The hyperbolic cosine tends to infinity at `+∞`: it is at least `exp x / 2`. -/
theorem tendsto_cosh_atTop : Filter.Tendsto cosh Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun x ↦ ?_) (tendsto_exp_atTop.atTop_div_const two_pos)
  rw [cosh_eq]
  linarith [exp_pos (-x)]

/-- The hyperbolic cosine tends to infinity at `-∞`, since it is even. -/
theorem tendsto_cosh_atBot : Filter.Tendsto cosh Filter.atBot Filter.atTop := by
  simpa [Function.comp_def] using tendsto_cosh_atTop.comp Filter.tendsto_neg_atBot_atTop

/-- The derivative of `log (cosh x)` is `tanh x`. -/
theorem _root_.Real.hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun x ↦ Real.log (Real.cosh x)) (Real.tanh x) x := by
  convert (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne' using 1
  rw [Real.tanh_eq_sinh_div_cosh]

/-- `log (cosh x)` is at least `|x| - log 2`, because `cosh x ≥ exp |x| / 2`. -/
theorem _root_.Real.abs_sub_log_two_le_log_cosh (x : ℝ) :
    |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hcosh : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_abs_le x]
  have := Real.log_le_log (by positivity) hcosh
  rwa [Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp] at this

/-- The ratio `cosh (x - a) / cosh (x + a)` tends to `exp (-(2 * a))` as `x → ∞`. -/
theorem tendsto_cosh_sub_div_cosh_add_atTop (a : ℝ) :
    Filter.Tendsto (fun x ↦ cosh (x - a) / cosh (x + a)) Filter.atTop
      (nhds (exp (-(2 * a)))) := by
  -- In terms of `t = exp (-x)`, the ratio is `(exp (-a) + exp a t²) / (exp a + exp (-a) t²)`.
  set g : ℝ → ℝ := fun t ↦
    (exp (-a) + exp a * t ^ 2) / (exp a + exp (-a) * t ^ 2)
  have hg : ContinuousAt g 0 :=
    ((continuous_const.add (continuous_const.mul (continuous_pow 2))).continuousAt).div
      ((continuous_const.add (continuous_const.mul (continuous_pow 2))).continuousAt)
      (by simp [(exp_pos a).ne'])
  have hg0 : g 0 = exp (-(2 * a)) := by
    simp only [g, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    rw [← exp_sub]
    ring_nf
  have heq : (fun x ↦ cosh (x - a) / cosh (x + a)) = g ∘ fun x ↦ exp (-x) := by
    funext x
    have := exp_pos x
    have := exp_pos a
    simp only [g, Function.comp_apply, cosh_eq, exp_neg, exp_sub, exp_add]
    field_simp
  rw [heq, ← hg0]
  exact hg.tendsto.comp tendsto_exp_neg_atTop_nhds_zero

end Real

namespace Complex

/-- `cosh (α - θ) / (2 * cosh α * cosh θ) = (1 - tanh α * tanh θ) / 2` for complex `α`, `θ`
with `cosh α ≠ 0` and `cosh θ ≠ 0`: both sides are
`(cosh α * cosh θ - sinh α * sinh θ) / (2 * cosh α * cosh θ)` by `Complex.cosh_sub`. -/
theorem cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two {α θ : ℂ}
    (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) :
    cosh (α - θ) / (2 * cosh α * cosh θ) =
      (1 - tanh α * tanh θ) / 2 := by
  rw [cosh_sub, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  field_simp

end Complex
