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
import TauCeti.Data.Nat.Factorial.Basic

/-!
# The addition formula and the monotonicity of the hyperbolic tangent, and bounds on `sinh`

Mathlib's `Analysis/Complex/Trigonometric.lean` defines `Real.sinh`, `Real.cosh` and `Real.tanh`
and proves the two addition formulae `Real.sinh_add` and `Real.cosh_add`, but records none for
`Real.tanh`; `Analysis/SpecialFunctions/Artanh.lean` inverts `Real.tanh` on `(-1, 1)` and proves
that the inverse is strictly monotone, but does not state the monotonicity of `Real.tanh`
itself, nor its continuity or smoothness. This file supplies these, together with the square of
`Real.sinh (r / 2)` in terms of the exponentials `exp (± r / 2)`, and the Gaussian bound
`sinh x ≤ x * exp (x ^ 2 / 6)` for `0 ≤ x`, the odd companion of Mathlib's
`Real.cosh_le_exp_half_sq`, with the bound it gives on `(1 - exp (-l)) / l`.

## Main declarations

* `Real.tanh_add` — `tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b)`: the hyperbolic
  tangent of a sum is the Möbius sum of the hyperbolic tangents.
* `Real.tanh_strictMono` and `Real.tanh_lt_tanh_iff` — `Real.tanh` is strictly monotone, so it
  compares two real numbers exactly as they compare, and is positive on the positive reals.
* `Real.tanh_nonneg`, `Real.tanh_neg_iff`, `Real.continuous_tanh` and `Real.contDiff_tanh` —
  `Real.tanh` is nonnegative on `[0, ∞)`, negative exactly on `(-∞, 0)`, continuous and smooth.
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
that law is in turn what makes the hyperbolic distance of the complex unit disc a metric, the
subject of layer L2 of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`).
-/

public section

namespace TauCeti

/-- **Addition formula for the hyperbolic tangent.** `Real.tanh (a + b)` is the Möbius sum
`(tanh a + tanh b) / (1 + tanh a * tanh b)`.

The pinned Mathlib has `Real.sinh_add` and `Real.cosh_add` but no addition formula for
`Real.tanh`. This one is their quotient, both sides of which carry the same factor: by those two
formulae `tanh a + tanh b = sinh (a + b) / (cosh a * cosh b)` and
`1 + tanh a * tanh b = cosh (a + b) / (cosh a * cosh b)`, and the right-hand denominator is
positive, so dividing cancels `cosh a * cosh b` and leaves `tanh (a + b)`. -/
theorem _root_.Real.tanh_add (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) := by
  have ha : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  have hb : Real.cosh b ≠ 0 := (Real.cosh_pos b).ne'
  have hc : Real.cosh (a + b) ≠ 0 := (Real.cosh_pos _).ne'
  have hnum : Real.tanh a + Real.tanh b
      = Real.sinh (a + b) / (Real.cosh a * Real.cosh b) := by
    rw [Real.sinh_add, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hden : 1 + Real.tanh a * Real.tanh b
      = Real.cosh (a + b) / (Real.cosh a * Real.cosh b) := by
    rw [Real.cosh_add, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hne : 1 + Real.tanh a * Real.tanh b ≠ 0 := by
    rw [hden]
    exact div_ne_zero hc (mul_ne_zero ha hb)
  rw [eq_div_iff hne, hnum, hden, Real.tanh_eq_sinh_div_cosh (a + b)]
  field_simp

/-- **The hyperbolic tangent is strictly monotone.** It is inverted on its range `(-1, 1)` by
the strictly monotone `Real.artanh`, so it cannot reverse a strict inequality. -/
theorem _root_.Real.tanh_strictMono : StrictMono Real.tanh := by
  intro a b hab
  have ha : Real.tanh a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
  have hb : Real.tanh b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩
  by_contra h
  rw [not_lt] at h
  have hba := (Real.artanh_le_artanh_iff hb ha).mpr h
  rw [Real.artanh_tanh, Real.artanh_tanh] at hba
  exact absurd hab (not_lt.mpr hba)

/-- The hyperbolic tangent compares two real numbers exactly as they compare. -/
@[simp]
theorem _root_.Real.tanh_lt_tanh_iff {a b : ℝ} : Real.tanh a < Real.tanh b ↔ a < b :=
  Real.tanh_strictMono.lt_iff_lt

/-- The hyperbolic tangent is nonnegative on the nonnegative reals. -/
theorem _root_.Real.tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using Real.tanh_strictMono.monotone hx

/-- The hyperbolic tangent is negative exactly on the negative reals. -/
@[simp]
theorem _root_.Real.tanh_neg_iff {x : ℝ} : Real.tanh x < 0 ↔ x < 0 := by
  simpa only [Real.tanh_zero] using @Real.tanh_lt_tanh_iff x 0

/-- The hyperbolic tangent is continuous: it is the quotient of `exp x - exp (-x)` by the
positive function `exp x + exp (-x)`. -/
@[continuity, fun_prop]
theorem _root_.Real.continuous_tanh : Continuous Real.tanh := by
  simp_rw [funext Real.tanh_eq]
  exact (by fun_prop : Continuous fun x ↦ Real.exp x - Real.exp (-x)).div (by fun_prop)
    fun x ↦ (add_pos (Real.exp_pos x) (Real.exp_pos (-x))).ne'

/-- The hyperbolic tangent is smooth: it is the quotient of `sinh` by the positive function
`cosh`. -/
@[fun_prop]
theorem _root_.Real.contDiff_tanh {n : WithTop ℕ∞} : ContDiff ℝ n Real.tanh := by
  simp_rw [funext Real.tanh_eq_sinh_div_cosh]
  exact Real.contDiff_sinh.div Real.contDiff_cosh fun x ↦ (Real.cosh_pos x).ne'

/-- The square of `sinh (r / 2)` in terms of `exp (± r / 2)`:
`4 * sinh (r / 2) ^ 2 = (exp (r / 2) - exp (-(r / 2))) ^ 2`. -/
theorem _root_.Real.four_mul_sinh_half_sq (r : ℝ) :
    4 * Real.sinh (r / 2) ^ 2 = (Real.exp (r / 2) - Real.exp (-(r / 2))) ^ 2 := by
  rw [Real.sinh_eq]
  ring

/-- `sinh x ≤ x * exp (x ^ 2 / 6)` for `0 ≤ x`, the odd companion of `Real.cosh_le_exp_half_sq`.
The constant `6` is sharp: the cubic terms of the two power series agree. -/
theorem _root_.Real.sinh_le_mul_exp_sq_div_six {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  -- Compare the power series `∑ x ^ (2 k + 1) / (2 k + 1)!` and
  -- `∑ x ^ (2 k + 1) / (6 ^ k * k !)` termwise, using
  -- `Nat.six_pow_mul_factorial_le_factorial_two_mul_add_one`.
  rw [Real.sinh_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ, ← tsum_mul_left]
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
theorem _root_.Real.one_sub_exp_neg_div_le_exp (l : ℝ) :
    (1 - Real.exp (-l)) / l ≤ Real.exp (-(l / 2) + l ^ 2 / 24) := by
  -- Write the left side as `exp (-(l / 2)) * (2 * sinh (l / 2) / l)`. The factor
  -- `2 * sinh (l / 2) / l` is even in `l`, so `Real.sinh_le_mul_exp_sq_div_six` at `|l| / 2`
  -- bounds it by `exp (l ^ 2 / 24)`.
  have h1 : 1 - Real.exp (-l) = Real.exp (-(l / 2)) * (2 * Real.sinh (l / 2)) := by
    have ha : Real.exp (-(l / 2)) * Real.exp (l / 2) = 1 := by rw [← Real.exp_add]; simp
    have hb : Real.exp (-l) = Real.exp (-(l / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [Real.sinh_eq]
    linear_combination -ha - hb
  have hsq : (l / 2) ^ 2 / 6 = l ^ 2 / 24 := by ring
  rw [h1, Real.exp_add, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rcases lt_trichotomy l 0 with hl | rfl | hl
  · have h := Real.sinh_le_mul_exp_sq_div_six (by linarith : 0 ≤ -(l / 2))
    rw [Real.sinh_neg, neg_sq, hsq] at h
    rw [div_le_iff_of_neg hl]
    linarith
  · simp
  · have h := Real.sinh_le_mul_exp_sq_div_six (half_pos hl).le
    rw [hsq] at h
    rw [div_le_iff₀ hl]
    linarith

end TauCeti
