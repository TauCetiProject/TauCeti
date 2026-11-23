/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
public import TauCeti.Analysis.MellinTransform.UpperTail
import Mathlib.MeasureTheory.Function.Floor

/-!
# Upper Mellin tails of the sawtooth

Write `B₁({x}) = {x} - 1/2` for the sawtooth, the periodic Bernoulli function
`bernoulliFun 1 (Int.fract x)`. Since `|B₁({x})| ≤ 1/2`, its tail integral against `x^(-s-1)` over
`(a, ∞)`, `a > 0`, converges absolutely for `0 < Re s`, with
`‖∫_a^∞ B₁({x}) x^(-s-1) dx‖ ≤ a^(-σ)/(2σ)`, `σ = Re s`. Writing `{x} = B₁({x}) + 1/2` relates
it to the tail integral of the fractional part. These tails are the remainders of the
first-order Euler–Maclaurin formula for `x ↦ x^(-s)`, as in the continuation of the Riemann zeta
function.

## Main results

* `TauCeti.isBigO_sawtooth`: the sawtooth viewed in `ℂ` is `O(x ^ 0)` at infinity.
* `TauCeti.integrableOn_sawtooth_mul_cpow`: the tail integral converges absolutely.
* `TauCeti.norm_integral_sawtooth_mul_cpow_le`: its bound `a^(-σ)/(2σ)`.
* `TauCeti.integral_fract_mul_cpow_eq_integral_sawtooth_add`:
  `∫_a^∞ {x} x^(-s-1) dx = ∫_a^∞ B₁({x}) x^(-s-1) dx + a^(-s)/(2s)`.
-/

public section

open Complex MeasureTheory

namespace TauCeti

/-- The sawtooth viewed in `ℂ` is `O(x ^ 0)` at infinity, the form of growth hypothesis taken by
`TauCeti.differentiableOn_integral_mul_cpow_of_isBigO`; see `TauCeti.isBigO_bernoulliFun_one_fract`
for the real sawtooth. -/
theorem isBigO_sawtooth :
    (fun x : ℝ ↦ (bernoulliFun 1 (Int.fract x) : ℂ)) =O[Filter.atTop] fun x : ℝ ↦ x ^ (0 : ℝ) :=
  (isBigO_ofReal_left.mpr (isBigO_bernoulliFun_one_fract Filter.atTop)).congr_right fun x ↦
    (Real.rpow_zero x).symm

/-- The tail integral of the sawtooth `B₁({x}) = {x} - 1/2` against `x^(-s-1)` converges
absolutely on `(a, ∞)` for `a > 0` and `0 < Re s`. -/
theorem integrableOn_sawtooth_mul_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi a) :=
  integrableOn_mul_cpow_of_bound ha
    ((continuous_ofReal.comp (continuous_bernoulliFun 1)).measurable.comp
      measurable_fract).aestronglyMeasurable (fun x _ ↦ norm_bernoulliFun_one_fract_le x) hs

/-- **The bound for the sawtooth tail.** For `a > 0` and `σ = Re s > 0`,
`‖∫_a^∞ B₁({x}) x^(-s-1) dx‖ ≤ a^(-σ)/(2σ)`, where `B₁({x}) = {x} - 1/2`. -/
theorem norm_integral_sawtooth_mul_cpow_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      a ^ (-s.re) / (2 * s.re) :=
  (norm_integral_mul_cpow_le_of_bound ha (fun x _ ↦ norm_bernoulliFun_one_fract_le x) hs).trans_eq
    (by ring)

/-- On `(a, ∞)`, `a > 0`, writing the fractional part as `{x} = B₁({x}) + 1/2` splits its tail
integral: `∫_a^∞ {x} x^(-s-1) dx = ∫_a^∞ B₁({x}) x^(-s-1) dx + a^(-s)/(2s)` for `0 < Re s`. -/
theorem integral_fract_mul_cpow_eq_integral_sawtooth_add {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) :
    ∫ x in Set.Ioi a, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        (a : ℂ) ^ (-s) / (2 * s) := by
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hre : (-(s + 1)).re < -1 := by simpa using hs
  have hsplit : ∫ x in Set.Ioi a, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        1 / 2 * ∫ x in Set.Ioi a, (x : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul, ← integral_add (integrableOn_sawtooth_mul_cpow ha hs)
      ((integrableOn_Ioi_cpow_of_lt hre ha).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    rw [bernoulliFun_one]
    push_cast
    ring
  have hexp : -(s + 1) + 1 = -s := by ring
  rw [hsplit, integral_Ioi_cpow_of_lt hre ha, hexp]
  field_simp

end TauCeti
