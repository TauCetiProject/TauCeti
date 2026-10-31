/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Catalan
public import TauCeti.Probability.Distributions.Semicircle.LocationScale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Moments of the semicircle law

The odd moments of the semicircle law about its centre vanish, and its even moments are Catalan
numbers: for the law `semicircleReal a v` with centre `a` and variance `v`,
`∫ (x - a) ^ (2 * n) = v ^ n * catalan n`. In particular the standard law `semicircleReal 0 1`
has moments `catalan n` in degree `2 * n`. These are the limiting moments in the moment-method
proof of Wigner's semicircle law, where `catalan n` counts the noncrossing pairings of `2 * n`
points.

## Main results

* `integral_pow_add_two_semicircleMeasure`: the moment recurrence of the unit-radius law.
* `integral_pow_two_mul_semicircleMeasure`, `integral_pow_two_mul_add_one_semicircleMeasure`:
  the even and odd moments of the unit-radius law.
* `integral_sub_pow_two_mul_semicircleReal`, `centralMoment_id_two_mul_semicircleReal`: the even
  moments about the centre are `v ^ n * catalan n`.
* `integral_sub_pow_two_mul_add_one_semicircleReal`,
  `centralMoment_id_two_mul_add_one_semicircleReal`: the odd moments about the centre vanish.
* `integral_pow_two_mul_semicircleReal_zero`, `integral_pow_two_mul_add_one_semicircleReal_zero`:
  the moments of a centred semicircle law.

## Implementation notes

The computation starts from the density `2 / π * √(1 - x ^ 2)` of the unit-radius law
`semicircleMeasure`. Integrating by parts against `(1 - x ^ 2) ^ (3 / 2)` gives the recurrence
`(n + 4) Mₙ₊₂ = (n + 1) Mₙ` for its moments `Mₙ`; starting from total mass one and mean zero,
it yields `M₂ₙ₊₁ = 0` and `M₂ₙ = catalan n / 4 ^ n`, through the first-order recurrence of the
Catalan numbers. The affine realization of `semicircleReal a v` transports these formulas.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set intervalIntegral
open scoped NNReal

namespace TauCeti.Probability

/-- The moments `Jₙ = ∫ x in -1..1, x ^ n * √(1 - x ^ 2)` of the semicircle height satisfy
`(n + 4) Jₙ₊₂ = (n + 1) Jₙ`. -/
private lemma intervalIntegral_pow_add_two_mul_sqrt (n : ℕ) :
    (n + 4 : ℝ) * ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2) =
      (n + 1) * ∫ x in -1..1, x ^ n * √(1 - x ^ 2) := by
  have hu (x : ℝ) (_ : x ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun y : ℝ ↦ y ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
    simpa using hasDerivAt_pow (n + 1) x
  have hv (x : ℝ) (_ : x ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun y : ℝ ↦ (1 - y ^ 2) ^ (3 / 2 : ℝ)) (-3 * x * √(1 - x ^ 2)) x := by
    convert ((hasDerivAt_pow 2 x).const_sub 1).rpow_const (p := 3 / 2)
      (Or.inr (by norm_num)) using 1
    rw [sqrt_eq_rpow, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun x : ℝ ↦ (n + 1 : ℝ) * x ^ n).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ ↦ -3 * x * √(1 - x ^ 2)).intervalIntegrable _ _)
  have hlhs : ∫ x in -1..1, x ^ (n + 1) * (-3 * x * √(1 - x ^ 2)) =
      -3 * ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ ↦ by ring
  have hrhs : ∫ x in -1..1, (n + 1 : ℝ) * x ^ n * (1 - x ^ 2) ^ (3 / 2 : ℝ) =
      (n + 1) * ((∫ x in -1..1, x ^ n * √(1 - x ^ 2)) -
        ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2)) := by
    have hint (k : ℕ) : IntervalIntegrable (fun x : ℝ ↦ x ^ k * √(1 - x ^ 2)) volume (-1) 1 :=
      (by fun_prop : Continuous fun x : ℝ ↦ x ^ k * √(1 - x ^ 2)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub (hint n) (hint (n + 2)),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    have h0 : 0 ≤ 1 - x ^ 2 := by
      rw [uIcc_of_le (by norm_num), mem_Icc] at hx
      nlinarith [hx.1, hx.2]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add' h0 (by norm_num), rpow_one,
      ← sqrt_eq_rpow]
    ring
  -- The boundary terms vanish because `(1 - x ^ 2) ^ (3 / 2)` is zero at `x = ±1`.
  rw [hlhs, hrhs] at hibp
  norm_num at hibp
  linarith

/-- The moments `Mₙ` of the unit-radius semicircle law satisfy `(n + 4) Mₙ₊₂ = (n + 1) Mₙ`. -/
theorem integral_pow_add_two_semicircleMeasure (n : ℕ) :
    (n + 4 : ℝ) * ∫ x, x ^ (n + 2) ∂semicircleMeasure =
      (n + 1) * ∫ x, x ^ n ∂semicircleMeasure := by
  rw [integral_semicircleMeasure_eq_intervalIntegral (· ^ (n + 2)),
    integral_semicircleMeasure_eq_intervalIntegral (· ^ n)]
  linear_combination (2 / π) * intervalIntegral_pow_add_two_mul_sqrt n

/-- Every odd moment of the unit-radius semicircle law vanishes. -/
@[simp]
theorem integral_pow_two_mul_add_one_semicircleMeasure (n : ℕ) :
    ∫ x, x ^ (2 * n + 1) ∂semicircleMeasure = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := integral_pow_add_two_semicircleMeasure (2 * n + 1)
    rw [ih, mul_zero, show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring] at h
    exact (mul_eq_zero.1 h).resolve_left (by positivity)

/-- The `2n`th moment of the unit-radius semicircle law is `catalan n / 4 ^ n`. -/
@[simp]
theorem integral_pow_two_mul_semicircleMeasure (n : ℕ) :
    ∫ x, x ^ (2 * n) ∂semicircleMeasure = catalan n / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := integral_pow_add_two_semicircleMeasure (2 * n)
    rw [ih, show 2 * n + 2 = 2 * (n + 1) by ring] at h
    have hcat : ((n + 2 : ℕ) : ℝ) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
      exact_mod_cast Nat.add_two_mul_catalan_succ n
    have hpos : (0 : ℝ) < 2 * n + 4 := by positivity
    apply mul_left_cancel₀ hpos.ne'
    push_cast at h hcat ⊢
    rw [h, pow_succ]
    field_simp
    linear_combination (-2 : ℝ) * hcat

/-- The `k`th moment of `semicircleReal a v` about its centre is `(2 √v) ^ k` times the `k`th
moment of the unit-radius law. -/
private lemma integral_sub_pow_semicircleReal (a : ℝ) (v : ℝ≥0) (k : ℕ) :
    ∫ x, (x - a) ^ k ∂semicircleReal a v =
      (2 * √(v : ℝ)) ^ k * ∫ x, x ^ k ∂semicircleMeasure := by
  rw [semicircleReal_def, integral_map (by fun_prop) (by fun_prop),
    ← MeasureTheory.integral_const_mul]
  congr with x
  ring

/-- The `2n`th moment of `semicircleReal a v` about its centre is `v ^ n * catalan n`. -/
@[simp]
theorem integral_sub_pow_two_mul_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, (x - a) ^ (2 * n) ∂semicircleReal a v = (v : ℝ) ^ n * catalan n := by
  rw [integral_sub_pow_semicircleReal, integral_pow_two_mul_semicircleMeasure, pow_mul, mul_pow,
    sq_sqrt v.coe_nonneg]
  field_simp
  ring

/-- Every odd moment of `semicircleReal a v` about its centre vanishes. -/
@[simp]
theorem integral_sub_pow_two_mul_add_one_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, (x - a) ^ (2 * n + 1) ∂semicircleReal a v = 0 := by
  rw [integral_sub_pow_semicircleReal, integral_pow_two_mul_add_one_semicircleMeasure, mul_zero]

/-- The `2n`th central moment of `semicircleReal a v` is `v ^ n * catalan n`. -/
@[simp]
theorem centralMoment_id_two_mul_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (semicircleReal a v) = (v : ℝ) ^ n * catalan n := by
  simpa only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_semicircleReal]
    using integral_sub_pow_two_mul_semicircleReal a v n

/-- Every odd central moment of `semicircleReal a v` vanishes. -/
@[simp]
theorem centralMoment_id_two_mul_add_one_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n + 1) (semicircleReal a v) = 0 := by
  simpa only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_semicircleReal]
    using integral_sub_pow_two_mul_add_one_semicircleReal a v n

/-- The `2n`th moment of a centred semicircle law of variance `v` is `v ^ n * catalan n`; for the
standard law `semicircleReal 0 1` it is the Catalan number `catalan n`. -/
@[simp]
theorem integral_pow_two_mul_semicircleReal_zero (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ (2 * n) ∂semicircleReal 0 v = (v : ℝ) ^ n * catalan n := by
  simpa only [sub_zero] using integral_sub_pow_two_mul_semicircleReal 0 v n

/-- Every odd moment of a centred semicircle law vanishes. -/
@[simp]
theorem integral_pow_two_mul_add_one_semicircleReal_zero (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ (2 * n + 1) ∂semicircleReal 0 v = 0 := by
  simpa only [sub_zero] using integral_sub_pow_two_mul_add_one_semicircleReal 0 v n

end TauCeti.Probability
