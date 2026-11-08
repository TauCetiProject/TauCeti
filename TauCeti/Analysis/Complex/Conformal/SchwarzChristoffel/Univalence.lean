/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import Mathlib.Analysis.Complex.Convex
import TauCeti.Algebra.Order.BigOperators.Sum.AbsSumMulLt
import TauCeti.Analysis.Complex.Univalence
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# An exponent criterion for Schwarz--Christoffel univalence

If the total absolute turning exponent satisfies `∑ i, |e i| ≤ 1`, the
Schwarz--Christoffel primitive is injective on the upper half-plane. The exponents may have
both signs, so the criterion permits reentrant corners. It imposes no separation or simplicity
condition on the boundary, and does not require distinct or ordered prevertices.

The argument of each factor `z - a i` lies strictly between `0` and `π`. Centering these
arguments at `π / 2` shows that rotation by `exp (-π / 2 * (∑ i, e i) * I)` puts the
integrand in the open right half-plane. The strict interior bound also handles equality in the
coefficient criterion. The Noshiro--Warschawski criterion then gives global injectivity.

This is a sufficient criterion for unbounded Schwarz--Christoffel maps. It does not apply to
the classical bounded-polygon data `∑ i, e i = -2`.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Finset Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the absolute turning exponents sum to at most one, a fixed rotation places the
Schwarz--Christoffel integrand strictly in the right half-plane. -/
theorem re_exp_mul_schwarzChristoffelIntegrand_pos_of_sum_abs_le_one
    (a e : ι → ℝ) (he : ∑ i, |e i| ≤ 1) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    0 < (exp (-((Real.pi / 2 * ∑ i, e i : ℝ) : ℂ) * Complex.I) *
      schwarzChristoffelIntegrand a e z).re := by
  classical
  let θ : ℝ := Real.pi / 2 * ∑ i, e i
  let S : ℂ := ∑ i, log (z - (a i : ℂ)) * (e i : ℂ)
  have harg : ∀ i, |(z - (a i : ℂ)).arg - Real.pi / 2| < Real.pi / 2 := fun i =>
    abs_arg_sub_pi_div_two_lt_of_im_pos (by simpa using hz)
  have hangle := abs_sum_mul_lt_of_sum_abs_le_one (half_pos Real.pi_pos) e _ he harg
  -- Express the rotated product as one exponential, keeping its unwrapped argument.
  have him : (S - (θ : ℂ) * Complex.I).im =
      ∑ i, e i * ((z - (a i : ℂ)).arg - Real.pi / 2) := by
    simp [S, θ, mul_im, log_im, mul_sub, sum_sub_distrib, sum_mul, mul_comm]
  have hrot : exp (-(θ : ℂ) * Complex.I) * schwarzChristoffelIntegrand a e z =
      exp (S - (θ : ℂ) * Complex.I) := by
    have hne : ∀ i, z ≠ (a i : ℂ) := fun i h => by simp [h] at hz
    rw [schwarzChristoffelIntegrand_eq_exp_sum_log a e hne, ← exp_add]
    congr 1
    ring
  -- Its real part is positive because the centered argument lies between -π/2 and π/2.
  rw [hrot, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  rw [him]
  exact abs_lt.mp hangle

/-- **An exponent criterion for Schwarz--Christoffel univalence.** If the total absolute
turning exponent is at most one, the primitive is injective on the upper half-plane, including
when positive exponents produce reentrant corners. No hypothesis on the boundary curve is
needed. -/
theorem injOn_schwarzChristoffelPrimitive_of_sum_abs_le_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (he : ∑ i, |e i| ≤ 1) :
    InjOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet := by
  apply injOn_of_re_mul_deriv_pos (convex_halfSpace_im_gt 0)
    (exp (-((Real.pi / 2 * ∑ i, e i : ℝ) : ℂ) * Complex.I))
  intro z hz
  rw [deriv_schwarzChristoffelPrimitive a e z₀ hz]
  exact re_exp_mul_schwarzChristoffelIntegrand_pos_of_sum_abs_le_one a e he hz

end TauCeti
