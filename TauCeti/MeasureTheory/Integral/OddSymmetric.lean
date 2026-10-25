/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Integrals of odd functions over symmetric domains

An odd integrand into a real normed space integrates to zero over an interval `[-R, R]`
symmetric about the origin, and more generally against any measure invariant under negation.
In particular a law invariant under negation has mean zero.

No integrability hypothesis is needed. The substitution `t ↦ -t` carries `[-R, R]` to itself, so
`intervalIntegral.integral_comp_neg` identifies the integral with the integral of `t ↦ g (-t)`;
oddness turns that into the negative of the original, and in a real vector space an element equal
to its own negative is zero. In particular the statement is also true (vacuously, both sides being
`0`) when `g` fails to be integrable.

## Main results

* `intervalIntegral.integral_eq_zero_of_odd` — `∫ t in -R..R, g t = 0` for odd `g`.
* `MeasureTheory.integral_eq_zero_of_odd` — `∫ x, g x ∂μ = 0` for odd `g` and a measure `μ`
  invariant under negation.
-/

public section

namespace intervalIntegral

/-- **An odd integrand integrates to zero over a symmetric interval.** No integrability
hypothesis is needed: the substitution `t ↦ -t` maps `[-R, R]` to itself, so the integral equals
its own negative. -/
@[simp]
theorem integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hodd : Function.Odd g) (R : ℝ) :
    ∫ t in (-R)..R, g t = 0 := by
  have hfun : (fun t => g (-t)) = fun t => -g t := funext hodd
  have hcomp : ∫ t in (-R)..R, g (-t) = ∫ t in (-R)..R, g t := by
    simp [intervalIntegral.integral_comp_neg (a := -R) (b := R) g]
  rw [hfun, intervalIntegral.integral_neg] at hcomp
  -- `hcomp` says the integral is its own negative; in a real vector space that forces `0`.
  have htwo : (2 : ℝ) • (∫ t in (-R)..R, g t) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hcomp]
    abel
  simpa using htwo

end intervalIntegral

namespace MeasureTheory

/-- **An odd integrand integrates to zero against a measure invariant under negation.** No
integrability hypothesis is needed: the substitution `x ↦ -x` preserves the measure, so the
integral equals its own negative. -/
theorem integral_eq_zero_of_odd {G E : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableNeg G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure G} [μ.IsNegInvariant] {g : G → E}
    (hodd : Function.Odd g) : ∫ x, g x ∂μ = 0 := by
  have hfun : (fun x ↦ g (-x)) = fun x ↦ -g x := funext hodd
  have h := integral_neg_eq_self g μ
  rw [hfun, integral_neg] at h
  rw [neg_eq_iff_add_eq_zero, ← two_smul ℝ] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

end MeasureTheory

end
