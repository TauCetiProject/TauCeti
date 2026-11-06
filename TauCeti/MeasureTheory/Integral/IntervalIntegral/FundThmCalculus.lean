/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fundamental theorem of calculus for nonnegative derivatives

Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` evaluates `∫ x in a..b, f x` as
`F b - F a` for an antiderivative `F` that is continuous on `[a, b]`, provided `f` is interval
integrable. When `f` is nonnegative on `(a, b)` the integrability is automatic
(`intervalIntegral.integrableOn_deriv_of_nonneg`), which matters for integrands that are unbounded
at an endpoint, such as `1 / √(x - a)`. This file records the combined statement.

It also records that along a loop `f` (with `f a = f b`) the integral of `B (f x) (f' x)` for a
continuous bilinear map `B` is unchanged by subtracting a constant from `f`, because `∫ f' = 0`.

## Main declarations

* `TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg`
* `ContinuousLinearMap.intervalIntegral_apply_apply_eq_sub_const`
-/

public section

open MeasureTheory Set
open scoped Interval

namespace TauCeti

namespace intervalIntegral

/-- **FTC-2 for a nonnegative derivative.** If `F` is continuous on `[a, b]` and has derivative
`f x ≥ 0` at every `x ∈ (a, b)`, then `∫ x in a..b, f x = F b - F a`; the integrability of `f`
is a consequence rather than a hypothesis. -/
theorem integral_eq_sub_of_hasDerivAt_of_le_of_nonneg {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) : ∫ x in a..b, f x = F b - F a :=
  _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF hd hf))

end intervalIntegral

end TauCeti

namespace ContinuousLinearMap

/-- Along a loop `f` (that is, `f a = f b`) continuous on `[a, b]` with derivative `f'` in the
interior, subtracting a constant from the first argument does not change the integral of
`B (f x) (f' x)`, since `∫ f' = f b - f a = 0`. -/
theorem intervalIntegral_apply_apply_eq_sub_const {V G : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (B : V →L[ℝ] V →L[ℝ] G) {a b : ℝ} {f f' : ℝ → V}
    (hfc : ContinuousOn f [[a, b]])
    (hf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf'ii : IntervalIntegrable f' volume a b) (m : V)
    (hint : IntervalIntegrable (fun x => B (f x - m) (f' x)) volume a b) :
    ∫ x in a..b, B (f x) (f' x) = ∫ x in a..b, B (f x - m) (f' x) := by
  have hmean : ∫ x in a..b, B m (f' x) = 0 := by
    rw [(B m).intervalIntegral_comp_comm hf'ii,
      intervalIntegral.integral_eq_sub_of_hasDeriv_right hfc
        (fun x hx => (hf x hx).hasDerivWithinAt) hf'ii, hfab, sub_self, map_zero]
  have hBm : IntervalIntegrable (fun x => B m (f' x)) volume a b :=
    ⟨(B m).integrable_comp hf'ii.1, (B m).integrable_comp hf'ii.2⟩
  rw [← add_zero (∫ x in a..b, B (f x - m) (f' x)), ← hmean,
    ← intervalIntegral.integral_add hint hBm]
  simp [map_sub]

end ContinuousLinearMap
