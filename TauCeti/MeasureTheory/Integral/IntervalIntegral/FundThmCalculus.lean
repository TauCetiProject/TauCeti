/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The fundamental theorem of calculus for nonnegative derivatives

Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` evaluates `∫ x in a..b, f x` as
`F b - F a` for an antiderivative `F` that is continuous on `[a, b]`, provided `f` is interval
integrable. When `f` is nonnegative on `(a, b)` the integrability is automatic
(`intervalIntegral.integrableOn_deriv_of_nonneg`), which matters for integrands that are unbounded
at an endpoint, such as `1 / √(x - a)`. This file records the combined statement.

In the converse direction, FTC-1 recovers the derivative of a `T`-periodic function `x` from the
integral equation `x(t) - x(0) = ∫₀ᵗ Y` over a single period `[0, T]`, when `Y` is continuous and
`T`-periodic: periodicity propagates the equation to all of `ℝ`.

## Main declarations

* `TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg`
* `TauCeti.hasDerivAt_of_periodic_of_sub_eq_integral`
-/

public section

open MeasureTheory Set

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

/-- **Periodic solutions of an integral equation.** Let `x` and a continuous `Y` be `T`-periodic,
with `T > 0`. If `x t - x 0 = ∫₀ᵗ Y` for every `t ∈ [0, T]`, then `x` has derivative `Y t` at every
`t`. -/
theorem hasDerivAt_of_periodic_of_sub_eq_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {x Y : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hxper : Function.Periodic x T) (hY : Continuous Y) (hYper : Function.Periodic Y T)
    (hint : ∀ t ∈ Icc 0 T, x t - x 0 = ∫ τ in 0..t, Y τ) (t : ℝ) : HasDerivAt x (Y t) t := by
  have hxT : x T = x 0 := by simpa using hxper 0
  have hintT : ∫ τ in 0..T, Y τ = 0 := by
    rw [← hint T ⟨hT.le, le_rfl⟩, hxT, sub_self]
  -- The difference of the two sides of the integral equation is periodic and vanishes on
  -- `[0, T)`, so it vanishes everywhere.
  have hall : ∀ t, x t = x 0 + ∫ τ in 0..t, Y τ := by
    set Φ : ℝ → E := fun t ↦ x 0 + (∫ τ in 0..t, Y τ) - x t
    have hΦper : Function.Periodic Φ T := fun t ↦ by
      have h := hYper.intervalIntegral_add_eq t 0
      rw [zero_add, hintT] at h
      simp only [Φ, hxper t]
      rw [← _root_.intervalIntegral.integral_add_adjacent_intervals (hY.intervalIntegrable 0 t)
        (hY.intervalIntegrable t (t + T)), h, add_zero]
    intro t
    obtain ⟨r, hr, htr⟩ := hΦper.exists_mem_Ico₀ hT t
    have h0 : Φ r = 0 := by
      simp only [Φ]
      rw [← hint r (Ico_subset_Icc_self hr)]
      abel
    exact (sub_eq_zero.1 (htr.trans h0)).symm
  have h := (_root_.intervalIntegral.integral_hasDerivAt_right (hY.intervalIntegrable 0 t)
    (hY.stronglyMeasurableAtFilter _ _) hY.continuousAt).const_add (x 0)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hall)

end TauCeti
