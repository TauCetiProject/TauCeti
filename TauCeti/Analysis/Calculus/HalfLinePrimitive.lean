/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The primitive of a function on the nonnegative half-line

Given `f : ℝ → E` with values in a real normed space, this file constructs
`TauCeti.halfLinePrimitive f`, the primitive `t ↦ ∫₀ᵗ f` of `f` on `[0, ∞)`. To make the function
total on `ℝ`, the integrand is composed with `max · 0`, so on `[0, ∞)` the value is the ordinary
integral `∫₀ᵗ f` and on `(-∞, 0]` it is the linear extension `t ↦ t • f 0`.

The construction is generic calculus: it depends only on Mathlib's fundamental theorem of
calculus.

## Main declarations

* `TauCeti.halfLinePrimitive`: the primitive `∫₀ᵗ f` of `f` on the nonnegative half-line.
* `TauCeti.halfLinePrimitive_def`: the unconditional defining equation
  `halfLinePrimitive f t = ∫₀ᵗ f (max x 0)`.
* `TauCeti.halfLinePrimitive_eq_integral_of_nonneg`, `TauCeti.halfLinePrimitive_of_nonpos`: the
  value of the primitive on each half-line.
* `TauCeti.continuous_halfLinePrimitive`: the primitive is continuous on all of `ℝ` whenever `f`
  is locally integrable on `[0, ∞)`.
* `TauCeti.hasDerivAt_halfLinePrimitive`, `TauCeti.deriv_halfLinePrimitive`: its derivative is
  `f t` at every nonnegative point `t` at which `f` is continuous within `[0, ∞)`.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {t : ℝ}

/-- If `f` is locally integrable on `[0, ∞)`, then its extension `x ↦ f (max x 0)` is interval
integrable on every interval. -/
private theorem intervalIntegrable_comp_max_zero (hf : LocallyIntegrableOn f (Ici 0)) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ f (max x 0)) volume a b := by
  suffices h : ∀ x, IntervalIntegrable (fun x ↦ f (max x 0)) volume 0 x from
    (h a).symm.trans (h b)
  intro x
  rcases le_total 0 x with hx | hx
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2 <|
      (hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).congr_fun
        (fun y hy ↦ by rw [max_eq_left hy.1]) measurableSet_Icc
  · refine (intervalIntegrable_const (c := f 0)).congr fun y hy ↦ ?_
    rw [uIoc_of_ge hx] at hy
    simp only [max_eq_right hy.2]

variable [NormedSpace ℝ E]

/-- The primitive of `f` on the nonnegative half-line. The `max` canonically extends the
integrand to negative arguments; on `[0, ∞)` this is `∫₀ᵗ f`. -/
noncomputable def halfLinePrimitive (f : ℝ → E) (t : ℝ) : E :=
  ∫ x in (0 : ℝ)..t, f (max x 0)

/-- The unconditional defining equation of `halfLinePrimitive`, usable in downstream files where
the body of the definition is not available. -/
theorem halfLinePrimitive_def (f : ℝ → E) (t : ℝ) :
    halfLinePrimitive f t = ∫ x in (0 : ℝ)..t, f (max x 0) := by rfl

/-- On the nonnegative half-line, `halfLinePrimitive` is the ordinary integral of `f` from
zero. -/
@[grind =>]
theorem halfLinePrimitive_eq_integral_of_nonneg (ht : 0 ≤ t) :
    halfLinePrimitive f t = ∫ x in (0 : ℝ)..t, f x := by
  rw [halfLinePrimitive_def]
  refine integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le ht] at hx
  simp only [max_eq_left hx.1]

/-- On the nonpositive half-line, `halfLinePrimitive` is the linear extension `t ↦ t • f 0`. -/
theorem halfLinePrimitive_of_nonpos [CompleteSpace E] (ht : t ≤ 0) :
    halfLinePrimitive f t = t • f 0 := by
  rw [halfLinePrimitive_def, integral_congr (g := fun _ ↦ f 0) fun x hx ↦ ?_]
  · simp
  · rw [uIcc_of_ge ht] at hx
    simp only [max_eq_right hx.2]

/-- The value of `halfLinePrimitive f` at the origin is `0`. -/
@[simp]
theorem halfLinePrimitive_zero (f : ℝ → E) : halfLinePrimitive f 0 = 0 := by
  simp [halfLinePrimitive_def]

/-- If `f` is locally integrable on `[0, ∞)`, then `halfLinePrimitive f` is continuous on all of
`ℝ`; the `max` extension of the integrand makes the primitive continuous through the origin. -/
theorem continuous_halfLinePrimitive (hf : LocallyIntegrableOn f (Ici 0)) :
    Continuous (halfLinePrimitive f) := by
  unfold halfLinePrimitive
  exact continuous_primitive (intervalIntegrable_comp_max_zero hf) 0

/-- If `f` is locally integrable on `[0, ∞)` and continuous within `[0, ∞)` at `t ≥ 0`, then
`halfLinePrimitive f` has derivative `f t` at `t`. The `max` extension of the integrand makes the
derivative at `t = 0` two-sided. -/
theorem hasDerivAt_halfLinePrimitive [CompleteSpace E] (hf : LocallyIntegrableOn f (Ici 0))
    (hft : ContinuousWithinAt f (Ici 0) t) (ht : 0 ≤ t) :
    HasDerivAt (halfLinePrimitive f) (f t) t := by
  have hint := intervalIntegrable_comp_max_zero hf
  have hcont : ContinuousAt (fun x ↦ f (max x 0)) t :=
    (continuousWithinAt_univ _ _).1 <|
      hft.comp_of_eq (continuous_id.max continuous_const).continuousWithinAt
        (fun x _ ↦ le_max_right x 0) (max_eq_left ht)
  unfold halfLinePrimitive
  simpa only [max_eq_left ht] using integral_hasDerivAt_right (hint 0 t)
    (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (hint (t - 1) (t + 1)).1.1
      (Ioc_mem_nhds (sub_one_lt t) (lt_add_one t))) hcont

/-- If `f` is locally integrable on `[0, ∞)` and continuous within `[0, ∞)` at `t ≥ 0`, then the
derivative of `halfLinePrimitive f` at `t` is `f t`. -/
@[grind =>]
theorem deriv_halfLinePrimitive [CompleteSpace E] (hf : LocallyIntegrableOn f (Ici 0))
    (hft : ContinuousWithinAt f (Ici 0) t) (ht : 0 ≤ t) :
    deriv (halfLinePrimitive f) t = f t :=
  (hasDerivAt_halfLinePrimitive hf hft ht).deriv

end TauCeti

end
