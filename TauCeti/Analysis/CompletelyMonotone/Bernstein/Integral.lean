/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitives of completely monotone functions are Bernstein functions

This file establishes one direction of the standard correspondence between completely monotone
and Bernstein functions. If `f` is completely monotone on `(0, ∞)` and continuous on `[0, ∞)`,
then

`t ↦ ∫ x in 0..t, f x` for `t ≥ 0`

is a Bernstein function, and so is `t ↦ c + ∫ x in 0..t, f x` for every `c ≥ 0`. Its derivative
on `(0, ∞)` is `f`, so complete monotonicity of the derivative is inherited directly from `f`.

The primitive is packaged as `TauCeti.halfLinePrimitive`, which integrates `f (max x 0)` so that
the function is defined on all of `ℝ`; on `[0, ∞)` this agrees with `∫₀ᵗ f` by
`TauCeti.halfLinePrimitive_eq_integral_of_nonneg`, and on `(-∞, 0]` it is the linear
extension `t ↦ t * f 0` by `TauCeti.halfLinePrimitive_of_nonpos`.

## Main declarations

* `TauCeti.halfLinePrimitive`: the primitive `∫₀ᵗ f` of `f` on the nonnegative half-line.
* `TauCeti.halfLinePrimitive_eq_integral_of_nonneg`,
  `TauCeti.halfLinePrimitive_of_nonpos`: the value of the primitive on each half-line.
* `TauCeti.hasDerivAt_halfLinePrimitive`, `TauCeti.deriv_halfLinePrimitive`: its derivative is
  `f` at every nonnegative point.
* `TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_halfLinePrimitive`,
  `TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_const_add_halfLinePrimitive`: the
  primitive of a completely monotone function, and its shifts by a nonnegative constant, are
  Bernstein.
* `TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_integral`: the same statement written
  directly in terms of `∫ x in 0..t, f x`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 3.
-/

public section

open Set intervalIntegral
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ} {t : ℝ}

/-- The primitive of `f` on the nonnegative half-line. The `max` canonically extends the
integrand to negative arguments; on `[0, ∞)` this is `∫₀ᵗ f`. -/
noncomputable def halfLinePrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, f (max x 0)

/-- If `f` is continuous on `[0, ∞)`, then its extension `x ↦ f (max x 0)` is continuous on all
of `ℝ`. -/
private theorem continuous_comp_max_zero (hf : ContinuousOn f (Ici 0)) :
    Continuous fun x : ℝ ↦ f (max x 0) := by
  simpa [Function.comp_def] using
    hf.comp_continuous (continuous_id'.max continuous_const) fun x ↦ mem_Ici.mpr (le_max_right x 0)

/-- On the nonnegative half-line, `halfLinePrimitive` is the ordinary integral of `f` from
zero. -/
@[grind =>]
theorem halfLinePrimitive_eq_integral_of_nonneg (ht : 0 ≤ t) :
    halfLinePrimitive f t = ∫ x in (0 : ℝ)..t, f x := by
  rw [halfLinePrimitive]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le ht] at hx
  simp only [max_eq_left hx.1]

/-- On the nonpositive half-line, `halfLinePrimitive` is the linear extension `t ↦ t * f 0`. -/
theorem halfLinePrimitive_of_nonpos (ht : t ≤ 0) : halfLinePrimitive f t = t * f 0 := by
  rw [halfLinePrimitive]
  rw [show (∫ x in (0 : ℝ)..t, f (max x 0)) = ∫ _ in (0 : ℝ)..t, f 0 from
    intervalIntegral.integral_congr fun x hx => by
      simp only [uIcc_of_ge ht] at hx
      simp only [max_eq_right hx.2]]
  simp

/-- The value of `halfLinePrimitive f` at the origin is `0`. -/
@[simp]
theorem halfLinePrimitive_zero (f : ℝ → ℝ) : halfLinePrimitive f 0 = 0 := by
  simp [halfLinePrimitive]

/-- If `f` is continuous on `[0, ∞)`, then `halfLinePrimitive f` has derivative `f t` at every
`t ≥ 0`. The `max` extension of the integrand makes the derivative at `t = 0` two-sided. -/
theorem hasDerivAt_halfLinePrimitive (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    HasDerivAt (halfLinePrimitive f) (f t) t := by
  have hcont := continuous_comp_max_zero hf
  -- Expose the defining integral, which is what the fundamental theorem of calculus is about.
  change HasDerivAt (fun u ↦ ∫ x in (0 : ℝ)..u, f (max x 0)) (f t) t
  simpa only [max_eq_left ht] using
    intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- If `f` is continuous on `[0, ∞)`, then the derivative of `halfLinePrimitive f` is `f` at
every `t ≥ 0`. -/
@[grind =>]
theorem deriv_halfLinePrimitive (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    deriv (halfLinePrimitive f) t = f t :=
  (hasDerivAt_halfLinePrimitive hf ht).deriv

namespace IsCompletelyMonotoneOnIoi

/-- A function that is completely monotone on `(0, ∞)` and continuous on `[0, ∞)` is
nonnegative on `[0, ∞)`. -/
theorem nonneg_of_continuousOn (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases ht.lt_or_eq with h | h
  · exact hf.nonneg h
  · subst h
    have htends : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds (f 0)) :=
      (hcont 0 self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htends (eventually_mem_nhdsWithin.mono fun x hx => hf.nonneg hx)

/-- The primitive on `[0, ∞)` of a function that is completely monotone on `(0, ∞)` and
continuous on `[0, ∞)` is a Bernstein function. -/
theorem isBernsteinFunction_halfLinePrimitive (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) : IsBernsteinFunction (halfLinePrimitive f) := by
  have hcontinuous : ContinuousOn (halfLinePrimitive f) (Ici 0) := fun t ht ↦
    (hasDerivAt_halfLinePrimitive hcont ht).continuousAt.continuousWithinAt
  have hcontDiff : ContDiffOn ℝ ∞ (halfLinePrimitive f) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht ↦
      (hasDerivAt_halfLinePrimitive hcont ht.le).differentiableAt.differentiableWithinAt, ?_⟩
    exact hf.contDiffOn.congr fun t ht ↦ deriv_halfLinePrimitive hcont ht.le
  rw [isBernsteinFunction_iff]
  refine ⟨hcontinuous, hcontDiff, fun t ht ↦ ?_, ?_⟩
  · rw [halfLinePrimitive]
    exact intervalIntegral.integral_nonneg ht fun x hx ↦
      hf.nonneg_of_continuousOn hcont (le_max_right x 0)
  · exact hf.congr fun t ht ↦ deriv_halfLinePrimitive hcont ht.le

/-- Shifting the primitive of a completely monotone function by a nonnegative constant again
gives a Bernstein function. -/
theorem isBernsteinFunction_const_add_halfLinePrimitive (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (fun t ↦ c + halfLinePrimitive f t) :=
  ((isBernsteinFunction_const hc).add
    (hf.isBernsteinFunction_halfLinePrimitive hcont)).congr fun _ _ ↦ rfl

/-- The primitive `t ↦ ∫₀ᵗ f` of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_integral (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) :
    IsBernsteinFunction fun t ↦ ∫ x in (0 : ℝ)..t, f x :=
  (hf.isBernsteinFunction_halfLinePrimitive hcont).congr fun _ ht ↦
    (halfLinePrimitive_eq_integral_of_nonneg ht).symm

end IsCompletelyMonotoneOnIoi

namespace IsCompletelyMonotone

/-- The primitive on `[0, ∞)` of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_halfLinePrimitive (hf : IsCompletelyMonotone f) :
    IsBernsteinFunction (halfLinePrimitive f) :=
  hf.isCompletelyMonotoneOnIoi.isBernsteinFunction_halfLinePrimitive hf.contDiffOn.continuousOn

/-- Shifting the primitive of a completely monotone function by a nonnegative constant again
gives a Bernstein function. -/
theorem isBernsteinFunction_const_add_halfLinePrimitive (hf : IsCompletelyMonotone f) {c : ℝ}
    (hc : 0 ≤ c) : IsBernsteinFunction (fun t ↦ c + halfLinePrimitive f t) :=
  hf.isCompletelyMonotoneOnIoi.isBernsteinFunction_const_add_halfLinePrimitive
    hf.contDiffOn.continuousOn hc

/-- The primitive `t ↦ ∫₀ᵗ f` of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_integral (hf : IsCompletelyMonotone f) :
    IsBernsteinFunction fun t ↦ ∫ x in (0 : ℝ)..t, f x :=
  hf.isCompletelyMonotoneOnIoi.isBernsteinFunction_integral hf.contDiffOn.continuousOn

end IsCompletelyMonotone

end TauCeti

end
