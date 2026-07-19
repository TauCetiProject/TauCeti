/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bernstein primitives of completely monotone functions

This file establishes one direction of the standard correspondence between completely monotone
and Bernstein functions. If `f` is completely monotone on `[0, ∞)`, then

`t ↦ c + ∫ x in 0..t, f x` for `t ≥ 0`

is a Bernstein function whenever `c ≥ 0`. Its derivative on `(0, ∞)` is `f`, so complete
monotonicity of the derivative is inherited directly from `f`. The special case `c = 0` gives
the canonical primitive vanishing at the origin.

## Main declarations

* `TauCeti.bernsteinPrimitive`: the primitive `c + ∫₀ᵗ f`.
* `TauCeti.hasDerivAt_bernsteinPrimitive`: its derivative is `f` at every nonnegative point.
* `TauCeti.IsCompletelyMonotone.isBernsteinFunction_bernsteinPrimitive`: a nonnegative
  primitive of a completely monotone function is Bernstein.
* `TauCeti.IsCompletelyMonotone.isBernsteinFunction_integral`: the primitive vanishing at zero
  is Bernstein.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 3.
-/

public section

open Set intervalIntegral
open scoped ContDiff

namespace TauCeti

/-- The primitive of `f` on the nonnegative half-line with initial value `c`. The `max`
canonically extends the integrand to negative arguments; on `[0, ∞)` this is `c + ∫₀ᵗ f`. -/
noncomputable def bernsteinPrimitive (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  c + ∫ x in (0 : ℝ)..t, f (max x 0)

/-- On the nonnegative half-line, `bernsteinPrimitive` is the ordinary integral of `f` from
zero, with initial value `c`. -/
theorem bernsteinPrimitive_eq {c : ℝ} {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    bernsteinPrimitive c f t = c + ∫ x in (0 : ℝ)..t, f x := by
  rw [bernsteinPrimitive]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le ht] at hx
  simp only [max_eq_left hx.1]

/-- The value of `bernsteinPrimitive c f` at the origin is `c`. -/
@[simp]
theorem bernsteinPrimitive_zero (c : ℝ) (f : ℝ → ℝ) :
    bernsteinPrimitive c f 0 = c := by
  simp [bernsteinPrimitive]

/-- A primitive built from a continuous function has derivative `f t` at every nonnegative
point. -/
theorem hasDerivAt_bernsteinPrimitive {c : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    HasDerivAt (bernsteinPrimitive c f) (f t) t := by
  have hcontinuous : Continuous (fun x : ℝ ↦ f (max x 0)) := by
    convert hf.comp_continuous (continuous_id.max continuous_const)
      (fun x ↦ mem_Ici.mpr (le_max_right x 0)) using 1
    ext x
    rfl
  -- Expose the primitive here so the FTC theorem sees its defining integral.
  change HasDerivAt (fun u ↦ c + ∫ x in (0 : ℝ)..u, f (max x 0)) (f t) t
  simpa only [bernsteinPrimitive, max_eq_left ht] using
    (intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ))
      (hcontinuous.intervalIntegrable 0 t)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt).const_add c

/-- The derivative of a primitive built from a continuous function is its integrand at every
nonnegative point. -/
theorem deriv_bernsteinPrimitive {c : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    deriv (bernsteinPrimitive c f) t = f t :=
  (hasDerivAt_bernsteinPrimitive hf ht).deriv

namespace IsCompletelyMonotone

variable {f : ℝ → ℝ}

/-- A nonnegative primitive of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_bernsteinPrimitive (hf : IsCompletelyMonotone f) {c : ℝ}
    (hc : 0 ≤ c) : IsBernsteinFunction (bernsteinPrimitive c f) := by
  have hintegrand : Continuous (fun x : ℝ ↦ f (max x 0)) := by
    convert hf.contDiffOn.continuousOn.comp_continuous
      (continuous_id.max continuous_const) (fun x ↦ mem_Ici.mpr (le_max_right x 0)) using 1
    ext x
    rfl
  have hcontinuous : ContinuousOn (bernsteinPrimitive c f) (Ici 0) :=
    (continuous_const.add
      (intervalIntegral.continuous_primitive
        (fun a b ↦ hintegrand.intervalIntegrable a b) 0)).continuousOn
  have hcontDiff : ContDiffOn ℝ ∞ (bernsteinPrimitive c f) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht ↦ (hasDerivAt_bernsteinPrimitive hf.contDiffOn.continuousOn
      ht.le).differentiableAt.differentiableWithinAt, ?_⟩
    exact (hf.contDiffOn.mono Ioi_subset_Ici_self).congr fun t ht ↦
      deriv_bernsteinPrimitive hf.contDiffOn.continuousOn ht.le
  rw [isBernsteinFunction_iff]
  refine ⟨hcontinuous, hcontDiff, fun t ht ↦ ?_, ?_⟩
  · rw [bernsteinPrimitive]
    exact add_nonneg hc
      (intervalIntegral.integral_nonneg ht fun x _ ↦ hf.nonneg (le_max_right x 0))
  · apply hf.isCompletelyMonotoneOnIoi.congr
    intro t ht
    exact deriv_bernsteinPrimitive hf.contDiffOn.continuousOn ht.le

/-- The primitive of a completely monotone function that vanishes at the origin is a Bernstein
function. -/
theorem isBernsteinFunction_integral (hf : IsCompletelyMonotone f) :
    IsBernsteinFunction (bernsteinPrimitive 0 f) :=
  hf.isBernsteinFunction_bernsteinPrimitive le_rfl

end IsCompletelyMonotone

end TauCeti

end
