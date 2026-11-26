/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.DividedDifference.Basic
import TauCeti.Analysis.Calculus.DSlope.Analytic
import TauCeti.Analysis.Calculus.DSlope.Integral
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Integral representation and entireness of coordinate divided differences

For an entire function `f : (ι → ℂ) → E` (with `ι` finite and `E` complete), the coordinate
divided difference `TauCeti.partialDslope i f ζ` is entire (`TauCeti.differentiable_partialDslope`,
via `TauCeti.analyticAt_dslope_update`) and admits the integral representation
`g z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt` (`TauCeti.partialDslope_eq_integral`).

## Main results

* `TauCeti.partialDslope_eq_integral`: integral representation of `partialDslope i f ζ` for
  entire `f`.
* `TauCeti.differentiable_partialDslope`: `partialDslope i f ζ` is entire when `f` is.
-/

public section

open Function Set

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

/-- **Integral representation of the divided difference.** For an entire `f`,
`partialDslope i f ζ z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt`. -/
theorem partialDslope_eq_integral [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i f ζ z =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update z i (ζ + t * (z i - ζ))) := by
  rw [partialDslope_apply, dslope_eq_integral_deriv isOpen_univ
    (differentiable_comp_update hf z i).contDiff.contDiffOn (subset_univ _)]
  congr 1 with t
  rw [Complex.real_smul, (hasDerivAt_comp_update (hf _)).deriv]

/-- **The divided difference of an entire function is entire.** -/
theorem differentiable_partialDslope [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) : Differentiable ℂ (partialDslope i f ζ) := by
  have := Fintype.ofFinite ι
  intro z
  have hfz := hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem (z := z)
  have hfζ :=
    hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem (z := update z i ζ)
  rw [show partialDslope i f ζ = fun q ↦ dslope (fun w ↦ f (update q i w)) ζ (q i) from
    funext (partialDslope_apply i f ζ)]
  exact (TauCeti.analyticAt_dslope_update i ζ hfz hfζ).differentiableAt

end TauCeti
