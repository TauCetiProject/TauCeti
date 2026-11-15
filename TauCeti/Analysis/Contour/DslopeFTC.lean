/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Integrating `g z / z` through a primitive of `dslope g 0`

Let `g` be holomorphic near `0`. Off `0`, the integrand `g z / z` splits as
`dslope g 0 z + g 0 / z`: the removable-singularity quotient `dslope g 0` is holomorphic wherever
`g` is (Mathlib's `Complex.differentiableOn_dslope`), and the polar part `g 0 / z` carries the whole
singularity. So along a path `γ` avoiding `0`, a primitive `H` of `dslope g 0` evaluates the first
part as an endpoint difference, and the integral of `g z / z` reduces to `g 0` times the integral
of `dz / z`.

Along an arc of `circleMap 0 R` the integral of `dz / z` is elementary, the integrand being
constantly `i`, so the integral of `g z / z` over the arc on `[a, b]` is
`H (circleMap 0 R b) - H (circleMap 0 R a) + (b - a) i g 0`.

## Main results

* `TauCeti.Contour.integral_mul_div_eq_of_hasDerivAt_dslope` — along a path `γ` avoiding `0`, the
  integral of `g z / z` is `H (γ b) - H (γ a) + g 0 ∫ dz / z`.
* `TauCeti.Contour.integral_circleMap_mul_div_eq_of_hasDerivAt_dslope` — its specialization to an
  arc of `circleMap 0 R`.
-/

public section

open Set
open scoped Topology Interval

namespace TauCeti.Contour

variable {U : Set ℂ} {g H : ℂ → ℂ} {a b : ℝ}

/-- **The integral of `g z / z` through a primitive of `dslope g 0`.** Let `g` be holomorphic on
a neighbourhood `U` of `0` and `H` a primitive of `dslope g 0` on `U`. Along a path `γ` in `U`
avoiding `0`, with continuous velocity `γ'`, the integral of `g z / z` is the endpoint difference
of `H` plus `g 0` times the integral of `dz / z`. -/
theorem integral_mul_div_eq_of_hasDerivAt_dslope {γ γ' : ℝ → ℂ}
    (hU : U ∈ 𝓝 (0 : ℂ)) (hg : DifferentiableOn ℂ g U)
    (hH : ∀ z ∈ U, HasDerivAt H (dslope g 0 z) z)
    (hγ : ∀ s ∈ [[a, b]], HasDerivAt γ (γ' s) s) (hγ' : ContinuousOn γ' [[a, b]])
    (hγU : ∀ s ∈ [[a, b]], γ s ∈ U) (hγ0 : ∀ s ∈ [[a, b]], γ s ≠ 0) :
    ∫ s in a..b, γ' s * (g (γ s) / γ s) =
      H (γ b) - H (γ a) + g 0 * ∫ s in a..b, γ' s / γ s := by
  have hγc : ContinuousOn γ [[a, b]] := fun s hs ↦ (hγ s hs).continuousAt.continuousWithinAt
  have hd : ContinuousOn (fun s ↦ dslope g 0 (γ s)) [[a, b]] :=
    ((Complex.differentiableOn_dslope hU).mpr hg).continuousOn.comp hγc fun s hs ↦ hγU s hs
  have hq : ContinuousOn (fun s ↦ γ' s / γ s) [[a, b]] := hγ'.div hγc hγ0
  have hsplit : EqOn (fun s ↦ γ' s * (g (γ s) / γ s))
      (fun s ↦ dslope g 0 (γ s) * γ' s + g 0 * (γ' s / γ s)) [[a, b]] := by
    intro s hs
    have h0 := hγ0 s hs
    simp only [dslope_of_ne _ h0, slope_def_field, sub_zero]
    field_simp
    ring
  have hi : IntervalIntegrable (fun s ↦ dslope g 0 (γ s) * γ' s) MeasureTheory.volume a b :=
    (hd.mul hγ').intervalIntegrable
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hi
    ((hq.const_mul _).intervalIntegrable),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := H ∘ γ)
      (fun s hs ↦ (hH _ (hγU s hs)).comp s (hγ s hs)) hi]
  rfl

/-- **The integral of `g z / z` over an arc of a circle about `0`.** Let `g` be holomorphic on a
neighbourhood `U` of `0` and `H` a primitive of `dslope g 0` on `U`. If `R ≠ 0` and the arc of
`circleMap 0 R` on `[a, b]` lies in `U`, then the integral of `g z / z` over the arc, with the
velocity `circleMap 0 R θ * I` of the parametrization, is
`H (circleMap 0 R b) - H (circleMap 0 R a) + (b - a) i g 0`. -/
theorem integral_circleMap_mul_div_eq_of_hasDerivAt_dslope {R : ℝ} (hR : R ≠ 0)
    (hU : U ∈ 𝓝 (0 : ℂ)) (hg : DifferentiableOn ℂ g U)
    (hH : ∀ z ∈ U, HasDerivAt H (dslope g 0 z) z)
    (hcirc : ∀ θ ∈ [[a, b]], circleMap 0 R θ ∈ U) :
    ∫ θ in a..b, circleMap 0 R θ * Complex.I * (g (circleMap 0 R θ) / circleMap 0 R θ) =
      H (circleMap 0 R b) - H (circleMap 0 R a) + g 0 * ((b - a : ℂ) * Complex.I) := by
  have h : EqOn (fun θ ↦ circleMap 0 R θ * Complex.I / circleMap 0 R θ) (fun _ ↦ Complex.I)
      [[a, b]] := fun θ _ ↦ mul_div_cancel_left₀ _ (circleMap_ne_center hR)
  rw [integral_mul_div_eq_of_hasDerivAt_dslope hU hg hH (fun θ _ ↦ hasDerivAt_circleMap 0 R θ)
    (by fun_prop) hcirc (fun θ _ ↦ circleMap_ne_center hR), intervalIntegral.integral_congr h,
    intervalIntegral.integral_const, Complex.real_smul, Complex.ofReal_sub]

end TauCeti.Contour
