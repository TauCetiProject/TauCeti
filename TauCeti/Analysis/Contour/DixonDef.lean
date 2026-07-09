/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.WindingNumber
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Dixon's `h₁` and `h₂` functions and their defining identity

Dixon's proof of the homology form of Cauchy's theorem hinges on a single auxiliary function that
is analytic on all of `ℂ`. This file records its two constituent integrals and the algebraic
identity relating them; the analyticity, boundedness, and Liouville steps are developed downstream.

For a curve `γ : ℝ → ℂ` on the oriented interval with endpoints `a`, `b` and a holomorphic `f`:

* `dixonH1 f γ a b w = ∫ t in a..b, dslope f w (γ t) * deriv γ t` — built from the *difference
  quotient* `dslope f w (γ t) = (f (γ t) - f w) / (γ t - w)` (which extends continuously through
  `γ t = w`, where it is `deriv f w`), so it is defined for **every** `w`, including points on `γ`.
* `dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` — the Cauchy-type integral,
  defined for `w` off the curve.
* `dixonFunction f U γ a b w` — glues the two: `dixonH1` on `U`, `dixonH2` on its complement.

## Main results

* `TauCeti.Contour.dixonH1_eq_dixonH2_sub_winding` — for `w` off the curve,
  `dixonH1 f γ a b w = dixonH2 f γ a b w - 2πi · n(γ, w) · f w`, where `n(γ, w)` is the generalized
  `windingNumber`. This is what makes `dixonFunction` well-glued across `∂U`.

These are the building blocks of the `homologyCauchyTheorem` roadmap target
(`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3, proved by Dixon's argument).

## Provenance

Adapted from `dixonH1`, `dixonH2`, `dixonFunction`, and `dixonH1_eq_dixonH2_sub_winding_f` in
`DixonDef.lean` of the AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an
oriented interval with endpoints `a` and `b`. See J. D. Dixon, *A brief proof of Cauchy's integral
theorem*, Proc. Amer. Math. Soc. 29 (1971), and K. Hungerbühler, J. Wasem, *A generalized notion of
winding numbers*.
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Dixon's `h₁` integral** `∫ t in a..b, dslope f w (γ t) * deriv γ t`. Because the difference
quotient `dslope f w z = (f z - f w) / (z - w)` extends continuously through `z = w` (taking the
value `deriv f w`), this integral is defined for *every* `w`, including points on the curve `γ`. -/
noncomputable def dixonH1 (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in a..b, dslope f w (γ t) * deriv γ t

/-- **Dixon's `h₂` integral** `∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t`. This is the ordinary
Cauchy-type integral, defined for `w` off the curve. -/
noncomputable def dixonH2 (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t

open Classical in
/-- **Dixon's glued function** `dixonH1` on `U`, `dixonH2` on its complement. The two pieces agree
on the overlap by `dixonH1_eq_dixonH2_sub_winding` together with null-homology, which is what makes
the glued function analytic on all of `ℂ`. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ a b w else dixonH2 f γ a b w

/-- Off the curve, the `dslope` integrand splits into the Cauchy-type integrand minus the
winding-number integrand scaled by `f w`. -/
private theorem dslope_integrand_eq {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∀ t ∈ uIcc a b, dslope f w (γ t) * deriv γ t =
      f (γ t) / (γ t - w) * deriv γ t - f w / (γ t - w) * deriv γ t := fun t ht ↦ by
  rw [dslope_of_ne _ (hoff t ht), slope_def_field]; ring

/-- The `f w`-weighted term of the split integrand as a constant times the index integrand. -/
private theorem fw_div_eq (f : ℂ → ℂ) (γ : ℝ → ℂ) (w : ℂ) :
    (fun t ↦ f w / (γ t - w) * deriv γ t) = fun t ↦ f w * ((γ t - w)⁻¹ * deriv γ t) := by
  funext t; rw [div_eq_mul_inv, mul_assoc]

/-- **The `h₁`/`h₂` identity.** For `w` off the curve, `dixonH1 f γ a b w` differs from
`dixonH2 f γ a b w` by exactly `2πi · n(γ, w) · f w`, the generalized winding number scaled by
`f w`. The proof expands `dslope f w (γ t) = (f (γ t) - f w) / (γ t - w)`, splits the integral, and
identifies the second piece with `f w · ∫ (γ · - w)⁻¹ · deriv γ = 2πi · n(γ, w) · f w`. -/
theorem dixonH1_eq_dixonH2_sub_winding {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (h_cont : ContinuousOn γ (uIcc a b)) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    dixonH1 f γ a b w =
      dixonH2 f γ a b w - 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  have hw_int : ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t =
      2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w := by
    rw [windingNumber_eq_integral_of_avoidance h_cont hoff h_base_int, ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  have h_fw_div_int : IntervalIntegrable (fun t ↦ f w / (γ t - w) * deriv γ t) volume a b :=
    (fw_div_eq f γ w) ▸ (h_base_int.const_mul (f w))
  simp only [dixonH1, dixonH2]
  rw [intervalIntegral.integral_congr (dslope_integrand_eq hoff),
    intervalIntegral.integral_sub h_cauchy_int h_fw_div_int, fw_div_eq,
    intervalIntegral.integral_const_mul, hw_int]
  ring

/-- On `U`, the glued Dixon function is `dixonH1`. -/
theorem dixonFunction_eq_dixonH1 {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hw : w ∈ U) : dixonFunction f U γ a b w = dixonH1 f γ a b w := by
  rw [dixonFunction, if_pos hw]

/-- Off `U`, the glued Dixon function is `dixonH2`. -/
theorem dixonFunction_eq_dixonH2 {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hw : w ∉ U) : dixonFunction f U γ a b w = dixonH2 f γ a b w := by
  rw [dixonFunction, if_neg hw]

end TauCeti.Contour
