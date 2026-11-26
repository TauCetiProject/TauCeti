/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.ODE.Wronskian
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Wronskians of solutions of the associated Legendre equation

The associated Legendre equation (DLMF 14.2.2, 14.21.1) of degree `ν` and order `μ` is
`(1 - z²) w'' - 2 z w' + (ν (ν + 1) - μ² / (1 - z²)) w = 0`,
which is the Sturm–Liouville equation `((1 - z²) w')' + q w = 0` with
`q = ν (ν + 1) - μ² / (1 - z²)`. A solution on an open set `V ⊆ ℂ` is a function complex
differentiable on `V` that satisfies the equation at each point of `V`, with `deriv` and
`deriv^[2]`; the equation is not packaged as a predicate. The Wronskian `𝒲{f, g}` is written out
as `f z * deriv g z - deriv f z * g z`.

This file proves the facts about Wronskians that replace the general theory of linear
differential equations for the Legendre functions: Lagrange's identity, Abel's identity, and the
span criterion. By Abel's identity the Wronskian of two solutions is `C / (1 - z²)` with a constant
`C`, which can be read off from the behaviour of the solutions at a singular point; by the span
criterion a solution is a combination of a fundamental pair with constant coefficients, which can
be fixed from values or limits. Lagrange's and Abel's identities are the special cases of the
corresponding identities for Sturm–Liouville equations in `TauCeti.Analysis.ODE.Wronskian`, and
the span criterion follows from Abel's identity by Cramer's rule.

## Main results

* `TauCeti.hasDerivAt_one_sub_sq_mul_wronskian_of_legendreEquation`: Lagrange's identity: if `f`
  solves the equation with `(ν₁, μ₁)` and `g` with `(ν₂, μ₂)`, then `(1 - z²) 𝒲{f, g}` has
  derivative `((ν₁ - ν₂) (ν₁ + ν₂ + 1) - (μ₁² - μ₂²) / (1 - z²)) f g`.
* `TauCeti.one_sub_sq_mul_wronskian_eq_of_legendreEquation`: Abel's identity: for two solutions
  with the same `(ν, μ)` on a preconnected open set, `(1 - z²) 𝒲{f, g}` is constant.
* `TauCeti.wronskian_ne_zero_of_legendreEquation`: on a preconnected open set, the Wronskian of
  two solutions is nowhere zero as soon as it is nonzero at one point `z₀` with `z₀ ≠ ±1`.
* `TauCeti.exists_eq_mul_add_mul_of_legendreEquation`: the span criterion: on a preconnected
  open set, two solutions whose Wronskian is nonzero at one point `z₀` with `z₀ ≠ ±1` span all
  solutions.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 5 §12.3.
* [DLMF] *NIST Digital Library of Mathematical Functions*, §14.2 and §14.21,
  <https://dlmf.nist.gov/14.2>.
-/

public section

namespace TauCeti

variable {f g w : ℂ → ℂ} {V : Set ℂ}

/-- The associated Legendre equation in the expanded Sturm–Liouville form
`(1 - z²) w'' + (-2z) w' + q w = 0` used by `TauCeti.hasDerivAt_mul_wronskian_of_sturmLiouville`. -/
private theorem legendreEquation_sturmLiouville {ν μ z : ℂ}
    (hw : (1 - z ^ 2) * deriv^[2] w z - 2 * z * deriv w z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * w z = 0) :
    (1 - z ^ 2) * deriv (deriv w) z + -2 * z * deriv w z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * w z = 0 := by
  rw [Function.iterate_succ_apply', Function.iterate_one] at hw
  linear_combination hw

/-- The coefficient `1 - z²` of the associated Legendre equation has derivative `-2z`. -/
private theorem hasDerivAt_one_sub_sq (z : ℂ) : HasDerivAt (fun x : ℂ ↦ 1 - x ^ 2) (-2 * z) z := by
  convert (hasDerivAt_pow 2 z).const_sub 1 using 1
  ring

/-- **Lagrange's identity for the associated Legendre equation.** If `f` solves the associated
Legendre equation with degree `ν₁` and order `μ₁` at `z`, and `g` with degree `ν₂` and order `μ₂`,
both analytic at `z`, then `(1 - z²) 𝒲{f, g}` has derivative
`((ν₁ - ν₂) (ν₁ + ν₂ + 1) - (μ₁² - μ₂²) / (1 - z²)) f g` at `z`. -/
theorem hasDerivAt_one_sub_sq_mul_wronskian_of_legendreEquation {ν₁ μ₁ ν₂ μ₂ z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hfe : (1 - z ^ 2) * deriv^[2] f z - 2 * z * deriv f z +
      (ν₁ * (ν₁ + 1) - μ₁ ^ 2 / (1 - z ^ 2)) * f z = 0)
    (hge : (1 - z ^ 2) * deriv^[2] g z - 2 * z * deriv g z +
      (ν₂ * (ν₂ + 1) - μ₂ ^ 2 / (1 - z ^ 2)) * g z = 0) :
    HasDerivAt (fun x ↦ (1 - x ^ 2) * (f x * deriv g x - deriv f x * g x))
      (((ν₁ - ν₂) * (ν₁ + ν₂ + 1) - (μ₁ ^ 2 - μ₂ ^ 2) / (1 - z ^ 2)) * f z * g z) z := by
  convert hasDerivAt_mul_wronskian_of_sturmLiouville (hasDerivAt_one_sub_sq z)
    hf.differentiableAt hf.deriv.differentiableAt hg.differentiableAt hg.deriv.differentiableAt
    (legendreEquation_sturmLiouville hfe) (legendreEquation_sturmLiouville hge) using 1
  ring

/-- **Abel's identity for the associated Legendre equation** (Olver, Ch. 5 §12.3): for two
solutions `f`, `g` of the associated Legendre equation with the same degree `ν` and order `μ` on a
preconnected open set `V`, the product `(1 - z²) 𝒲{f, g}(z)` is constant on `V`. -/
theorem one_sub_sq_mul_wronskian_eq_of_legendreEquation {ν μ : ℂ} (hV : IsOpen V)
    (hVc : IsPreconnected V) (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (hfe : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] f z - 2 * z * deriv f z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * f z = 0)
    (hge : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] g z - 2 * z * deriv g z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * g z = 0)
    {x z : ℂ} (hx : x ∈ V) (hz : z ∈ V) :
    (1 - x ^ 2) * (f x * deriv g x - deriv f x * g x) =
      (1 - z ^ 2) * (f z * deriv g z - deriv f z * g z) :=
  mul_wronskian_eq_of_sturmLiouville (p := fun x ↦ 1 - x ^ 2) hV hVc
    (fun z _ ↦ hasDerivAt_one_sub_sq z) hf (hf.deriv hV) hg (hg.deriv hV)
    (fun z hz ↦ legendreEquation_sturmLiouville (hfe z hz))
    (fun z hz ↦ legendreEquation_sturmLiouville (hge z hz)) hx hz

/-- On a preconnected open set `V`, the Wronskian `𝒲{f, g}` of two solutions of the associated
Legendre equation with the same degree `ν` and order `μ` vanishes nowhere on `V` as soon as it is
nonzero at one point `z₀ ∈ V` with `1 - z₀² ≠ 0`. -/
theorem wronskian_ne_zero_of_legendreEquation {ν μ : ℂ} (hV : IsOpen V) (hVc : IsPreconnected V)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (hfe : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] f z - 2 * z * deriv f z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * f z = 0)
    (hge : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] g z - 2 * z * deriv g z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * g z = 0)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ V) (hz₀' : 1 - z₀ ^ 2 ≠ 0)
    (hW : f z₀ * deriv g z₀ - deriv f z₀ * g z₀ ≠ 0) (hz : z ∈ V) :
    f z * deriv g z - deriv f z * g z ≠ 0 := by
  intro h
  have := one_sub_sq_mul_wronskian_eq_of_legendreEquation hV hVc hf hg hfe hge hz hz₀
  rw [h, mul_zero] at this
  exact mul_ne_zero hz₀' hW this.symm

/-- **Span criterion for the associated Legendre equation.** On a preconnected open set `V`, if
two solutions `f`, `g` of the associated Legendre equation with degree `ν` and order `μ` have
nonzero Wronskian `𝒲{f, g}` at one point `z₀ ∈ V` with `1 - z₀² ≠ 0`, then every solution `w` on
`V` with the same `ν` and `μ` is `α f + β g` on `V`, with constants `α`, `β`. -/
theorem exists_eq_mul_add_mul_of_legendreEquation {ν μ : ℂ} (hV : IsOpen V)
    (hVc : IsPreconnected V)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V) (hw : DifferentiableOn ℂ w V)
    (hfe : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] f z - 2 * z * deriv f z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * f z = 0)
    (hge : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] g z - 2 * z * deriv g z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * g z = 0)
    (hwe : ∀ z ∈ V, (1 - z ^ 2) * deriv^[2] w z - 2 * z * deriv w z +
      (ν * (ν + 1) - μ ^ 2 / (1 - z ^ 2)) * w z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀' : 1 - z₀ ^ 2 ≠ 0)
    (hW : f z₀ * deriv g z₀ - deriv f z₀ * g z₀ ≠ 0) :
    ∃ α β : ℂ, ∀ z ∈ V, w z = α * f z + β * g z := by
  -- Cramer's rule: `w 𝒲{f, g} = 𝒲{w, g} f + 𝒲{f, w} g` at every point, and by Abel's identity
  -- each of the three Wronskians at `z` is `(1 - z₀²) / (1 - z²)` times its value at `z₀`.
  refine ⟨(w z₀ * deriv g z₀ - deriv w z₀ * g z₀) / (f z₀ * deriv g z₀ - deriv f z₀ * g z₀),
    (f z₀ * deriv w z₀ - deriv f z₀ * w z₀) / (f z₀ * deriv g z₀ - deriv f z₀ * g z₀),
    fun z hz ↦ ?_⟩
  have hfg := one_sub_sq_mul_wronskian_eq_of_legendreEquation hV hVc hf hg hfe hge hz hz₀
  have hwg := one_sub_sq_mul_wronskian_eq_of_legendreEquation hV hVc hw hg hwe hge hz hz₀
  have hfw := one_sub_sq_mul_wronskian_eq_of_legendreEquation hV hVc hf hw hfe hwe hz hz₀
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
  refine mul_left_cancel₀ hz₀' ?_
  linear_combination -(w z) * hfg + f z * hwg + g z * hfw

end TauCeti
