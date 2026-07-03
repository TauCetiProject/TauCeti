/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The generalized winding number (Hungerbühler–Wasem Def 2.1)

For a curve `γ : ℝ → ℂ` on an interval `[a, b]` and a point `z₀ : ℂ`, the **generalized winding
number** is the normalized contour integral
`n_{z₀}(γ) = (2πi)⁻¹ ∫_a^b γ'(t) / (γ(t) − z₀) dt`
(Hungerbühler–Wasem, arXiv:1808.00997, Def 2.1). Closedness `γ a = γ b` is **not** part of the
definition; it is the hypothesis under which this is a genuine winding number — the classical
integer index when `z₀ ∉ γ '' [a, b]`, and the geometric angle `α / 2π` (in general non-integer)
when `z₀` lies on `γ`.

The definition places no regularity hypothesis on `γ` (it is intended to be applied to piecewise
`C¹` curves), so it is available unconditionally and the regularity is carried on the theorems that
need it.

## Main definitions

* `windingNumber γ a b z₀` — the generalized winding number `(2πi)⁻¹ ∫_a^b γ' / (γ − z₀)`.
* `IsNullHomologous γ a b Ω` — the cycle `γ` winds zero times about every point outside `Ω`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Def 2.1.
-/

public section

noncomputable section

open intervalIntegral

namespace TauCeti.Contour

/-- **The generalized winding number** (Hungerbühler–Wasem Def 2.1): for `γ : ℝ → ℂ` on `[a, b]`
and `z₀ : ℂ`,
`windingNumber γ a b z₀ = (2πi)⁻¹ ∫_a^b γ'(t) / (γ(t) − z₀) dt`.
Closedness of `γ` is not assumed here; it is imposed on the theorems for which this value is a
genuine winding number. -/
@[expose]
def windingNumber (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, deriv γ t / (γ t - z₀)

/-- **A cycle is null-homologous in `Ω`** when its generalized winding number about every point
outside `Ω` vanishes — the hypothesis of the homology form of Cauchy's theorem and of the
Hungerbühler–Wasem residue theorem. -/
def IsNullHomologous (γ : ℝ → ℂ) (a b : ℝ) (Ω : Set ℂ) : Prop :=
  ∀ w ∉ Ω, windingNumber γ a b w = 0

end TauCeti.Contour

end
