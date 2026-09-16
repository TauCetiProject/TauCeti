/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Cycle.Residue

/-!
# Cauchy's integral formula in homology form, for all derivatives

For `f` holomorphic on an open `U`, a closed piecewise-`C¹` curve `γ` in `U` that is
**null-homologous** there, and a point `z ∈ U` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`

for every `k : ℕ`, with `n_z(γ)` the generalized winding number. The case `k = 0` is the identity
`f(z) · n_z(γ) = (2πi)⁻¹ ∮_γ f(w)/(w − z) dw` that accompanies the homology Cauchy theorem,
and the general `k` is its derivative form.

This is the single-curve case of
`TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`:
a closed curve is a cycle with one component and multiplicity one. The formulas here use the
parametrization directly, so applications can express the contour integral as an interval integral
over the oriented interval `a..b`.

## Main results

* `TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous` — the formula above, for
  every order `k`.
* `TauCeti.Contour.cauchyIntegralFormula_nullHomologous` — its `k = 0` case, Cauchy's integral
  formula in homology form `∮_γ f(w)/(w − z) dw = 2πi · n_z(γ) · f z`.
* `TauCeti.Contour.cauchyIntegralFormula_deriv_nullHomologous` — its `k = 1` case, stated with
  `deriv f z`.

## Relation to Mathlib

Mathlib's Cauchy integral formulas are all stated for a round circle: the higher-derivative ones
(`Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable` and its
`DiffContOnCl` / `DifferentiableOn` variants) evaluate the circle integral of
`(w − c)^{−(k+1)} • f w` at the **centre** `c` of the circle only, and the off-centre one
(`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`) is the case `k = 0`. Mathlib
has no winding number for a general curve, hence no formula weighted by one; that is what the
statements here supply.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 (the index of a point and the homology form of Cauchy's
  theorem and integral formula).
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.

## Provenance

No formal source is vendored: the statements specialize the repository's Cauchy integral formula
for cycles, built on the residue and contour APIs migrated from the AINTLIB `LeanModularForms`
development.
-/

public section

open Complex MeasureTheory Set

open scoped Interval Real

namespace TauCeti.Contour

/-- **Cauchy's integral formula for the `k`-th derivative, homology form.** Let `f` be holomorphic
on an open `U`, let `γ` be a closed piecewise-`C¹` curve in `U` that is null-homologous there, and
let `z ∈ U` lie off the curve. Then for every `k`,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`,

the `k`-th Taylor coefficient of `f` at `z` weighted by the generalized winding number of `γ` about
`z`. Only the residue at `z` contributes: the residue theorem for a null-homologous cycle applied
to the Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)`, whose only possible singularity in `U` is at
`z`, leaves the single residue `iteratedDeriv k f z / k !`. -/
theorem cauchyIntegralFormula_iteratedDeriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  -- The raw-curve comparison lemmas identify the single-generator cycle with the given curve.
  simpa only [Cycle.integral_of_raw, Cycle.windingNumber_of_raw] using
    Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf
      ((Cycle.isIn_of_raw_iff γ hγ hclosed U).2 hγU)
      ((Cycle.isNullHomologous_of_raw_iff γ hγ hclosed U).2 hnull) hz
      (by simpa only [Cycle.trace_of_raw, Set.mem_image, not_exists, not_and] using hoff) k

/-- **Cauchy's integral formula, homology form.** For `f` holomorphic on an open
`U`, `γ` a closed piecewise-`C¹` curve in `U` that is null-homologous there, and `z ∈ U` off the
curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z)) = 2πi · n_z(γ) · f z`,

so that `f z · n_z(γ) = (2πi)⁻¹ ∮_γ f(w)/(w − z) dw`: the Cauchy-type integral recovers the value of
`f` at `z`, counted with the multiplicity with which `γ` winds around it. The `S = ∅` companion of
this statement is the homology Cauchy theorem `TauCeti.Contour.homologyCauchyTheorem`. -/
theorem cauchyIntegralFormula_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z := by
  simpa using cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hγ hγU hclosed hnull hz
    hoff 0

/-- **Cauchy's integral formula for the first derivative, homology form.** The `k = 1` case of
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, stated with `deriv f z`:

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ 2) = 2πi · n_z(γ) · f' z`. -/
theorem cauchyIntegralFormula_deriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ 2)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hγ hγU hclosed hnull hz hoff 1

end TauCeti.Contour

end
