/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The fundamental theorem of calculus along a contour

If `G' = g` along the image of a curve `γ : ℝ → 𝕜`, then the contour integral of `g` along `γ`
is the endpoint difference `G (γ b) - G (γ a)`, and hence vanishes for a closed curve. The curve
is a raw function `γ : ℝ → 𝕜` on a parameter interval `[a, b]`, with no bundled path structure,
and the contour integral is the ordinary interval integral `∫ t in a..b, γ' t • g (γ t)`, where
`γ'` is either a supplied velocity or `deriv γ`. The statements for a curve with a derivative, or
a right derivative, at every interior point of the parameter interval hold over any `RCLike` field
`𝕜`, for `g G : 𝕜 → E` valued in a complete normed space `E` over `𝕜`; the scalar contour integral
of complex analysis is the case `𝕜 = E = ℂ`, where `γ' t • g (γ t) = γ' t * g (γ t)`. The
integrand follows the argument order of Mathlib's chain rule `HasDerivAt.scomp` and of
`intervalIntegral.integral_deriv_smul_deriv_comp'`.

The explicit-velocity form asks only for continuity of `G ∘ γ` on `[a, b]` and right derivatives
`γ' t` of the curve in the interior, matching the hypotheses of Mathlib's interval-integral
fundamental theorem of calculus `intervalIntegral.integral_eq_sub_of_hasDeriv_right`.

This is the statement that a function with a primitive integrates to zero around closed curves,
the elementary input to Cauchy's theorem and to the residue theorems. It is the chain rule
combined with Mathlib's interval-integral fundamental theorem of calculus.

An absolutely continuous curve is differentiable only almost everywhere. For such a curve
`γ : ℝ → ℂ` the same endpoint formula holds for the contour integral of `deriv G` when
`G : ℂ → ℂ` is holomorphic on an open set containing the curve: then `G ∘ γ` is absolutely
continuous, with derivative `deriv γ t • deriv G (γ t)` at almost every `t`.

## Main results

* `Contour.integral_smul_comp_eq_sub_of_hasDeriv_right` — an explicit-velocity form using a
  supplied right derivative `γ'`.
* `Contour.integral_deriv_smul_comp_eq_sub_of_hasDerivAt` — the same statement with `deriv γ`,
  for a curve differentiable in the interior.
* `Contour.integral_smul_comp_eq_zero_of_hasDeriv_right_of_closed` and
  `Contour.integral_deriv_smul_comp_eq_zero_of_hasDerivAt_of_closed` — closed-curve corollaries.
* `AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_sub` — the endpoint formula
  along an absolutely continuous curve, for `G` holomorphic on an open set containing it, and
  `AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_zero_of_closed`, its
  closed-curve corollary.

## Provenance

This is routine API around Mathlib's `intervalIntegral.integral_eq_sub_of_hasDeriv_right`,
following the contour-integral convention of N. Hungerbühler, M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997. Earlier formalizations of
the same step appear in the AINTLIB `LeanModularForms` sources
`ForMathlib/GeneralizedResidueTheory/CauchyPrimitive.lean`,
`ForMathlib/GeneralizedResidueTheory/ArcCalculus.lean`, and `ForMathlib/ArcFTC*.lean`; no formal
source is vendored here. The absolutely continuous form combines
`AbsolutelyContinuousOnInterval.comp_of_contDiffAt` with
`AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt`.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] {γ γ' : ℝ → 𝕜} {g G : 𝕜 → E} {a b : ℝ}

/-- **FTC along a contour, explicit-velocity form.** If `γ' t` is the right derivative of the
curve `γ` and `G' = g` at the points `γ t`, then the contour integral of `g` along `γ` is the
endpoint difference `G (γ b) - G (γ a)`. The integrability hypothesis is stated directly on the
contour integrand, so this lemma can be used with any regularity package that supplies it. -/
theorem integral_smul_comp_eq_sub_of_hasDeriv_right
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivWithinAt γ (γ' t) (Set.Ioi t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => γ' t • g (γ t)) volume a b) :
    ∫ t in a..b, γ' t • g (γ t) = G (γ b) - G (γ a) :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont
    (fun t ht => (hG t ht).scomp_hasDerivWithinAt t (hγ t ht)) hint

/-- **FTC along a contour, `deriv` form.** If `G' = g` along the image of a curve differentiable
in the interior of `[a, b]`, then the contour integral written with `deriv γ` is the endpoint
difference `G (γ b) - G (γ a)`. -/
theorem integral_deriv_smul_comp_eq_sub_of_hasDerivAt
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => deriv γ t • g (γ t)) volume a b) :
    ∫ t in a..b, deriv γ t • g (γ t) = G (γ b) - G (γ a) :=
  integral_smul_comp_eq_sub_of_hasDeriv_right hcont
    (fun t ht => (hγ t ht).hasDerivAt.hasDerivWithinAt) hG hint

/-- A contour integral of an exact derivative vanishes on a closed curve, explicit-velocity form. -/
theorem integral_smul_comp_eq_zero_of_hasDeriv_right_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivWithinAt γ (γ' t) (Set.Ioi t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => γ' t • g (γ t)) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, γ' t • g (γ t) = 0 := by
  rw [integral_smul_comp_eq_sub_of_hasDeriv_right hcont hγ hG hint, hclosed, sub_self]

/-- A contour integral of an exact derivative vanishes on a closed curve, `deriv` form. -/
theorem integral_deriv_smul_comp_eq_zero_of_hasDerivAt_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => deriv γ t • g (γ t)) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • g (γ t) = 0 :=
  integral_smul_comp_eq_zero_of_hasDeriv_right_of_closed hcont
    (fun t ht => (hγ t ht).hasDerivAt.hasDerivWithinAt) hG hint hclosed

/-- **FTC along an absolutely continuous contour.** If `G` is holomorphic on an open set `U` and
`γ` is an absolutely continuous curve in `U`, then the contour integral of `deriv G` along `γ` is
the endpoint difference `G (γ b) - G (γ a)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_sub
    {G : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) :
    ∫ t in a..b, deriv γ t • deriv G (γ t) = G (γ b) - G (γ a) := by
  have hGγ : AbsolutelyContinuousOnInterval (G ∘ γ) a b := by
    refine hγ.comp_of_contDiffAt ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ((hG.contDiffOn hU).contDiffAt (hU.mem_nhds (hγU t ht))).restrict_scalars ℝ
  refine hGγ.integral_eq_sub_of_ae_hasDerivAt ?_
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  have htI := Set.uIoc_subset_uIcc hmem
  exact (hG.differentiableAt (hU.mem_nhds (hγU t htI))).hasDerivAt.scomp t (ht htI).hasDerivAt

/-- The contour integral of `deriv G` vanishes along a closed absolutely continuous curve in an
open set on which `G` is holomorphic. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_zero_of_closed
    {G : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • deriv G (γ t) = 0 := by
  rw [hγ.integral_deriv_smul_deriv_comp_eq_sub hU hG hγU, hclosed, sub_self]

end TauCeti.Contour

end
