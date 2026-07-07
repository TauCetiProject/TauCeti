/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.CauchyPrincipalValue

/-!
# The generalized winding number (Hungerbühler–Wasem Def 2.1)

For a curve `γ : ℝ → ℂ` on `[a, b]` and a point `z₀`, the **generalized winding number**
`windingNumber γ a b z₀` is the principal-value normalization of the index integral
`(2πi)⁻¹ · PV ∮_γ dz/(z − z₀)` (Hungerbühler–Wasem Def 2.1); see
`windingNumber_eq_integral_of_avoidance` for its reduction to the ordinary index integral under the
hypotheses stated there. As an unconditional `limUnder`-based value it is junk when the principal
value does not exist.

## Main definitions

* `TauCeti.Contour.windingNumber` — the generalized winding number.
* `TauCeti.Contour.IsNullHomologous` — a curve whose winding number vanishes outside a set `Ω`.

## Main results

* `TauCeti.Contour.windingNumber_eq_cauchyPVAt` — characteristic value lemma for the raw
  `cauchyPVAt` defining value.
* `TauCeti.Contour.windingNumber_eq_of_hasCauchyPVAt` — evaluate `windingNumber` from a Cauchy
  principal-value witness, without unfolding the definition.
* `TauCeti.Contour.isNullHomologous_iff` — restates `IsNullHomologous` as its vanishing condition,
  so consumers use the predicate without unfolding its hidden body.
* `TauCeti.Contour.windingNumber_eq_integral_of_avoidance` — reduces `windingNumber` to the ordinary
  index integral `(2πi)⁻¹ · ∮_γ dz/(z − z₀)` under the continuity, avoidance, and integrability
  hypotheses stated there.

This is Layer 0 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project, file
`ForMathlib/GeneralizedWindingNumber.lean`, specialised to the raw-function
(`γ : ℝ → ℂ` on `[a, b]`) design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **Generalized winding number** (HW Def 2.1): `n_{z₀}(γ) = (2πi)⁻¹ · PV ∮_γ dz/(z − z₀)`, the
principal-value normalization of the index integral for a curve `γ : ℝ → ℂ` on `[a, b]` and any
point `z₀`. See `windingNumber_eq_integral_of_avoidance` for its reduction to the ordinary index
integral; as a `limUnder`-based value it is junk when the principal value does not exist. -/
@[expose]
def windingNumber (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀

/-- **Characteristic value lemma.** The generalized winding number is the normalized raw
single-point principal-value value. This is the public, module-safe form of the definition for
value-level rewrites. -/
theorem windingNumber_eq_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    windingNumber γ a b z₀ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ :=
  rfl

/-- **Characteristic value lemma.** From a Cauchy principal-value witness for `(· − z₀)⁻¹` along
`γ`, the generalized winding number is the normalized value `(2πi)⁻¹ · L`. This evaluates
`windingNumber` through the `HasCauchyPVAt` predicate without unfolding the definition. -/
theorem windingNumber_eq_of_hasCauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ L) :
    windingNumber γ a b z₀ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L := by
  rw [windingNumber_eq_cauchyPVAt, h.cauchyPVAt_eq]

/-- A curve `γ` on `[a, b]` is **null-homologous** in `Ω` when its generalized winding number
about every point outside `Ω` vanishes — the hypothesis of the homology form of Cauchy's theorem
and of the Hungerbühler–Wasem residue theorem (HW Thm 3.3). -/
def IsNullHomologous (γ : ℝ → ℂ) (a b : ℝ) (Ω : Set ℂ) : Prop :=
  ∀ w ∉ Ω, windingNumber γ a b w = 0

/-- Restatement of `IsNullHomologous` as its defining vanishing condition, so consumers can use the
predicate without unfolding its hidden body. -/
theorem isNullHomologous_iff {γ : ℝ → ℂ} {a b : ℝ} {Ω : Set ℂ} :
    IsNullHomologous γ a b Ω ↔ ∀ w ∉ Ω, windingNumber γ a b w = 0 :=
  Iff.rfl

/-- If `γ` is continuous on `[a, b]`, avoids `z₀` there, and the index integrand is
interval-integrable, the generalized winding number is the ordinary index integral: the principal
value collapses to `(2πi)⁻¹ · ∮_γ dz/(z − z₀)`. -/
theorem windingNumber_eq_integral_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => (γ t - z₀)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    windingNumber γ a b z₀
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t :=
  windingNumber_eq_of_hasCauchyPVAt (HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int)

end TauCeti.Contour

end
