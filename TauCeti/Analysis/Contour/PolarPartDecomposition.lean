/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.HomologyCauchy
public import TauCeti.Analysis.Contour.Residue

/-!
# Polar-part decompositions

A **polar-part decomposition** of `f` on `U` at the finite singular set `S`: for each `s ∈ S` an
explicit finite Laurent tail `polarPart s z = ∑ k, coeff s k / (z - s)^(k+1)`, such that `f`
minus the total polar part extends to a function differentiable on all of `U`, and the residue at
each `s` is the first Laurent coefficient. This bundles exactly the data the generalized residue
theorem manipulates: the analytic remainder integrates to zero around any null-homologous closed
curve — even one passing through the poles — so the principal value of `∮ f` reduces to the polar
parts.

## Main definitions

* `Contour.PolarPartDecomposition f S U` — the decomposition data: polar parts, orders, Laurent
  coefficients, the residue identification, and the analytic remainder.

## Main results

* `Contour.PolarPartDecomposition.intervalIntegral_analyticRemainder_eq_zero` — the contour
  integral of the analytic remainder along a closed null-homologous piecewise-`C¹` curve in `U`
  vanishes, by the homology Cauchy theorem.

## Provenance

The structure is migrated from `PolarPartDecomposition` of `HungerbuhlerWasem.lean` in the
AINTLIB `LeanModularForms` development; the remainder-integral theorem is its
`analyticRemainder_contourIntegral_zero`, which there re-runs Dixon's argument inline and here is
a direct application of `Contour.homologyCauchyTheorem`. See K. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory Set

open scoped Interval

/-- **Polar-part decomposition** of `f` on `U` at the finite singular set `S`: explicit finite
Laurent tails at the points of `S` whose removal from `f` leaves a function differentiable on all
of `U`, with the residue at each `s ∈ S` read off as the first Laurent coefficient. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The polar part at each pole, as a function of `z`. -/
  polarPart : ℂ → ℂ → ℂ
  /-- The order of the polar part at each pole (`0` for no pole). -/
  order : ℂ → ℕ
  /-- The Laurent coefficients of the polar part at each pole. -/
  coeff : (s : ℂ) → Fin (order s) → ℂ
  /-- The polar part at `s` is the explicit Laurent sum `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  /-- The residue at `s ∈ S` is the first Laurent coefficient, or zero for an empty polar
  part. -/
  residue_eq : ∀ s ∈ S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  /-- The function `f` minus the total polar part, extended to all of `U`. -/
  analyticRemainder : ℂ → ℂ
  /-- The analytic remainder is differentiable on all of `U`. -/
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  /-- Off the singular set, `f` is the analytic remainder plus the total polar part. -/
  decomp : ∀ z ∈ U \ (↑S : Set ℂ), f z = analyticRemainder z + ∑ s ∈ S, polarPart s z

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The analytic remainder integrates to zero** along any closed null-homologous
piecewise-`C¹` curve in `U` — even one passing through the poles of `f`, since the remainder
extends differentiably to all of `U`. The homology Cauchy theorem applied to the remainder. -/
theorem intervalIntegral_analyticRemainder_eq_zero (decomp : PolarPartDecomposition f S U)
    (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ} (hγ_pc1 : IsPiecewiseC1On γ a b)
    (hγ : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t) = 0 :=
  homologyCauchyTheorem hU γ a b hγ_pc1 hγ hclosed decomp.analyticRemainder_diff hnull

end PolarPartDecomposition

end TauCeti.Contour

end
