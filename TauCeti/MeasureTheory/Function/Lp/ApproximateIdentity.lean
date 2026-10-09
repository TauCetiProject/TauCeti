/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Average
public import TauCeti.MeasureTheory.Function.Lp.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Smooth approximate identities in `Lᵖ`

Let `φ` be a smooth bump function centred at the origin and normalized to have integral one.
This file defines the corresponding averaging operator on `Lᵖ` by the Bochner integral

`f ↦ ∫ t, φ(t) f(· - t)`

as a continuous linear map of norm at most one, and proves that these operators converge strongly
to the identity when the outer radii of the bumps tend to zero.  The result holds for `1 ≤ p < ∞`,
for functions with values in an arbitrary real Banach space, and for every additive Haar measure
on a finite-dimensional real normed space.

The integral is taken directly in `Lᵖ`.  This avoids choosing pointwise representatives: translation
is continuous in `Lᵖ`, so the average is a Bochner integral of a continuous compactly supported
`Lᵖ`-valued function.  The proof is the standard approximate-identity estimate

`‖∫ φ(t) (f(· - t) - f) dt‖ₚ ≤ sup_{t ∈ supp φ} ‖f(· - t) - f‖ₚ`.

This is the `Lᵖ` convergence input for mollification in Sobolev spaces.  Together with commutation
of mollification and weak differentiation, it approximates both the value and every weak derivative
by the same smooth kernel.

## Main declarations

* `TauCeti.normedBumpLp`: averaging an `Lᵖ` function against a normalized smooth bump, as a
  continuous linear operator on `Lᵖ`.
* `TauCeti.normedBumpLp_apply`: the defining Bochner integral of that operator.
* `TauCeti.normedBumpLp_eq_normedBumpAverageL`: this operator is the normalized-bump average of
  the `Lᵖ` translation action.
* `TauCeti.normedBumpLp_eq_convolutionLp`: this operator is convolution with the normalized bump.
* `TauCeti.compLpL_normedBumpLp`: this operator commutes with postcomposition by a continuous
  linear map.
* `TauCeti.norm_normedBumpLp_le_one`: this averaging operator is an `Lᵖ` contraction.
* `TauCeti.tendsto_normedBumpLp`: normalized bumps whose radii shrink to zero converge strongly
  to the identity on `Lᵖ`.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Proposition 4.21.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero, as a
continuous linear operator on `Lᵖ`.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable; that integrability is what makes the average
additive, and the operator is a contraction by `TauCeti.norm_normedBumpLp_le_one`.

Completeness of `F` is not part of the definition, exactly as for `MeasureTheory.average` and
`convolution`: the Bochner integral is formed in whatever normed space is at hand, and it is `0`
unless that space is complete. So this operator is the advertised average of the translates of
its argument precisely when `F` is a Banach space, which is the setting of
`TauCeti.tendsto_normedBumpLp`; the contraction bound holds in either case. -/
def normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] : Lp F p mu →L[ℝ] Lp F p mu :=
  normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp)

/-- The defining Bochner-integral formula for `normedBumpLp`. -/
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • mu.translateLp p (-t) f ∂mu := by
  exact normedBumpAverageL_apply (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp) f

/-- `normedBumpLp` is the normalized-bump average of the `Lᵖ` translation action. -/
theorem normedBumpLp_eq_normedBumpAverageL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpLp (F := F) hp phi mu =
      normedBumpAverageL phi mu (mu.translateLp p) (Measure.continuous_translateLp hp) :=
  (rfl)

/-- Averaging against a normalized bump is convolution with the normalized bump, as an operator
on `Lᵖ`. -/
theorem normedBumpLp_eq_convolutionLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpLp (F := F) hp phi mu = convolutionLp hp (phi.normed mu) mu := by
  ext1 f
  rw [normedBumpLp_apply, convolutionLp_apply hp phi.integrable_normed]

/-- Averaging against a normalized bump commutes with postcomposition by a continuous linear map
between Banach spaces. -/
theorem compLpL_normedBumpLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G] (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (L : F →L[ℝ] G) (f : Lp F p mu) :
    L.compLpL p mu (normedBumpLp hp phi mu f) = normedBumpLp hp phi mu (L.compLpL p mu f) :=
  normedBumpAverageL_comm _ _ _ _ _ _ _ (Measure.compLpL_translateLp L) f

/-- Averaging against a normalized nonnegative bump does not increase the `Lᵖ` norm when
`p < ∞`. -/
theorem norm_normedBumpLp_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖normedBumpLp (F := F) hp phi mu‖ ≤ 1 := by
  exact norm_normedBumpAverageL_le_one (F := Lp F p mu) phi mu (mu.translateLp p)
    (Measure.continuous_translateLp hp)

/-- **Smooth approximate identity in `Lᵖ`.** Let `phi i` be normalized smooth bumps centred at
zero. If their outer radii tend to zero, then averaging any `f ∈ Lᵖ` against these bumps converges
to `f` in the `Lᵖ` norm.

The hypothesis `p < ∞` is used to obtain strong translation continuity in this general setting, and
`F` is assumed complete so that the `Lᵖ`-valued Bochner integral defining the average is the limit
of its approximating sums. No positivity or normalization hypotheses are exposed because they are
already supplied by `ContDiffBump.normed`. -/
theorem tendsto_normedBumpLp [CompleteSpace F] {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  simpa only [normedBumpLp, Measure.translateLp_zero] using
    tendsto_normedBumpAverageL (F := Lp F p mu) hphi mu (mu.translateLp p)
      (Measure.continuous_translateLp hp) f

end TauCeti
