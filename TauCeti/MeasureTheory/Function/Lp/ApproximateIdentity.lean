/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Smooth approximate identities in `Lᵖ`

Let `φ` be a smooth bump function centred at the origin and normalized to have integral one.
This file defines the corresponding averaging operator on `Lᵖ` by the Bochner integral

`f ↦ ∫ t, φ(t) f(· - t)`

and proves that these operators converge strongly to the identity when the outer radii of the
bumps tend to zero.  The result holds for `1 ≤ p < ∞`, for functions with values in an arbitrary
real Banach space, and for every additive Haar measure on a finite-dimensional real normed space.

The integral is taken directly in `Lᵖ`.  This avoids choosing pointwise representatives: translation
is continuous in `Lᵖ`, so the average is a Bochner integral of a continuous compactly supported
`Lᵖ`-valued function.  The proof is the standard approximate-identity estimate

`‖∫ φ(t) (f(· - t) - f) dt‖ₚ ≤ sup_{t ∈ supp φ} ‖f(· - t) - f‖ₚ`.

This is the `Lᵖ` convergence input for mollification in Sobolev spaces.  Together with commutation
of mollification and weak differentiation, it approximates both the value and every weak derivative
by the same smooth kernel.

## Main declarations

* `TauCeti.normedBumpLp`: averaging an `Lᵖ` function against a normalized smooth bump.
* `TauCeti.norm_normedBumpLp_le`: this averaging operation is an `Lᵖ` contraction.
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
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable. -/
def normedBumpLp (_hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (f : Lp F p mu) : Lp F p mu :=
  (phi.normed mu ⋆[lsmul ℝ ℝ, mu] fun h ↦ translateLp mu p h f) 0

omit [CompleteSpace F] in
/-- The defining Bochner-integral formula for `normedBumpLp`. -/
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu := by
  rw [normedBumpLp, convolution_lsmul]
  simp only [zero_sub]

omit [CompleteSpace F] in
private theorem integrable_normed_smul_translateLp_neg (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    Integrable (fun t ↦ phi.normed mu t • translateLp mu p (-t) f) mu := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact phi.continuous_normed.smul ((continuous_translateLp (mu := mu) hp f).comp continuous_neg)
  · exact phi.hasCompactSupport_normed.smul_right

omit [CompleteSpace F] in
/-- Averaging against a normalized nonnegative bump does not increase the `Lᵖ` norm when
`p < ∞`. -/
theorem norm_normedBumpLp_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) :
    ‖normedBumpLp hp phi mu f‖ ≤ ‖f‖ := by
  calc
    ‖normedBumpLp hp phi mu f‖ ≤
        ∫ t, ‖phi.normed mu t • translateLp mu p (-t) f‖ ∂mu := by
      rw [normedBumpLp_apply]
      exact norm_integral_le_of_norm_le
        (integrable_normed_smul_translateLp_neg hp phi f).norm
        (Eventually.of_forall fun _ ↦ le_rfl)
    _ = ∫ t, phi.normed mu t * ‖f‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      have ht : ‖translateLp mu p (-t) f‖ = ‖f‖ := (translateLp mu p (-t)).norm_map f
      rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), ht]
    _ = ‖f‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

omit [CompleteSpace F] in
/-- `normedBumpLp` preserves addition when `p < ∞`. -/
@[simp]
theorem normedBumpLp_add (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f g : Lp F p mu) :
    normedBumpLp hp phi mu (f + g) =
      normedBumpLp hp phi mu f + normedBumpLp hp phi mu g := by
  rw [normedBumpLp_apply, normedBumpLp_apply, normedBumpLp_apply,
    ← integral_add (integrable_normed_smul_translateLp_neg hp phi f)
      (integrable_normed_smul_translateLp_neg hp phi g)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_add, smul_add]

omit [CompleteSpace F] in
/-- `normedBumpLp` commutes with real scalar multiplication when `p < ∞`. -/
@[simp]
theorem normedBumpLp_smul (hp : p ≠ ∞) (c : ℝ) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) :
    normedBumpLp hp phi mu (c • f) = c • normedBumpLp hp phi mu f := by
  rw [normedBumpLp_apply, normedBumpLp_apply, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, smul_smul, mul_comm c]

/-- **Smooth approximate identity in `Lᵖ`.** Let `phi i` be normalized smooth bumps centred at
zero. If their outer radii tend to zero, then averaging any `f ∈ Lᵖ` against these bumps converges
to `f` in the `Lᵖ` norm.

The hypothesis `p < ∞` is used to obtain strong translation continuity in this general setting.
No positivity or normalization hypotheses are exposed because they are already supplied by
`ContDiffBump.normed`. -/
theorem tendsto_normedBumpLp {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  simpa only [normedBumpLp, translateLp_zero] using
    ContDiffBump.convolution_tendsto_right_of_continuous hphi
      (continuous_translateLp (mu := mu) hp f) (0 : E)

end TauCeti
