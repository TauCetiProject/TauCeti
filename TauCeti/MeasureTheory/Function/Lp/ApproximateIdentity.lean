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
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- The average of an `Lᵖ` class against the normalized form of a smooth bump centred at zero,
before it is bundled as a continuous linear map by `TauCeti.normedBumpLp`. -/
private def normedBumpFun (phi : ContDiffBump (0 : E)) (f : Lp F p mu) : Lp F p mu :=
  (phi.normed mu ⋆[lsmul ℝ ℝ, mu] fun h ↦ translateLp mu p h f) 0

private theorem normedBumpFun_apply (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpFun phi f = ∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu := by
  rw [normedBumpFun, convolution_lsmul]
  simp only [zero_sub]

private theorem integrable_normed_smul_translateLp_neg (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    Integrable (fun t ↦ phi.normed mu t • translateLp mu p (-t) f) mu := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact phi.continuous_normed.smul ((continuous_translateLp (mu := mu) hp f).comp continuous_neg)
  · exact phi.hasCompactSupport_normed.smul_right

private theorem normedBumpFun_add (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f g : Lp F p mu) :
    normedBumpFun phi (f + g) = normedBumpFun phi f + normedBumpFun phi g := by
  rw [normedBumpFun_apply, normedBumpFun_apply, normedBumpFun_apply,
    ← integral_add (integrable_normed_smul_translateLp_neg hp phi f)
      (integrable_normed_smul_translateLp_neg hp phi g)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_add, smul_add]

private theorem normedBumpFun_smul (c : ℝ) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpFun phi (c • f) = c • normedBumpFun phi f := by
  rw [normedBumpFun_apply, normedBumpFun_apply, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, smul_smul, mul_comm c]

private theorem norm_normedBumpFun_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) :
    ‖normedBumpFun phi f‖ ≤ ‖f‖ := by
  calc
    ‖normedBumpFun phi f‖ ≤
        ∫ t, ‖phi.normed mu t • translateLp mu p (-t) f‖ ∂mu := by
      rw [normedBumpFun_apply]
      exact norm_integral_le_of_norm_le
        (integrable_normed_smul_translateLp_neg hp phi f).norm
        (Eventually.of_forall fun _ ↦ le_rfl)
    _ = ∫ t, phi.normed mu t * ‖f‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      have ht : ‖translateLp mu p (-t) f‖ = ‖f‖ := (translateLp mu p (-t)).norm_map f
      rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), ht]
    _ = ‖f‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero, as a
continuous linear operator on `Lᵖ`.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable; that integrability is what makes the average
additive, and the operator is a contraction by `TauCeti.norm_normedBumpLp_le_one`.

Completeness of `F` is not needed to build the operator or to bound its norm; it is assumed only
where the average has to be a genuine Bochner integral, in `TauCeti.tendsto_normedBumpLp`. -/
def normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] : Lp F p mu →L[ℝ] Lp F p mu :=
  LinearMap.mkContinuous
    { toFun := normedBumpFun phi
      map_add' := normedBumpFun_add hp phi
      map_smul' := fun c f ↦ normedBumpFun_smul c phi f } 1
    fun f ↦ by rw [one_mul]; exact norm_normedBumpFun_le hp phi f

/-- The defining Bochner-integral formula for `normedBumpLp`. -/
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu := by
  rw [normedBumpLp]
  exact normedBumpFun_apply phi f

/-- Averaging against a normalized nonnegative bump does not increase the `Lᵖ` norm when
`p < ∞`. -/
theorem norm_normedBumpLp_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖normedBumpLp (F := F) hp phi mu‖ ≤ 1 := by
  rw [normedBumpLp]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

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
  have hval : ∀ i, normedBumpLp hp (phi i) mu f =
      ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] fun h ↦ translateLp mu p h f) 0 := fun i ↦ by
    rw [normedBumpLp_apply, convolution_lsmul]
    simp only [zero_sub]
  simpa only [hval, translateLp_zero] using
    ContDiffBump.convolution_tendsto_right_of_continuous hphi
      (continuous_translateLp (mu := mu) hp f) (0 : E)

end TauCeti
