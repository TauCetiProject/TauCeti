/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

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

open Filter MeasureTheory Metric Set
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Translation by `-t` on `Lᵖ`, used internally to express convolution without selecting a
pointwise representative. -/
private def subRightContinuousMap (t : E) : C(E, E) :=
  ⟨fun x ↦ x - t, continuous_id.sub continuous_const⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem measurePreserving_subRightContinuousMap (t : E) :
    MeasurePreserving (subRightContinuousMap t) mu mu := by
  simpa only [subRightContinuousMap, ContinuousMap.coe_mk, sub_eq_add_neg] using
    measurePreserving_add_right mu (-t)

private def translateSubLp (t : E) (f : Lp F p mu) : Lp F p mu :=
  Lp.compMeasurePreserving (subRightContinuousMap t)
    (measurePreserving_subRightContinuousMap t) f

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F]
  [Fact (1 ≤ p)] in
private theorem translateSubLp_zero (f : Lp F p mu) :
    translateSubLp (mu := mu) (p := p) 0 f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_subRightContinuousMap (mu := mu) (0 : E))] with x hx
  simpa only [translateSubLp, subRightContinuousMap, ContinuousMap.coe_mk,
    Function.comp_apply, sub_zero] using hx

omit [NormedSpace ℝ F] [CompleteSpace F] in
private theorem continuous_translateSubLp (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun t : E ↦ translateSubLp (mu := mu) (p := p) t f := by
  let T : E → C(E, E) := fun t ↦ ⟨fun x ↦ x - t, continuous_id.sub continuous_const⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T <| by
    dsimp only [T, Function.uncurry_apply_pair, ContinuousMap.coe_mk]
    fun_prop
  have hpres : ∀ t, MeasurePreserving (T t) mu mu := fun t ↦ by
    simpa only [T, subRightContinuousMap] using
      (measurePreserving_subRightContinuousMap (mu := mu) t)
  have h : Continuous (fun t : E ↦ Lp.compMeasurePreserving (T t) (hpres t) f) :=
    (continuous_const : Continuous fun _ : E ↦ f).compMeasurePreservingLp hT hpres hp
  simpa only [translateSubLp, T, subRightContinuousMap] using h

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable. -/
def normedBumpLp (_hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (f : Lp F p mu) : Lp F p mu :=
  ∫ t, phi.normed mu t • translateSubLp (mu := mu) (p := p) t f ∂mu

omit [CompleteSpace F] in
private theorem integrable_normed_smul_translateSubLp (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    Integrable (fun t ↦ phi.normed mu t • translateSubLp (mu := mu) (p := p) t f) mu := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact phi.continuous_normed.smul (continuous_translateSubLp hp f)
  · exact phi.hasCompactSupport_normed.smul_right

omit [CompleteSpace F] in
/-- Averaging against a normalized nonnegative bump does not increase the `Lᵖ` norm. -/
theorem norm_normedBumpLp_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) :
    ‖normedBumpLp hp phi mu f‖ ≤ ‖f‖ := by
  refine (norm_integral_le_of_norm_le (phi.integrable_normed.mul_const ‖f‖) ?_).trans_eq ?_
  · filter_upwards with t
    have ht : ‖translateSubLp (mu := mu) (p := p) t f‖ = ‖f‖ := by
      exact Lp.norm_compMeasurePreserving f (measurePreserving_subRightContinuousMap t)
    rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), ht]
  · rw [integral_mul_const, phi.integral_normed, one_mul]

private theorem norm_normedBumpLp_sub_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) {C : ℝ}
    (htrans : ∀ t ∈ ball (0 : E) phi.rOut,
      ‖translateSubLp (mu := mu) (p := p) t f - f‖ ≤ C) :
    ‖normedBumpLp hp phi mu f - f‖ ≤ C := by
  have havg :
      normedBumpLp hp phi mu f - f =
        ∫ t, phi.normed mu t • (translateSubLp (mu := mu) (p := p) t f - f) ∂mu := by
    calc
      normedBumpLp hp phi mu f - f =
          (∫ t, phi.normed mu t • translateSubLp (mu := mu) (p := p) t f ∂mu) -
            ∫ t, phi.normed mu t • f ∂mu := by
              rw [normedBumpLp, phi.integral_normed_smul]
      _ = ∫ t, (phi.normed mu t • translateSubLp (mu := mu) (p := p) t f) -
          phi.normed mu t • f ∂mu :=
        (integral_sub (integrable_normed_smul_translateSubLp hp phi f)
          (phi.integrable_normed.smul_const f)).symm
      _ = ∫ t, phi.normed mu t •
          (translateSubLp (mu := mu) (p := p) t f - f) ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        rw [smul_sub]
  rw [havg]
  refine (norm_integral_le_of_norm_le (phi.integrable_normed.mul_const C) ?_).trans_eq ?_
  · filter_upwards with t
    rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t)]
    by_cases ht : t ∈ Function.support (phi.normed mu)
    · exact mul_le_mul_of_nonneg_left
        (htrans t (by simpa only [phi.support_normed_eq] using ht))
        (phi.nonneg_normed t)
    · simp [Function.notMem_support.mp ht]
  · rw [integral_mul_const, phi.integral_normed, one_mul]

/-- **Smooth approximate identity in `Lᵖ`.** Let `phi i` be normalized smooth bumps centred at
zero. If their outer radii tend to zero, then averaging any `f ∈ Lᵖ` against these bumps converges
to `f` in the `Lᵖ` norm.

The restriction `p < ∞` is essential: translation is strongly continuous on `Lᵖ` exactly in the
finite-exponent range. No positivity or normalization hypotheses are exposed because they are
already supplied by `ContDiffBump.normed`. -/
theorem tendsto_normedBumpLp {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hcont : Tendsto
      (fun t : E ↦ ‖translateSubLp (mu := mu) (p := p) t f - f‖)
      (nhds 0) (nhds 0) := by
    have hc : Continuous fun t : E ↦ translateSubLp (mu := mu) (p := p) t f - f :=
      (continuous_translateSubLp hp f).sub continuous_const
    simpa only [translateSubLp_zero, sub_self, norm_zero] using hc.norm.tendsto (0 : E)
  have hevent := hcont.eventually (Iio_mem_nhds (half_pos hepsilon))
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨delta, hdelta, hsmall⟩ := hevent
  have hradius : ∀ᶠ i in l, (phi i).rOut < delta :=
    hphi.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hradius] with i hi
  rw [dist_eq_norm]
  refine (norm_normedBumpLp_sub_le hp (phi i) f fun t ht ↦ ?_).trans_lt
    (half_lt_self hepsilon)
  exact (hsmall (by
    simpa only [dist_zero_right] using (mem_ball_zero_iff.mp ht).trans hi)).le

end TauCeti
