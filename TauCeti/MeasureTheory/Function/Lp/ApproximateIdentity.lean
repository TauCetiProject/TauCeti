/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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

open Filter MeasureTheory Metric Set
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

/-- Averaging an `Lᵖ` function against the normalized form of a smooth bump centred at zero.

The average is a Bochner integral in `Lᵖ`, so it is independent of all choices of pointwise
representative. The restriction `p < ∞` ensures that translation is strongly continuous, hence
that the `Lᵖ`-valued integrand is integrable. -/
@[expose]
def normedBumpLp (_hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (f : Lp F p mu) : Lp F p mu :=
  ∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu

omit [CompleteSpace F] in
/-- The defining Bochner-integral formula for `normedBumpLp`. -/
theorem normedBumpLp_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (f : Lp F p mu) :
    normedBumpLp hp phi mu f =
      ∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu := rfl

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
      rw [normedBumpLp]
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
  rw [normedBumpLp, normedBumpLp, normedBumpLp,
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
  rw [normedBumpLp, normedBumpLp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, smul_smul, mul_comm c]

private theorem norm_normedBumpLp_sub_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p mu) {C : ℝ}
    (htrans : ∀ t ∈ ball (0 : E) phi.rOut,
      ‖translateLp mu p (-t) f - f‖ ≤ C) :
    ‖normedBumpLp hp phi mu f - f‖ ≤ C := by
  have havg :
      normedBumpLp hp phi mu f - f =
        ∫ t, phi.normed mu t • (translateLp mu p (-t) f - f) ∂mu := by
    calc
      normedBumpLp hp phi mu f - f =
          (∫ t, phi.normed mu t • translateLp mu p (-t) f ∂mu) -
            ∫ t, phi.normed mu t • f ∂mu := by
              rw [normedBumpLp, phi.integral_normed_smul]
      _ = ∫ t, (phi.normed mu t • translateLp mu p (-t) f) -
          phi.normed mu t • f ∂mu :=
        (integral_sub (integrable_normed_smul_translateLp_neg hp phi f)
          (phi.integrable_normed.smul_const f)).symm
      _ = ∫ t, phi.normed mu t •
          (translateLp mu p (-t) f - f) ∂mu := by
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

The hypothesis `p < ∞` is used to obtain strong translation continuity in this general setting.
No positivity or normalization hypotheses are exposed because they are already supplied by
`ContDiffBump.normed`. -/
theorem tendsto_normedBumpLp {I : Type*} {l : Filter I}
    (hp : p ≠ ∞) {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0)) (f : Lp F p mu) :
    Tendsto (fun i ↦ normedBumpLp hp (phi i) mu f) l (nhds f) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hcont : Tendsto
      (fun t : E ↦ ‖translateLp mu p (-t) f - f‖)
      (nhds 0) (nhds 0) := by
    have hc : Continuous fun t : E ↦ translateLp mu p (-t) f - f :=
      ((continuous_translateLp (mu := mu) hp f).comp continuous_neg).sub continuous_const
    simpa only [neg_zero, translateLp_zero, sub_self, norm_zero] using hc.norm.tendsto (0 : E)
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
