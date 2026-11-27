/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Stein.Solution
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Stein's characterization of the standard normal law

A probability measure `μ` on `ℝ` is the standard normal law `γ = gaussianReal 0 1` if and only if
the Stein operator `f ↦ f′(x) - x f(x)` integrates to `0` against `μ` for every continuously
differentiable `f` with compact support.

For `μ = γ` this is Gaussian integration by parts. Conversely, for a continuous compactly
supported `ψ` with `∫ ψ dγ = 0` the Stein solution `f_ψ` is such a test function and satisfies
`f_ψ′(x) - x f_ψ(x) = ψ(x)`, so `∫ ψ dμ = 0`. Hence `∫ ψ dμ` is a fixed multiple of `∫ ψ dγ` for
every continuous compactly supported `ψ`, so `μ` is a multiple of `γ` by the uniqueness part of the
Riesz–Markov–Kakutani theorem, and comparing total masses shows that the multiple is `1`.

Stein's method uses the characterization in the quantitative form of bounds on
`|∫ (f′(x) - x f(x)) dμ(x)|`; the class of test functions here is small, which makes the converse
direction strong.

## Main statements

* `TauCeti.Probability.eq_gaussianReal_iff_integral_stein`: Stein's characterization.

## References

* C. Stein, *A bound for the error in the normal approximation to the distribution of a sum of
  dependent random variables*, Proc. Sixth Berkeley Symp. Math. Statist. Probab. 2 (1972),
  583–602.
* N. Ross, *Fundamentals of Stein's method*, Probability Surveys 8 (2011), 210–293, Lemma 2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported NNReal

namespace TauCeti.Probability

/-- If the Stein operator integrates to `0` against `μ` for every compactly supported `C¹`
function, then so does every continuous compactly supported `ψ` with `∫ ψ dγ = 0`. -/
private theorem integral_eq_zero_of_integral_stein {μ : Measure ℝ}
    (H : ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f → ∫ x, (deriv f x - x * f x) ∂μ = 0)
    {ψ : ℝ → ℝ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (h0 : ∫ x, ψ x ∂gaussianReal 0 1 = 0) :
    ∫ x, ψ x ∂μ = 0 := by
  have hi : Integrable ψ (gaussianReal 0 1) := hc.integrable_of_hasCompactSupport hs
  rw [← H _ (contDiff_steinSolution hi hc) (hasCompactSupport_steinSolution hi hs h0)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [deriv_steinSolution hi hc.continuousAt, h0]
  ring

/-- **Stein's characterization of the standard normal law.** A probability measure `μ` on `ℝ` is
the standard normal law if and only if `∫ (f′(x) - x f(x)) dμ(x) = 0` for every continuously
differentiable `f` with compact support. -/
theorem eq_gaussianReal_iff_integral_stein (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ = gaussianReal 0 1 ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f → ∫ x, (deriv f x - x * f x) ∂μ = 0 := by
  constructor
  · rintro rfl f hf hs
    have hdf : Integrable (deriv f) (gaussianReal 0 1) :=
      (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv
    have hxf : Integrable (fun x => x * f x) (gaussianReal 0 1) :=
      (continuous_id.mul hf.continuous).integrable_of_hasCompactSupport hs.mul_left
    rw [integral_sub hdf hxf, integral_mul_eq_integral_deriv_gaussianReal f
      (hf.differentiable one_ne_zero) hxf hdf, sub_self]
  intro H
  -- A nonnegative bump `ρ` with `∫ ρ dγ > 0`, used to normalize test functions.
  have : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  let ρ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set a := ∫ x, ρ x ∂gaussianReal 0 1
  have ha : 0 < a := ρ.integral_pos
  have hρμ : 0 ≤ ∫ x, ρ x ∂μ := integral_nonneg fun x => ρ.nonneg
  set c : ℝ≥0 := ((∫ x, ρ x ∂μ) / a).toNNReal with hc_def
  -- `∫ ψ dμ = c ∫ ψ dγ` for every continuous compactly supported `ψ`.
  have hμ : μ = c • gaussianReal 0 1 := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun ψ => ?_
    set b := ∫ x, ψ x ∂gaussianReal 0 1
    have hψi : Integrable ψ (gaussianReal 0 1) :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hψμ : Integrable ψ μ :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hφ := integral_eq_zero_of_integral_stein H (ψ := fun x => a * ψ x - b * ρ x)
      ((continuous_const.mul ψ.continuous).sub (continuous_const.mul ρ.continuous))
      (ψ.hasCompactSupport.mul_left.sub ρ.hasCompactSupport.mul_left)
      (by
        rw [integral_sub (hψi.const_mul a) (ρ.integrable.const_mul b), integral_const_mul,
          integral_const_mul]
        ring)
    rw [integral_sub (hψμ.const_mul a) (ρ.integrable.const_mul b), integral_const_mul,
      integral_const_mul, sub_eq_zero] at hφ
    rw [integral_smul_nnreal_measure, hc_def, NNReal.smul_def,
      Real.coe_toNNReal _ (div_nonneg hρμ ha.le), smul_eq_mul]
    field_simp
    linear_combination hφ
  -- Comparing total masses gives `c = 1`.
  have hc1 : c = 1 := by
    have h := congrArg (fun ν : Measure ℝ => ν Set.univ) hμ
    simp only [measure_univ, smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact_mod_cast h.symm
  rw [hμ, hc1, one_smul]

end TauCeti.Probability
