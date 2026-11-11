/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
public import Mathlib.Probability.Process.Kolmogorov

/-!
# Kolmogorov bounds from Gaussian increment laws

A real process whose increments have centered Gaussian laws with variance equal to the
parameter distance satisfies the fourth-moment Kolmogorov bound with exponents 4 and 2
and constant 3. This is the moment input for continuous-modification arguments for Gaussian
processes; it does not itself construct a continuous modification.

The calculation uses the Gaussian fourth-moment formula. See Karatzas–Shreve, *Brownian
Motion and Stochastic Calculus*, second edition, Chapter 2, §2.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Gaussian increments with variance equal to parameter distance satisfy the exact
fourth-moment Kolmogorov bound. Only coordinate measurability, not joint process
measurability or path regularity, is needed. -/
theorem isKolmogorovProcess_of_hasLaw_sub_gaussianReal {T Ω : Type*}
    [PseudoMetricSpace T] [MeasurableSpace Ω] {P : Measure Ω} {X : T → Ω → ℝ}
    (hX : ∀ t, Measurable (X t))
    (h : ∀ s t, HasLaw (fun ω ↦ X s ω - X t ω) (gaussianReal 0 (nndist s t)) P) :
    IsKolmogorovProcess X P 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hX (fun s t ↦ ?_)
    (by norm_num) (by norm_num)
  have hl := ofReal_integral_eq_lintegral_ofReal
    (TauCeti.integrable_pow_gaussianReal 0 (nndist s t) 4)
    (Filter.Eventually.of_forall (fun x ↦ by positivity))
  have he : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (nndist s t) = 3 * (dist s t) ^ 2 := by
    simpa using TauCeti.Probability.integral_sub_pow_four_gaussianReal 0 (nndist s t)
  have hd (x y : ℝ) : edist x y ^ (4 : ℝ) = ENNReal.ofReal ((x - y) ^ 4) := by
    simp only [edist_dist, Real.dist_eq, ENNReal.rpow_ofNat]
    rw [← ENNReal.ofReal_pow (abs_nonneg _)]
    congr 1
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  simp_rw [hd]
  rw [(h s t).lintegral_comp (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ 4)) (by fun_prop),
    ← hl, he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (dist_nonneg)]
  norm_num [edist_dist, ENNReal.rpow_ofNat]

end ProbabilityTheory
