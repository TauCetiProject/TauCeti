/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Process.Kolmogorov

import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Kolmogorov bounds from moment and Gaussian increment laws

This file provides constructors for Mathlib's `ProbabilityTheory.IsKolmogorovProcess`:

* `ProbabilityTheory.IsKolmogorovProcess.of_integral_dist_rpow_le` and
  `ProbabilityTheory.IsKolmogorovProcess.of_secondCountableTopology_integral_dist_rpow_le`:
  build `IsKolmogorovProcess` from Bochner `dist`-moment bounds on pseudometric spaces.
* `ProbabilityTheory.isKolmogorovProcess_of_hasLaw_sub_gaussianReal`: a real process whose
  increments have centered Gaussian laws with variance equal to the parameter distance satisfies
  the even-moment Kolmogorov bounds with exponents `2 * n` and `n` and constant `(2 * n - 1)‼` for
  every positive integer `n` (in particular `(4, 2, 3)` for `n = 2`).

These bounds are moment inputs for continuous-modification arguments; they do not themselves
construct a continuous modification.

The Gaussian calculation uses the Gaussian even-moment formula. See Karatzas–Shreve, *Brownian
Motion and Stochastic Calculus*, second edition, Chapter 2, §2.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Nat

namespace ProbabilityTheory

/-- Construct `IsKolmogorovProcess` from Bochner `p`-th moment bounds on `dist`. -/
theorem IsKolmogorovProcess.of_integral_dist_rpow_le {T Ω E : Type*} [PseudoMetricSpace T]
    {_ : MeasurableSpace Ω} [PseudoMetricSpace E] {X : T → Ω → E} {P : Measure Ω}
    {p q : ℝ} {M : ℝ≥0}
    (hpair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω))
    (hint : ∀ s t : T, Integrable (fun ω ↦ dist (X s ω) (X t ω) ^ p) P)
    (hkol : ∀ s t : T, ∫ ω, dist (X s ω) (X t ω) ^ p ∂P ≤ M * dist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M where
  measurablePair := hpair
  p_pos := hp
  q_pos := hq
  kolmogorovCondition s t := by
    have heq (ω : Ω) :
        edist (X s ω) (X t ω) ^ p = ENNReal.ofReal (dist (X s ω) (X t ω) ^ p) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint s t)
      (Filter.Eventually.of_forall fun _ ↦ Real.rpow_nonneg dist_nonneg _)]
    calc ENNReal.ofReal (∫ ω, dist (X s ω) (X t ω) ^ p ∂P)
        ≤ ENNReal.ofReal ((M : ℝ) * dist s t ^ q) := ENNReal.ofReal_le_ofReal (hkol s t)
      _ = M * edist s t ^ q := by
        rw [ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal, edist_dist,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le]

/-- In a second-countable Borel space, coordinatewise measurability and Bochner `p`-th moment
bounds on `dist` imply `IsKolmogorovProcess`. -/
theorem IsKolmogorovProcess.of_secondCountableTopology_integral_dist_rpow_le {T Ω E : Type*}
    [PseudoMetricSpace T] {_ : MeasurableSpace Ω} [PseudoMetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : T → Ω → E} {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
    (hmeas : ∀ t : T, Measurable (X t))
    (hint : ∀ s t : T, Integrable (fun ω ↦ dist (X s ω) (X t ω) ^ p) P)
    (hkol : ∀ s t : T, ∫ ω, dist (X s ω) (X t ω) ^ p ∂P ≤ M * dist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M := by
  refine IsKolmogorovProcess.of_integral_dist_rpow_le (fun s t ↦ ?_) hint hkol hp hq
  rw [← Prod.borelSpace.measurable_eq]
  exact (hmeas s).prodMk (hmeas t)

/-- Centered Gaussian increments with variance `nndist s t` satisfy the Kolmogorov bound
with exponents `2 * n` and `n` and constant `(2 * n - 1)‼` for every positive `n`.
Only coordinate measurability, not joint process measurability or path regularity, is needed. -/
theorem isKolmogorovProcess_of_hasLaw_sub_gaussianReal {T Ω : Type*}
    [PseudoMetricSpace T] [MeasurableSpace Ω] {P : Measure Ω} {X : T → Ω → ℝ}
    (hX : ∀ t, Measurable (X t))
    (h : ∀ s t, HasLaw (fun ω ↦ X s ω - X t ω) (gaussianReal 0 (nndist s t)) P)
    {n : ℕ} (hn : n ≠ 0) :
    IsKolmogorovProcess X P (2 * n : ℕ) n (2 * n - 1)‼ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hX (fun s t ↦ ?_)
    (by positivity) hn'
  have hl := ofReal_integral_eq_lintegral_ofReal
    (TauCeti.integrable_pow_gaussianReal 0 (nndist s t) (2 * n))
    (Filter.Eventually.of_forall (fun x ↦ (even_two_mul n).pow_nonneg x))
  have he : ∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 (nndist s t) =
      (dist s t) ^ n * (2 * n - 1 : ℕ)‼ := by
    simpa using TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 (nndist s t) n
  have hd (x y : ℝ) : edist x y ^ ((2 * n : ℕ) : ℝ) =
      ENNReal.ofReal ((x - y) ^ (2 * n)) := by
    simp only [edist_dist, Real.dist_eq, ENNReal.rpow_natCast]
    rw [← ENNReal.ofReal_pow (abs_nonneg _)]
    congr 1
    rw [← abs_pow, abs_of_nonneg ((even_two_mul n).pow_nonneg _)]
  simp_rw [hd]
  rw [(h s t).lintegral_comp (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 * n))) (by fun_prop),
    ← hl, he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (dist_nonneg)]
  simp [edist_dist, ENNReal.rpow_natCast, mul_comm]

end ProbabilityTheory
