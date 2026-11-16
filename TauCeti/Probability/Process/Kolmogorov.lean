/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Kolmogorov bounds from Gaussian increment laws

A real process whose increments have centered Gaussian laws with variance equal to the
parameter distance satisfies the even-moment Kolmogorov bounds with exponents `2 * n` and `n`
and constant `(2 * n - 1)‼` for every positive integer `n`. In particular, `n = 2` gives
exponents 4 and 2 and constant 3. These bounds are moment inputs for continuous-modification
arguments; they do not themselves construct a continuous modification.

The calculation uses the Gaussian even-moment formula. See Karatzas–Shreve, *Brownian
Motion and Stochastic Calculus*, second edition, Chapter 2, §2.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Nat

namespace ProbabilityTheory

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
