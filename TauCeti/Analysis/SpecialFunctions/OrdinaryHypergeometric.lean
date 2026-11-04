/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# The ordinary hypergeometric function on the unit ball

Mathlib computes the radius of convergence of the series of `₂F₁(a, b; c; ·)`: it is `1`, unless
one of the parameters is a nonpositive integer, in which case the series is finite or its
coefficients take the junk value `0`, and the radius is `⊤`. This file records the uniform
consequence that the radius is always at least `1`, so `₂F₁(a, b; c; ·)` is analytic on the open
unit ball for all parameters.

## Main statements

* `TauCeti.one_le_radius_ordinaryHypergeometricSeries`: the radius of convergence of
  `ordinaryHypergeometricSeries 𝔸 a b c` is at least `1`.
* `TauCeti.analyticOnNhd_ordinaryHypergeometric`: `₂F₁ a b c` is analytic on the open unit ball.
-/

public section

namespace TauCeti

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The radius of convergence of the hypergeometric series `₂F₁(a, b; c; ·)` is at least `1`, for
all parameters. -/
theorem one_le_radius_ordinaryHypergeometricSeries (a b c : 𝕂) :
    1 ≤ (ordinaryHypergeometricSeries 𝔸 a b c).radius := by
  by_cases h : ∀ k : ℕ, (k : 𝕂) ≠ -a ∧ (k : 𝕂) ≠ -b ∧ (k : 𝕂) ≠ -c
  · exact (ordinaryHypergeometricSeries_radius_eq_one 𝔸 a b c h).ge
  · push Not at h
    obtain ⟨k, hk⟩ := h
    by_cases ha : (k : 𝕂) = -a
    · have ha' : a = -(k : 𝕂) := by rw [ha, neg_neg]
      rw [ha', ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    by_cases hb : (k : 𝕂) = -b
    · have hb' : b = -(k : 𝕂) := by rw [hb, neg_neg]
      rw [hb', ordinaryHypergeometric_radius_top_of_neg_nat₂]
      exact le_top
    · have hc : c = -(k : 𝕂) := by rw [hk ha hb, neg_neg]
      rw [hc, ordinaryHypergeometric_radius_top_of_neg_nat₃]
      exact le_top

/-- The ordinary hypergeometric function `₂F₁(a, b; c; ·)` is analytic on the open unit ball, for
all parameters. -/
theorem analyticOnNhd_ordinaryHypergeometric [CompleteSpace 𝔸] (a b c : 𝕂) :
    AnalyticOnNhd 𝕂 (₂F₁ a b c : 𝔸 → 𝔸) (Metric.ball 0 1) := by
  intro x hx
  have h1 := one_le_radius_ordinaryHypergeometricSeries 𝔸 a b c
  exact ((ordinaryHypergeometricSeries 𝔸 a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le h1)).analyticAt_of_mem
      (Metric.eball_subset_eball h1 (by
        simpa only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, Metric.mem_ball] using hx))

end TauCeti
