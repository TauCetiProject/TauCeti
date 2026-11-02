/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Powers of an element of spectral radius less than one

In a complex Banach algebra, Gelfand's formula
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` identifies the spectral radius of
`a` with the limit of `‖a ^ n‖ ^ (1 / n)`. So if the spectral radius is less than one, the norms
`‖a ^ n‖` are eventually bounded by a geometric sequence `q ^ n` with `q < 1`, and the powers of
`a` tend to zero.

## Main results

* `spectrum.tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one`: the powers of an element of a
  complex Banach algebra whose spectral radius is less than one tend to zero.
-/

public section

open Filter Topology
open scoped NNReal ENNReal

namespace spectrum

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The powers of an element of a complex Banach algebra whose spectral radius is less than one
tend to zero. -/
theorem tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one {a : A}
    (ha : spectralRadius ℂ a < 1) : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  obtain ⟨q, hρq, hq1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
  have hq : q < 1 := by exact_mod_cast hq1
  -- By Gelfand's formula, `‖a ^ n‖ ^ (1 / n) < q`, that is `‖a ^ n‖ < q ^ n`, for large `n`.
  have hev : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ (q : ℝ) ^ n := by
    filter_upwards [(pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
      (gt_mem_nhds hρq), eventually_gt_atTop 0] with n hn hn0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [one_div, ENNReal.rpow_inv_lt_iff hn0', ENNReal.rpow_natCast] at hn
    exact_mod_cast hn.le
  exact squeeze_zero_norm' hev (tendsto_pow_atTop_nhds_zero_of_lt_one q.coe_nonneg hq)

end spectrum
