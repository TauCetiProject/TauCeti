/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Global error bounds from a modulus of continuity

Let `g` be a function from a pseudometric space to a normed group, bounded in norm by `M`, which
moves by less than `η` over distances less than `δ` (the shape of
`Metric.uniformContinuous_iff`). Then `‖g a - g b‖ ≤ η + 2 M min(1, dist a b / δ)` for all `a`
and `b`. The second term is a continuous function of `dist a b` vanishing at `0`, which makes
this the standard pointwise input of approximate-identity arguments: integrating it against a
kernel concentrating at the origin leaves only `η`.

The weighted variant bounds `‖c • g a - g b‖` for a real scalar `|c| ≤ H`, adding the cost
`M |c - 1|` of the weight differing from one.

## Main declarations

* `TauCeti.norm_sub_le_add_mul_min_dist_div`: the modulus-of-continuity bound.
* `TauCeti.norm_smul_sub_le_add_mul_min_dist_div`: its weighted variant.
-/

public section

namespace TauCeti

variable {X E : Type*} [PseudoMetricSpace X]

/-- A function bounded in norm by `M` which moves by less than `η` over distances less than `δ`
satisfies `‖g a - g b‖ ≤ η + 2 M min(1, dist a b / δ)` for all `a` and `b`. -/
theorem norm_sub_le_add_mul_min_dist_div [SeminormedAddCommGroup E] {g : X → E} {M : ℝ}
    (hgM : ∀ x, ‖g x‖ ≤ M) {δ η : ℝ} (hδ : 0 < δ)
    (hgδ : ∀ ⦃a b : X⦄, dist a b < δ → dist (g a) (g b) < η) (a b : X) :
    ‖g a - g b‖ ≤ η + 2 * M * min 1 (dist a b / δ) := by
  by_cases hab : dist a b < δ
  · have hM : 0 ≤ M := (norm_nonneg _).trans (hgM a)
    have : 0 ≤ min 1 (dist a b / δ) := le_min zero_le_one (by positivity)
    have := hgδ hab
    rw [dist_eq_norm] at this
    nlinarith
  · rw [min_eq_left ((one_le_div hδ).2 (not_lt.1 hab))]
    -- `η` is positive, as `g` moves by less than `η` from `b` to itself.
    have hη : 0 < η := by simpa using hgδ (a := b) (b := b) (by simpa using hδ)
    linarith [norm_sub_le (g a) (g b), hgM a, hgM b]

/-- The weighted form of `norm_sub_le_add_mul_min_dist_div`: for a real scalar `c` with
`|c| ≤ H`, `‖c • g a - g b‖ ≤ H η + (2 H M min(1, dist a b / δ) + M |c - 1|)`. -/
theorem norm_smul_sub_le_add_mul_min_dist_div [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {g : X → E} {M : ℝ} (hgM : ∀ x, ‖g x‖ ≤ M) {δ η : ℝ} (hδ : 0 < δ)
    (hgδ : ∀ ⦃a b : X⦄, dist a b < δ → dist (g a) (g b) < η) {c H : ℝ} (hcH : |c| ≤ H)
    (a b : X) :
    ‖c • g a - g b‖ ≤ H * η + (2 * H * M * min 1 (dist a b / δ) + M * |c - 1|) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hcH
  have hsplit : c • g a - g b = c • (g a - g b) + (c - 1) • g b := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |c| * ‖g a - g b‖ ≤ H * (η + 2 * M * min 1 (dist a b / δ)) :=
    mul_le_mul hcH (norm_sub_le_add_mul_min_dist_div hgM hδ hgδ a b) (norm_nonneg _) hH
  have h2 : |c - 1| * ‖g b‖ ≤ M * |c - 1| := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hgM b) (abs_nonneg _)
  nlinarith

end TauCeti
