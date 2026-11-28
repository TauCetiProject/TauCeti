/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Descent of `L²` boosting

In a real inner product space, let `r` be a residual and `h ≠ 0` a base learner whose absolute
correlation with `r` is at least `γ ≥ 0`, that is `γ ‖r‖ ‖h‖ ≤ |⟪r, h⟫|`. The least-squares
coefficient of `r` on `h` is `⟪r, h⟫ / ‖h‖²`, and the step with shrinkage `ν ∈ [0, 2]` replaces
`r` by `r - ν (⟪r, h⟫ / ‖h‖²) h`. The identity
`‖r - ν (⟪r, h⟫ / ‖h‖²) h‖² = ‖r‖² - ν (2 - ν) ⟪r, h⟫² / ‖h‖²` and the inequality
`⟪r, h⟫² ≥ γ² ‖r‖² ‖h‖²` give the bound `‖r'‖² ≤ (1 - ν (2 - ν) γ²) ‖r‖²`. The factor
`1 - ν (2 - ν) γ²` is at most `1`, and less than `1` when `0 < γ` and `0 < ν < 2`. Along an
iteration of such steps, `‖r m‖²` is at most the `m`-th power of this factor times `‖r 0‖²`.

When `r m = f* - f m` in `L²` of the law of the features, with `f m` the current fit of a target
`f*`, this is the descent of gradient boosting for the squared loss.

## Main results

* `TauCeti.boosting_descent_step`: one shrunken least-squares step multiplies the squared norm of
  the residual by at most the factor `1 - ν (2 - ν) γ²`.
* `TauCeti.boosting_descent`: along the iteration, each step multiplies the squared residual by
  at most this factor, and hence `‖r m‖² ≤ (1 - ν (2 - ν) γ²) ^ m ‖r 0‖²`.

## References

* P. Bühlmann and B. Yu, *Boosting with the `L₂` loss: regression and classification*,
  J. Amer. Statist. Assoc. 98 (2003), 324–339.
* J. H. Friedman, *Greedy function approximation: a gradient boosting machine*, Ann. Statist. 29
  (2001), 1189–1232.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **One step of `L²` boosting.** If the base learner `h ≠ 0` has absolute correlation at least
`γ ≥ 0` with the residual `r`, that is `γ ‖r‖ ‖h‖ ≤ |⟪r, h⟫|`, then the shrunken least-squares step
`r - ν (⟪r, h⟫ / ‖h‖²) h` with `0 ≤ ν ≤ 2` has squared norm at most
`(1 - ν (2 - ν) γ²) ‖r‖²`. The factor is at most `1`, and less than `1` when `0 < γ` and
`0 < ν < 2`. -/
theorem boosting_descent_step {r h : E} {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hν2 : ν ≤ 2)
    (hcorr : γ * ‖r‖ * ‖h‖ ≤ |⟪r, h⟫_ℝ|) (hh : h ≠ 0) :
    ‖r - (ν * (⟪r, h⟫_ℝ / ‖h‖ ^ 2)) • h‖ ^ 2 ≤ (1 - ν * (2 - ν) * γ ^ 2) * ‖r‖ ^ 2 := by
  have hn : 0 < ‖h‖ ^ 2 := by positivity
  -- The squared norm of the step is `‖r‖² - ν (2 - ν) ⟪r, h⟫² / ‖h‖²`.
  have hid : ‖r - (ν * (⟪r, h⟫_ℝ / ‖h‖ ^ 2)) • h‖ ^ 2 =
      ‖r‖ ^ 2 - ν * (2 - ν) * ⟪r, h⟫_ℝ ^ 2 / ‖h‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  -- Squaring the correlation bound gives `γ² ‖r‖² ‖h‖² ≤ ⟪r, h⟫²`.
  have hsq : γ ^ 2 * ‖r‖ ^ 2 * ‖h‖ ^ 2 ≤ ⟪r, h⟫_ℝ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hcorr 2
    rw [sq_abs] at this
    linarith [show (γ * ‖r‖ * ‖h‖) ^ 2 = γ ^ 2 * ‖r‖ ^ 2 * ‖h‖ ^ 2 by ring]
  have hdiv : ν * (2 - ν) * γ ^ 2 * ‖r‖ ^ 2 ≤ ν * (2 - ν) * ⟪r, h⟫_ℝ ^ 2 / ‖h‖ ^ 2 := by
    rw [le_div_iff₀ hn]
    linarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hν (sub_nonneg.2 hν2))]
  rw [hid]
  linarith

/-- **Descent of `L²` boosting.** Let the residuals `r m` and the base learners `h m ≠ 0` satisfy
the correlation bound `γ ‖r m‖ ‖h m‖ ≤ |⟪r m, h m⟫|` for a fixed `γ ≥ 0`, and the shrunken
least-squares step `r (m + 1) = r m - ν (⟪r m, h m⟫ / ‖h m‖²) h m` with `0 ≤ ν ≤ 2`. Then each step
multiplies the squared residual by at most the factor `1 - ν (2 - ν) γ²`, and
`‖r m‖² ≤ (1 - ν (2 - ν) γ²) ^ m ‖r 0‖²`. The factor is at most `1`, and less than `1` when
`0 < γ` and `0 < ν < 2`. -/
theorem boosting_descent (r h : ℕ → E) {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hν2 : ν ≤ 2)
    (hcorr : ∀ m, γ * ‖r m‖ * ‖h m‖ ≤ |⟪r m, h m⟫_ℝ|) (hh : ∀ m, h m ≠ 0)
    (hstep : ∀ m, r (m + 1) = r m - (ν * (⟪r m, h m⟫_ℝ / ‖h m‖ ^ 2)) • h m) :
    (∀ m, ‖r (m + 1)‖ ^ 2 ≤ (1 - ν * (2 - ν) * γ ^ 2) * ‖r m‖ ^ 2) ∧
      ∀ m, ‖r m‖ ^ 2 ≤ (1 - ν * (2 - ν) * γ ^ 2) ^ m * ‖r 0‖ ^ 2 := by
  have hone : ∀ m, ‖r (m + 1)‖ ^ 2 ≤ (1 - ν * (2 - ν) * γ ^ 2) * ‖r m‖ ^ 2 := fun m ↦ by
    rw [hstep m]
    exact boosting_descent_step hγ hν hν2 (hcorr m) (hh m)
  refine ⟨hone, ?_⟩
  by_cases h0 : r 0 = 0
  · -- A zero residual stays zero, so both sides vanish.
    have hzero : ∀ m, r m = 0 := fun m ↦ by
      induction m with
      | zero => exact h0
      | succ m ih => rw [hstep m, ih]; simp
    simp [hzero]
  · -- A nonzero initial residual forces the contraction factor to be nonnegative.
    have hpos : 0 < ‖r 0‖ ^ 2 := by positivity
    have hq : 0 ≤ 1 - ν * (2 - ν) * γ ^ 2 :=
      (mul_nonneg_iff_of_pos_right hpos).mp ((sq_nonneg _).trans (hone 0))
    exact fun m ↦ (monotone_mul_left_of_nonneg hq).seq_le_seq
      (x := fun n ↦ ‖r n‖ ^ 2) (y := fun n ↦ (1 - ν * (2 - ν) * γ ^ 2) ^ n * ‖r 0‖ ^ 2) m
      (by simp) (fun k _ ↦ hone k)
      (fun k _ ↦ by simp [pow_succ', mul_assoc])

end TauCeti
