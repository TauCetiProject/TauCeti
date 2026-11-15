/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax

/-!
# Relative maximum-modulus bounds on a disc

Two consequences of the maximum modulus principle for a function `f` that is differentiable on
`ball z₀ R` and continuous on its closure, under a bound on `sphere z₀ R` relative to the value
at the centre:

* if `‖f w‖ ≤ M ‖f z₀‖` on the sphere and `f z₀ ≠ 0`, then `1 ≤ M`;
* if `‖P w * G w‖ ≤ M ‖P z₀ * G z₀‖` on the sphere, where `P` is nonzero there and at least as
  large as at the centre, then `‖G w‖ ≤ M ‖G z₀‖` on the closed disc.

The second removes a factor `P` that is no smaller on the boundary than at the centre, such as a
product of linear factors over zeros near `z₀`.

## Main results

* `DiffContOnCl.one_le_of_forall_mem_sphere_norm_le_mul`
* `Complex.norm_le_of_forall_mem_sphere_norm_mul_le`
-/

public section

open Metric Set

variable {z₀ : ℂ} {R M : ℝ}

/-- If `f` is differentiable on `ball z₀ R` and continuous on its closure, with `0 < R`,
`f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, then `1 ≤ M`. -/
theorem DiffContOnCl.one_le_of_forall_mem_sphere_norm_le_mul {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball z₀ R)) (hR : 0 < R) (hz₀ : f z₀ ≠ 0)
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) : 1 ≤ M := by
  have := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
    (by rwa [frontier_ball z₀ hR.ne'])
    (by rw [closure_ball z₀ hR.ne']; exact mem_closedBall_self hR.le)
  rwa [le_mul_iff_one_le_left (norm_pos_iff.2 hz₀)] at this

/-- **Maximum modulus for a cofactor.** Let `G` be differentiable on `ball z₀ R` and continuous on
its closure, with `0 < R`, and let `P` be nonzero on `sphere z₀ R` with `‖P z₀‖ ≤ ‖P w‖` there.
If `‖P w * G w‖ ≤ M ‖P z₀ * G z₀‖` on the sphere, then `‖G w‖ ≤ M ‖G z₀‖` on `closedBall z₀ R`. -/
theorem Complex.norm_le_of_forall_mem_sphere_norm_mul_le {P G : ℂ → ℂ} (hR : 0 < R)
    (hG : DiffContOnCl ℂ G (ball z₀ R)) (hP₀ : ∀ w ∈ sphere z₀ R, P w ≠ 0)
    (hP : ∀ w ∈ sphere z₀ R, ‖P z₀‖ ≤ ‖P w‖)
    (hPG : ∀ w ∈ sphere z₀ R, ‖P w * G w‖ ≤ M * ‖P z₀ * G z₀‖) {w : ℂ}
    (hw : w ∈ closedBall z₀ R) : ‖G w‖ ≤ M * ‖G z₀‖ := by
  have hmax {C : ℝ} (hC : ∀ u ∈ sphere z₀ R, ‖G u‖ ≤ C) {v : ℂ} (hv : v ∈ closedBall z₀ R) :
      ‖G v‖ ≤ C :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG
      (by rwa [frontier_ball z₀ hR.ne']) (by rwa [closure_ball z₀ hR.ne'])
  rcases le_or_gt 0 M with hM | hM
  · -- Divide the sphere bound by `‖P u‖ ≥ ‖P z₀‖`.
    refine hmax (fun u hu ↦ ?_) hw
    have h1 := hPG u hu
    rw [norm_mul, norm_mul] at h1
    have h2 : M * (‖P z₀‖ * ‖G z₀‖) ≤ M * (‖P u‖ * ‖G z₀‖) := by gcongr; exact hP u hu
    exact le_of_mul_le_mul_left (h1.trans (h2.trans_eq (by ring))) (norm_pos_iff.2 (hP₀ u hu))
  · -- For `M < 0` the sphere bound forces `G = 0` on the sphere, hence on the whole disc.
    have h0 (u : ℂ) (hu : u ∈ sphere z₀ R) : ‖G u‖ ≤ 0 := by
      have h1 := hPG u hu
      rw [norm_mul, norm_mul] at h1
      have hPu : 0 < ‖P u‖ := norm_pos_iff.2 (hP₀ u hu)
      have hrhs : M * (‖P z₀‖ * ‖G z₀‖) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hM.le (by positivity)
      by_contra! h
      linarith [mul_pos hPu h]
    have hz₀ : ‖G z₀‖ ≤ 0 := hmax h0 (mem_closedBall_self hR.le)
    have : ‖G z₀‖ = 0 := le_antisymm hz₀ (norm_nonneg _)
    rw [this, mul_zero]
    exact hmax h0 hw
