/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Relative maximum-modulus bounds

A bound by the real part of a holomorphic function propagates from the frontier of a bounded set
to its closure: if `‖f w‖ ≤ re (g w)` on the frontier, for `f` and `g` complex differentiable
inside and continuous on the closure, then the same holds on the closure
(`Complex.norm_le_re_of_forall_mem_frontier_norm_le_re`). Since `re ∘ g` is harmonic, this is a
comparison of the subharmonic function `‖f‖` with a harmonic majorant, and it reduces to the
maximum modulus principle for `exp (ℓ ∘ f - g)` with `ℓ` a norming functional at the point.

The rest of the file gives three consequences of the maximum modulus principle for a function
`f` that is differentiable on `ball z₀ R` and continuous on its closure, under a bound on
`sphere z₀ R` relative to the value at the centre:

* if a nonzero value occurs in the closed disc under the relative sphere bound, then the
  central value is nonzero, for any real radius and any complex normed-space target;
* if `‖f w‖ ≤ M ‖f z₀‖` on the sphere and `f z₀ ≠ 0`, then `1 ≤ M`;
* if `‖P w * G w‖ ≤ M ‖P z₀ * G z₀‖` on the sphere, where `P` is nonzero there and at least as
  large as at the centre, then `‖G w‖ ≤ M ‖G z₀‖` on the closed disc.

The cofactor bound removes a factor `P` that is no smaller on the boundary than at the centre,
such as a product of linear factors over zeros near `z₀`.

The file ends with the maximum modulus principle on a closed disc with the bound read as the
supremum of `‖f‖` over the boundary circle, and the boundedness of `‖f‖` on a sphere that makes
this supremum usable with `le_ciSup`.

## Main results

* `Complex.norm_le_re_of_forall_mem_frontier_norm_le_re`
* `DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul`
* `DiffContOnCl.one_le_of_forall_mem_sphere_norm_le_mul`
* `Complex.norm_le_of_forall_mem_sphere_norm_mul_le`
* `ContinuousOn.bddAbove_range_norm_sphere`
* `DiffContOnCl.norm_le_iSup_norm_sphere_of_mem_closedBall`
-/

public section

open Metric Set

/-- **Comparison with the real part of a holomorphic function.** Let `f` and `g` be complex
differentiable on a bounded set `U` and continuous on its closure, with `f` valued in a complex
normed space and `g` complex valued. If `‖f w‖ ≤ re (g w)` on the frontier of `U`, then
`‖f z‖ ≤ re (g z)` on the closure of `U`. -/
theorem Complex.norm_le_re_of_forall_mem_frontier_norm_le_re {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {g : E → ℂ} {U : Set E} (hU : Bornology.IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U)
    (hfg : ∀ w ∈ frontier U, ‖f w‖ ≤ (g w).re) {z : E} (hz : z ∈ closure U) : ‖f z‖ ≤ (g z).re := by
  obtain ⟨ℓ, hℓ, hℓz⟩ := exists_dual_vector'' ℂ (f z)
  have hexp : DiffContOnCl ℂ (fun w ↦ Complex.exp (ℓ (f w) - g w)) U :=
    Complex.differentiable_exp.comp_diffContOnCl ((ℓ.differentiable.comp_diffContOnCl hf).sub hg)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le hU hexp (C := 1) (fun w hw ↦ by
    rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.sub_re, sub_nonpos]
    calc (ℓ (f w)).re ≤ ‖ℓ (f w)‖ := Complex.re_le_norm _
      _ ≤ ‖ℓ‖ * ‖f w‖ := ℓ.le_opNorm _
      _ ≤ ‖f w‖ := mul_le_of_le_one_left (norm_nonneg _) hℓ
      _ ≤ (g w).re := hfg w hw) hz
  rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.sub_re, sub_nonpos, hℓz] at key
  simpa using key

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

/-- Under a relative sphere bound, a nonzero value on the closed disc forces the central
value to be nonzero. The radius and bound are arbitrary real numbers; no completeness of
the complex normed target is required. -/
theorem DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ℂ → F} (hf : DiffContOnCl ℂ f (ball z₀ R))
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) {z : ℂ}
    (hz : z ∈ closedBall z₀ R) (hfz : f z ≠ 0) : f z₀ ≠ 0 := by
  by_cases hR : 0 < R
  · intro hzero
    have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
      (by rwa [frontier_ball z₀ hR.ne']) (by rwa [closure_ball z₀ hR.ne'])
    rw [hzero, norm_zero, mul_zero] at hbound
    exact hfz (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  · have hzz : z = z₀ := dist_le_zero.mp ((mem_closedBall.mp hz).trans (le_of_not_gt hR))
    simpa only [hzz] using hfz

/-- The norm of a function that is continuous on a sphere of a proper space is bounded there:
the family `w ↦ ‖f w‖` indexed by the sphere is bounded above. This is the hypothesis of
`le_ciSup` for the supremum `⨆ w : sphere x r, ‖f w‖`. -/
theorem ContinuousOn.bddAbove_range_norm_sphere {α F : Type*} [PseudoMetricSpace α]
    [ProperSpace α] [SeminormedAddGroup F] {f : α → F} {x : α} {r : ℝ}
    (hf : ContinuousOn f (sphere x r)) : BddAbove (range fun w : sphere x r => ‖f w‖) := by
  rw [← image_eq_range (fun w => ‖f w‖) (sphere x r)]
  exact (isCompact_sphere x r).bddAbove_image hf.norm

/-- The maximum modulus principle on a closed disc, in terms of the supremum over the boundary
circle: if `f` is differentiable on `ball z₀ R` and continuous on its closure, then `‖f z‖` is at
most the supremum of `‖f‖` over `sphere z₀ R` for every `z` in `closedBall z₀ R`. For `R ≠ 0` this
is Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le` on the ball, whose frontier is the
sphere; for `R = 0` the closed disc and the sphere are both `{z₀}`. -/
theorem DiffContOnCl.norm_le_iSup_norm_sphere_of_mem_closedBall {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} (hf : DiffContOnCl ℂ f (ball z₀ R))
    {z : ℂ} (hz : z ∈ closedBall z₀ R) : ‖f z‖ ≤ ⨆ w : sphere z₀ R, ‖f w‖ := by
  have hbdd := (hf.continuousOn_ball.mono sphere_subset_closedBall).bddAbove_range_norm_sphere
  rcases eq_or_ne R 0 with rfl | hR
  · rw [closedBall_zero, mem_singleton_iff] at hz
    exact le_ciSup hbdd ⟨z, by rw [hz, sphere_zero]; exact mem_singleton z₀⟩
  · refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf (fun w hw => ?_)
      (by rwa [closure_ball z₀ hR])
    rw [frontier_ball z₀ hR] at hw
    exact le_ciSup hbdd ⟨w, hw⟩
