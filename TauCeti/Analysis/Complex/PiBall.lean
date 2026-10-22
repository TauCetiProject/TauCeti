/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Polydiscs centred at real points

A ball in `ι → ℂ` for the sup norm is a polydisc. When its centre is a real point
`fun i ↦ (a i : ℂ)`, taking real parts maps it into the ball of the same radius around `a` in
`ι → ℝ`, and it is invariant under complex conjugation.

## Main declarations

* `Complex.pi_re_mem_ball`: the real part of a point of the polydisc lies in the real ball.
* `Complex.pi_ofReal_re_mem_ball`: the real part, viewed as a complex point, lies in the polydisc.
* `Complex.pi_star_mem_ball_iff`: the polydisc is invariant under complex conjugation.
-/

public section

open Metric

namespace Complex

variable {ι : Type*} [Fintype ι] {a : ι → ℝ} {r : ℝ} {z : ι → ℂ}

/-- The real part of a point of a polydisc centred at a real point `a` lies in the ball of the
same radius around `a`. -/
theorem pi_re_mem_ball (hz : z ∈ ball (fun i ↦ (a i : ℂ)) r) :
    (fun i ↦ (z i).re) ∈ ball a r := by
  have hr := pos_of_mem_ball hz
  rw [mem_ball, dist_pi_lt_iff hr] at hz ⊢
  intro i
  calc dist (z i).re (a i) = |(z i - a i).re| := by simp [Real.dist_eq]
    _ ≤ ‖z i - a i‖ := abs_re_le_norm _
    _ < r := by simpa [dist_eq_norm] using hz i

/-- The real part of a point of a polydisc centred at a real point, viewed as a complex point,
lies in the polydisc. -/
theorem pi_ofReal_re_mem_ball (hz : z ∈ ball (fun i ↦ (a i : ℂ)) r) :
    (fun i ↦ ((z i).re : ℂ)) ∈ ball (fun i ↦ (a i : ℂ)) r := by
  have hre := pi_re_mem_ball hz
  have hr := pos_of_mem_ball hz
  rw [mem_ball, dist_pi_lt_iff hr] at hre ⊢
  intro i
  simpa [dist_of_im_eq] using hre i

/-- A polydisc centred at a real point is invariant under complex conjugation. -/
theorem pi_star_mem_ball_iff :
    star z ∈ ball (fun i ↦ (a i : ℂ)) r ↔ z ∈ ball (fun i ↦ (a i : ℂ)) r := by
  suffices ∀ w : ι → ℂ, w ∈ ball (fun i ↦ (a i : ℂ)) r → star w ∈ ball (fun i ↦ (a i : ℂ)) r from
    ⟨fun h ↦ by simpa using this _ h, this z⟩
  intro w hw
  have hr := pos_of_mem_ball hw
  rw [mem_ball, dist_pi_lt_iff hr] at hw ⊢
  intro i
  simpa [dist_eq_norm, ← norm_conj (w i - a i)] using hw i

end Complex
