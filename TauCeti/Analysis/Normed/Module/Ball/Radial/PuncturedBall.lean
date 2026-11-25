/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Pushing a punctured ball onto its boundary sphere

In a real normed space and for a radius `r`, the homotopy `TauCeti.puncturedBallPush r` moves
every vector `y ≠ 0` of norm less than `r` along its ray, at time `t` scaling it by
`1 - t + t r / ‖y‖`, so that at time one it reaches the sphere of radius `r`. Every vector of norm
at least `r` stays fixed at all times, and so does `0`. Unlike `TauCeti.radialPush`, which moves
every vector of the closed unit ball, this deformation is the identity outside the ball of radius
`r`, so it can be glued with the identity outside a cell; it is continuous only off the origin.

## Main declarations

* `TauCeti.puncturedBallPush`: the push of the punctured ball of radius `r` onto its boundary
  sphere.
* `TauCeti.puncturedBallPush_apply`: its value, as a multiple of the vector.
* `TauCeti.puncturedBallPush_zero` and `TauCeti.puncturedBallPush_of_le_norm`: it starts at the
  identity and fixes the complement of the ball of radius `r`.
* `TauCeti.puncturedBallPush_zero_right`: it fixes the origin.
* `TauCeti.norm_puncturedBallPush_le`: it does not leave the ball of radius `max ‖y‖ r`.
* `TauCeti.le_norm_puncturedBallPush_one`: at the end it sends nonzero vectors outside the ball
  of radius `r`.
* `TauCeti.puncturedBallPush_ne_zero` and `TauCeti.continuousAt_puncturedBallPush`: it keeps
  nonzero vectors nonzero and is continuous off the origin.
-/

public section

open unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} {y : E}

/-- The push of the punctured ball of radius `r` onto its boundary sphere: at time `t` the
vector `y` is scaled by `max 1 (1 - t + t r / ‖y‖)`. Vectors of norm at least `r` are fixed. -/
noncomputable def puncturedBallPush (r : ℝ) (t : I) (y : E) : E :=
  max 1 (1 - (t : ℝ) + t * (r / ‖y‖)) • y

/-- The value of the push: at time `t` it scales `y` by `max 1 (1 - t + t r / ‖y‖)`. -/
theorem puncturedBallPush_apply (r : ℝ) (t : I) (y : E) :
    puncturedBallPush r t y = max 1 (1 - (t : ℝ) + t * (r / ‖y‖)) • y := by
  rw [puncturedBallPush]

/-- The push fixes the origin at all times. -/
@[simp]
theorem puncturedBallPush_zero_right (r : ℝ) (t : I) : puncturedBallPush r t (0 : E) = 0 := by
  rw [puncturedBallPush_apply, smul_zero]

/-- At time zero the push is the identity. -/
@[simp]
theorem puncturedBallPush_zero (r : ℝ) (y : E) : puncturedBallPush r 0 y = y := by
  simp [puncturedBallPush]

/-- The push fixes every vector of norm at least `r`. -/
theorem puncturedBallPush_of_le_norm (t : I) (hy : r ≤ ‖y‖) : puncturedBallPush r t y = y := by
  have ht : (t : ℝ) * (r / ‖y‖) ≤ t :=
    mul_le_of_le_one_right t.property.1 (div_le_one_of_le₀ hy (norm_nonneg _))
  rw [puncturedBallPush, max_eq_left (by linarith), one_smul]

/-- The norm along the push is the norm of `y` times the scaling factor. -/
theorem norm_puncturedBallPush (r : ℝ) (t : I) (y : E) :
    ‖puncturedBallPush r t y‖ = max 1 (1 - (t : ℝ) + t * (r / ‖y‖)) * ‖y‖ := by
  rw [puncturedBallPush, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (le_max_left _ _))]

/-- The push does not leave the closed ball of radius `max ‖y‖ r`. -/
theorem norm_puncturedBallPush_le (r : ℝ) (t : I) (y : E) :
    ‖puncturedBallPush r t y‖ ≤ max ‖y‖ r := by
  rw [norm_puncturedBallPush]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases le_total (1 - (t : ℝ) + t * (r / ‖y‖)) 1 with h | h
  · rw [max_eq_left h, one_mul]
    exact le_max_left _ _
  · -- Off the unit factor, the norm is `(1 - t) ‖y‖ + t r`, between `‖y‖` and `r`.
    have h2 : r / ‖y‖ * ‖y‖ = r := div_mul_cancel₀ r hpos.ne'
    rw [max_eq_right h, add_mul, mul_assoc, h2]
    nlinarith [t.property.1, t.property.2, le_max_left ‖y‖ r, le_max_right ‖y‖ r]

/-- The push keeps nonzero vectors nonzero. -/
theorem puncturedBallPush_ne_zero (r : ℝ) (t : I) (hy : y ≠ 0) : puncturedBallPush r t y ≠ 0 :=
  smul_ne_zero (zero_lt_one.trans_le (le_max_left _ _)).ne' hy

/-- At the end, the push sends every nonzero vector outside the open ball of radius `r`. -/
theorem le_norm_puncturedBallPush_one (r : ℝ) (hy : y ≠ 0) : r ≤ ‖puncturedBallPush r 1 y‖ := by
  rw [norm_puncturedBallPush]
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  calc r = (1 - ((1 : I) : ℝ) + (1 : I) * (r / ‖y‖)) * ‖y‖ := by
        simp [div_mul_cancel₀ r hpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

/-- The push is continuous in the time and the vector, away from the origin. -/
theorem continuousAt_puncturedBallPush (r : ℝ) {t : I} (hy : y ≠ 0) :
    ContinuousAt (fun q : I × E ↦ puncturedBallPush r q.1 q.2) (t, y) := by
  have hdiv : ContinuousAt (fun q : I × E ↦ r / ‖q.2‖) (t, y) :=
    continuousAt_const.div continuous_snd.norm.continuousAt (norm_ne_zero_iff.2 hy)
  unfold puncturedBallPush
  exact (continuousAt_const.max ((continuousAt_const.sub
    (continuous_subtypeVal.comp continuous_fst).continuousAt).add
    ((continuous_subtypeVal.comp continuous_fst).continuousAt.mul hdiv))).smul
    continuous_snd.continuousAt

end TauCeti
