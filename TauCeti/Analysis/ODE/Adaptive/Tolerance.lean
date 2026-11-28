/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Mixed absolute and relative tolerances

An adaptive integrator for a system with state space `ι → ℝ` compares an error indicator
`Δ : ι → ℝ` with a tolerance in each component. With absolute tolerances `atol i > 0`, relative
tolerances `rtol i ≥ 0` and the two states `u` and `v` of a trial step (for an embedded pair, the
current state and the proposed new state), the scale of component `i` is
`s i = atol i + rtol i * max |u i| |v i|`, and the normalised indicator is the maximum norm
`w = ‖fun i ↦ Δ i / s i‖`. A trial is accepted when `w ≤ 1`.

## Main definitions

* `TauCeti.toleranceScale atol rtol u v i`: the scale `atol i + rtol i * max |u i| |v i|`.
* `TauCeti.scaledError atol rtol u v Δ`: the normalised indicator `‖fun i ↦ Δ i / s i‖`.

## Main results

* `TauCeti.toleranceScale_pos`: each scale is positive.
* `TauCeti.scaledError_le_iff`, `TauCeti.scaledError_le_one_iff`: `w ≤ c` if and only if
  `|Δ i| ≤ c * s i` for every component; in particular `w ≤ 1` if and only if `|Δ i| ≤ s i`.
* `TauCeti.scaledError_of_isEmpty`: without components, `w = 0`.
* `TauCeti.scaledError_mul_left`: `w` does not change when `u i`, `v i`, `Δ i` and `atol i` are
  multiplied by the same `λ i > 0` (a change of the unit of component `i`), with `rtol` unchanged.

## References

* E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I*,
  2nd edition, Springer, 1993, Section II.4.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- The tolerance scale `atol i + rtol i * max |u i| |v i|` of component `i`, for absolute
tolerances `atol`, relative tolerances `rtol` and the two states `u` and `v` of a trial step. -/
def toleranceScale (atol rtol u v : ι → ℝ) (i : ι) : ℝ :=
  atol i + rtol i * max |u i| |v i|

theorem toleranceScale_def (atol rtol u v : ι → ℝ) (i : ι) :
    toleranceScale atol rtol u v i = atol i + rtol i * max |u i| |v i| := (rfl)

/-- A positive absolute tolerance and a nonnegative relative tolerance give a positive scale. -/
theorem toleranceScale_pos {atol rtol : ι → ℝ} (u v : ι → ℝ) {i : ι} (ha : 0 < atol i)
    (hr : 0 ≤ rtol i) : 0 < toleranceScale atol rtol u v i := by
  rw [toleranceScale_def]
  have : 0 ≤ max |u i| |v i| := le_max_of_le_left (abs_nonneg _)
  positivity

/-- Multiplying `atol i`, `u i` and `v i` by `λ i ≥ 0` multiplies the scale of component `i`
by `λ i`. -/
theorem toleranceScale_mul_left (atol rtol u v scale : ι → ℝ) {i : ι} (hs : 0 ≤ scale i) :
    toleranceScale (scale * atol) rtol (scale * u) (scale * v) i =
      scale i * toleranceScale atol rtol u v i := by
  simp only [toleranceScale_def, Pi.mul_apply, abs_mul, abs_of_nonneg hs,
    ← mul_max_of_nonneg _ _ hs]
  ring

variable [Fintype ι]

/-- The normalised indicator `‖fun i ↦ Δ i / s i‖` of an indicator `Δ`, in the maximum norm of
`ι → ℝ`, where `s = toleranceScale atol rtol u v`. -/
noncomputable def scaledError (atol rtol u v Δ : ι → ℝ) : ℝ :=
  ‖fun i ↦ Δ i / toleranceScale atol rtol u v i‖

theorem scaledError_def (atol rtol u v Δ : ι → ℝ) :
    scaledError atol rtol u v Δ = ‖fun i ↦ Δ i / toleranceScale atol rtol u v i‖ := (rfl)

theorem scaledError_nonneg (atol rtol u v Δ : ι → ℝ) : 0 ≤ scaledError atol rtol u v Δ :=
  norm_nonneg _

/-- Without components, the normalised indicator is zero. -/
@[simp]
theorem scaledError_of_isEmpty [IsEmpty ι] (atol rtol u v Δ : ι → ℝ) :
    scaledError atol rtol u v Δ = 0 := by
  rw [scaledError_def, Subsingleton.elim (fun i ↦ Δ i / toleranceScale atol rtol u v i) 0,
    norm_zero]

/-- For `c ≥ 0`, the normalised indicator is at most `c` if and only if `|Δ i| ≤ c * s i` in
every component. -/
theorem scaledError_le_iff (atol rtol u v Δ : ι → ℝ) (ha : ∀ i, 0 < atol i)
    (hr : ∀ i, 0 ≤ rtol i) {c : ℝ} (hc : 0 ≤ c) :
    scaledError atol rtol u v Δ ≤ c ↔ ∀ i, |Δ i| ≤ c * toleranceScale atol rtol u v i := by
  rw [scaledError_def, pi_norm_le_iff_of_nonneg hc]
  refine forall_congr' fun i ↦ ?_
  have hs := toleranceScale_pos u v (ha i) (hr i)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_le_iff₀ hs]

/-- The acceptance test `w ≤ 1` holds if and only if `|Δ i| ≤ s i` in every component. -/
theorem scaledError_le_one_iff (atol rtol u v Δ : ι → ℝ) (ha : ∀ i, 0 < atol i)
    (hr : ∀ i, 0 ≤ rtol i) :
    scaledError atol rtol u v Δ ≤ 1 ↔ ∀ i, |Δ i| ≤ toleranceScale atol rtol u v i := by
  simpa only [one_mul] using scaledError_le_iff atol rtol u v Δ ha hr zero_le_one

/-- The normalised indicator does not depend on the units of the components: multiplying
`atol i`, `u i`, `v i` and `Δ i` by the same `λ i > 0`, with `rtol` unchanged, leaves it fixed. -/
theorem scaledError_mul_left (atol rtol u v Δ scale : ι → ℝ) (hs : ∀ i, 0 < scale i) :
    scaledError (scale * atol) rtol (scale * u) (scale * v) (scale * Δ) =
      scaledError atol rtol u v Δ := by
  simp only [scaledError_def, toleranceScale_mul_left _ _ _ _ _ (hs _).le, Pi.mul_apply,
    mul_div_mul_left _ _ (hs _).ne']

end TauCeti
