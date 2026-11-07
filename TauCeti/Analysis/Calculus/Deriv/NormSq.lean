/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The squared distance along a differentiable path

If a path `φ` through `z₀` has velocity `z₀ - ζ` at time `0`, then the squared distance
`‖φ t - ζ‖ ^ 2` has derivative `2 * ‖z₀ - ζ‖ ^ 2` at `0`, so near `0` it stays close to its tangent
line.

## Main results

* `HasDerivAt.eventually_abs_norm_sub_sq_sub_sub_mul_le`: the tangent-line estimate for the
  squared distance along a path with velocity `z₀ - ζ`.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {z₀ ζ : E} {ρ : ℝ}

/-- **First-order tangent-line estimate for the squared distance along a path.** If a path `φ`
through `z₀` has velocity `z₀ - ζ` at `0`, where `‖z₀ - ζ‖ = ρ > 0`, then near `0` the squared
distance `‖φ t - ζ‖ ^ 2` stays within `ρ ^ 2 * |t|` of its tangent line `ρ ^ 2 + t * (2 * ρ ^ 2)`.
-/
theorem HasDerivAt.eventually_abs_norm_sub_sq_sub_sub_mul_le {φ : ℝ → E}
    (hφ : HasDerivAt φ (z₀ - ζ) 0) (hφ0 : φ 0 = z₀) (hρ : 0 < ρ) (hnorm : ‖z₀ - ζ‖ = ρ) :
    ∀ᶠ t : ℝ in 𝓝 0, |‖φ t - ζ‖ ^ 2 - ρ ^ 2 - t * (2 * ρ ^ 2)| ≤ ρ ^ 2 * |t| := by
  have hψ : HasDerivAt (fun t => ‖φ t - ζ‖ ^ 2) (2 * ρ ^ 2) 0 := by
    have h1 := (hφ.sub_const ζ).norm_sq
    rw [hφ0, real_inner_self_eq_norm_sq, hnorm] at h1
    exact h1
  have := (hasDerivAt_iff_isLittleO.mp hψ).def (sq_pos_of_pos hρ)
  simpa [hφ0, hnorm] using this
