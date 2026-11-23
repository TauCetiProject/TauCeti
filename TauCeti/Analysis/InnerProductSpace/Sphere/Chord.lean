/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Chord-length characterization on spheres

This file records a chord-length consequence of the parallelogram law
`parallelogram_law_with_norm` in a real inner product space:

* `TauCeti.norm_sub_eq_two_mul_iff_of_mem_sphere`: two points on `Metric.sphere c R` lie at the
  diameter distance `2 R` if and only if they are antipodal across `c`, `y - c = -(x - c)`.

The equilateral-triangle chord length `√3 R` is
`TauCeti.norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero` in
`TauCeti.Analysis.InnerProductSpace.Triangle`.
-/

public section

namespace TauCeti

variable {F : Type*}

/-- Two points on a sphere of center `c` and radius `R` lie at distance `2 R` if and only if they
are antipodal across `c`. -/
theorem norm_sub_eq_two_mul_iff_of_mem_sphere [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x y c : F} {R : ℝ} (hx : x ∈ Metric.sphere c R) (hy : y ∈ Metric.sphere c R) :
    ‖y - x‖ = 2 * R ↔ y - c = -(x - c) := by
  have hR : 0 ≤ R := hx ▸ dist_nonneg
  have hx' : ‖x - c‖ = R := by simpa [dist_eq_norm] using hx
  have hy' : ‖y - c‖ = R := by simpa [dist_eq_norm] using hy
  have hpar : ‖(y - c) + (x - c)‖ ^ 2 + ‖y - x‖ ^ 2 = 4 * R ^ 2 := by
    rw [← sub_sub_sub_cancel_right y x c, parallelogram_law_with_norm ℝ, hx', hy']
    ring
  constructor
  · intro h
    have h0 : ‖(y - c) + (x - c)‖ ^ 2 = 0 := by
      rw [h] at hpar
      nlinarith
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 (sq_eq_zero_iff.1 h0))
  · intro h
    have hadd : (y - c) + (x - c) = 0 := add_eq_zero_iff_eq_neg.2 h
    rw [hadd, norm_zero] at hpar
    have hsq : ‖y - x‖ ^ 2 = (2 * R) ^ 2 := by nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end TauCeti
