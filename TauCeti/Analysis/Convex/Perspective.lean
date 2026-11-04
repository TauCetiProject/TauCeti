/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp

/-!
# Monotonicity of a convex perspective

For a convex function vanishing at zero, the perspective `s ↦ s * Φ (P / s)` is
nonincreasing on the positive half-line when `P ≥ 0`. This scalar comparison allows an
upper bound on a reciprocal-gradient integral to be substituted into a level-set Jensen
inequality.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen,
  *The Pólya–Szegő inequality for smoothing rearrangements*, Theorem 5.8.
-/

public section

open Set

namespace ConvexOn

/-- The perspective of a convex function vanishing at zero is nonincreasing in its
positive denominator, for a fixed nonnegative numerator. No monotonicity of `Φ` is needed. -/
theorem antitoneOn_mul_map_div {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦ0 : Φ 0 = 0) {P : ℝ} (hP : 0 ≤ P) :
    AntitoneOn (fun s : ℝ ↦ s * Φ (P / s)) (Ioi 0) := by
  intro s hs t ht hst
  have hzero : (0 : ℝ) ∈ Ici 0 := le_rfl
  have hdiv : P / s ∈ Ici 0 := div_nonneg hP hs.le
  have hcoeff : 0 ≤ 1 - s / t := sub_nonneg.mpr ((div_le_one₀ ht).mpr hst)
  have h := hΦ.2 hzero hdiv hcoeff
    (div_nonneg hs.le ht.le) (sub_add_cancel 1 (s / t))
  simp only [smul_eq_mul, mul_zero, zero_add, hΦ0] at h
  have heq : s / t * (P / s) = P / t := by field_simp [ne_of_gt hs]
  rw [heq] at h
  calc
    t * Φ (P / t) ≤ t * (s / t * Φ (P / s)) := mul_le_mul_of_nonneg_left h ht.le
    _ = s * Φ (P / s) := by field_simp [ne_of_gt ht]

end ConvexOn
