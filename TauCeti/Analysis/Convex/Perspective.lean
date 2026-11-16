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
# Monotonicity of convex perspectives and lower truncations

For a convex function vanishing at zero, the perspective `s ↦ s * Φ (P / s)` is
nonincreasing on the positive half-line when `P ≥ 0`. This scalar comparison allows an
upper bound on a reciprocal-gradient integral to be substituted into a level-set Jensen
inequality. In addition, truncating any function convex on `[c, ∞)` from below at `d ≥ Φ c`
produces a nondecreasing function on `[c, ∞)` (`ConvexOn.monotoneOn_max_const`).

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

/-- Truncating a function convex on `[c, ∞)` from below at any level `d ≥ Φ c` produces a
nondecreasing function on `[c, ∞)`. -/
theorem monotoneOn_max_const {Φ : ℝ → ℝ} {c d : ℝ} (hΦ : ConvexOn ℝ (Ici c) Φ) (hd : Φ c ≤ d) :
    MonotoneOn (fun s ↦ max (Φ s) d) (Ici c) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have hcb : 0 < b - c := sub_pos.mpr (lt_of_le_of_lt ha hlt)
  set θ : ℝ := (a - c) / (b - c)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr ha) hcb.le
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.mpr ((div_le_one₀ hcb).mpr (sub_le_sub_right hab c))
  have hcomb : (1 - θ) • c + θ • b = a := by
    simp only [smul_eq_mul, θ]
    field_simp [hcb.ne']
    ring
  have hconv := hΦ.2 (le_rfl : c ∈ Ici c) hb hθ1 hθ0 (sub_add_cancel 1 θ)
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  have hbound : Φ a ≤ max (Φ b) d := calc
    Φ a ≤ (1 - θ) * Φ c + θ * Φ b := hconv
    _ ≤ (1 - θ) * max (Φ b) d + θ * max (Φ b) d :=
      add_le_add (mul_le_mul_of_nonneg_left (hd.trans (le_max_right _ _)) hθ1)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ0)
    _ = max (Φ b) d := by ring
  exact max_le hbound (le_max_right _ _)

end ConvexOn
