/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Harnack chains along segments

A Harnack inequality is usually first proved at a single scale: for a nonnegative solution `g`,
`g x ≤ C (g y + K)` whenever `x` and `y` are within distance `t` of each other, where `K` accounts
for the right-hand side of the equation. Joining two points of a convex set by a segment cut into
`N` pieces of length at most `t` propagates the estimate to points at distance at most `N t`, with
the constant `C ^ N` and the error `N K`
(`Convex.le_pow_mul_add_mul_of_dist_le_mul`). This is the *Harnack chain* argument
(Gilbarg–Trudinger, proof of Theorem 8.20).

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.20.
-/

public section

open AffineMap Set

namespace Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/-- **Harnack chains.** Let `s` be convex, and let `g x ≤ C (g y + K)` hold for all `x, y ∈ s` at
distance at most `t`, with `C ≥ 1` and `K ≥ 0`. Then `g x ≤ C ^ N (g y + N K)` for all `x, y ∈ s`
at distance at most `N t`. -/
theorem le_pow_mul_add_mul_of_dist_le_mul (hs : Convex ℝ s) {g : E → ℝ} {C K t : ℝ}
    (hC : 1 ≤ C) (hK : 0 ≤ K) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ t → g x ≤ C * (g y + K))
    (N : ℕ) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hxy : dist x y ≤ N * t) :
    g x ≤ C ^ N * (g y + N * K) := by
  induction N generalizing x with
  | zero =>
    rw [Nat.cast_zero, zero_mul, dist_le_zero] at hxy
    simp [hxy]
  | succ N ih =>
    -- Step from `x` to the point `w` at the fraction `1 / (N + 1)` of the way to `y`.
    have hN : (0 : ℝ) < N + 1 := by positivity
    set c : ℝ := ((N : ℝ) + 1)⁻¹
    have hc : c ∈ Icc (0 : ℝ) 1 := ⟨by positivity, inv_le_one_of_one_le₀ (by simp)⟩
    have hxy' : dist x y ≤ (N + 1) * t := by exact_mod_cast hxy
    have hw : lineMap x y c ∈ s := hs.lineMap_mem hx hy hc
    have hxw : dist x (lineMap x y c) ≤ t := by
      rw [dist_left_lineMap, Real.norm_of_nonneg hc.1]
      exact (inv_mul_le_iff₀ hN).2 hxy'
    have hwy : dist (lineMap x y c) y ≤ N * t := by
      rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.2 hc.2)]
      calc (1 - c) * dist x y ≤ (1 - c) * ((N + 1) * t) := by gcongr; exact sub_nonneg.2 hc.2
        _ = N * t := by linear_combination (-t) * (inv_mul_cancel₀ hN.ne' : c * (N + 1) = 1)
    have : 0 ≤ C := zero_le_one.trans hC
    calc g x ≤ C * (g (lineMap x y c) + K) := h x hx _ hw hxw
      _ ≤ C * (C ^ N * (g y + N * K) + K) := by gcongr; exact ih hw hwy
      _ = C ^ (N + 1) * (g y + N * K) + C * K := by ring
      _ ≤ C ^ (N + 1) * (g y + N * K) + C ^ (N + 1) * K := by
        gcongr
        exact le_self_pow₀ hC N.succ_ne_zero
      _ = C ^ (N + 1) * (g y + (N + 1 : ℕ) * K) := by push_cast; ring

end Convex
