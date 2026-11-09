/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Convexity of powers of the norm, and internally tangent balls

In every real seminormed space, the `q`-th power of the norm is a convex function for every exponent
`1 ≤ q`, as the composition of the convex norm with the convex nondecreasing function `t ↦ t ^ q`
on `[0, ∞)`. In particular, for `0 ≤ a` every quadratic `x ↦ (a / 2) ‖x‖² + c` is convex.

In a strictly convex real normed space, the `q`-th power of the norm is a strictly convex function
for every exponent `1 < q`. Both kinds of strictness are needed: strict convexity of `t ↦ t ^ q` on
`[0, ∞)` separates points of different norms, and strict convexity of the space separates distinct
points of equal norm. The exponent `q = 1` is excluded, since the norm itself is affine along every
ray.

This is the pointwise input for strict convexity of the spaces `Lᵖ(μ; E)` with `1 < p < ∞`
(`MeasureTheory.Lp.strictConvexSpace`).

Strict convexity of the space also makes the closed ball of radius `R / 2` about the midpoint of
`x` and a point `z` of `sphere x R` internally tangent to `ball x R` at `z`: every other point of
the small closed ball lies in the open ball. This is the interior sphere geometry used by Hopf's
boundary-point lemma.

## Main statements

* `TauCeti.convexOn_norm_rpow` — `x ↦ ‖x‖ ^ q` is convex on a real seminormed space, for `1 ≤ q`.
* `TauCeti.convexOn_mul_norm_sq_add` — `x ↦ (a / 2) ‖x‖² + c` is convex on every convex set, for
  `0 ≤ a`.
* `TauCeti.strictConvexOn_norm_rpow` — `x ↦ ‖x‖ ^ q` is strictly convex on a strictly convex real
  normed space, for `1 < q`.
* `TauCeti.mem_ball_of_mem_closedBall_midpoint` — the closed ball of radius `R / 2` about the
  midpoint of `x` and `z ∈ sphere x R` meets the complement of `ball x R` only at `z`.
-/

public section

open Metric Set

namespace TauCeti

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Convexity of powers of the norm.** In a real seminormed space, the function `x ↦ ‖x‖ ^ q` is
convex for every exponent `1 ≤ q`. -/
theorem convexOn_norm_rpow {q : ℝ} (hq : 1 ≤ q) : ConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ q := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have hle := (convexOn_norm convex_univ).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hle ⊢
  calc ‖a • x + b • y‖ ^ q ≤ (a * ‖x‖ + b * ‖y‖) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) hle (zero_le_one.trans hq)
    _ ≤ a * ‖x‖ ^ q + b * ‖y‖ ^ q := by
        simpa only [smul_eq_mul] using
          (convexOn_rpow hq).2 (mem_Ici.2 (norm_nonneg x)) (mem_Ici.2 (norm_nonneg y)) ha hb hab

/-- For `0 ≤ a`, the quadratic `x ↦ (a / 2) ‖x‖² + c` is convex on every convex set in a real
seminormed space. -/
theorem convexOn_mul_norm_sq_add {s : Set E} (hs : Convex ℝ s) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    ConvexOn ℝ s fun x : E ↦ a / 2 * ‖x‖ ^ 2 + c :=
  (((convexOn_norm hs).pow (fun _ _ ↦ norm_nonneg _) 2).smul
    (by positivity : 0 ≤ a / 2)).add_const c

end Seminormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- **Strict convexity of powers of the norm.** In a strictly convex real normed space, the
function `x ↦ ‖x‖ ^ q` is strictly convex for every exponent `1 < q`. -/
theorem strictConvexOn_norm_rpow {q : ℝ} (hq : 1 < q) :
    StrictConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ q := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab ↦ ?_⟩
  have hq0 : 0 < q := zero_lt_one.trans hq
  simp only [smul_eq_mul]
  -- The norm of the combination is at most the combination of the norms.
  have hle : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  rcases ne_or_eq ‖x‖ ‖y‖ with hn | hn
  · -- Points of different norms: strict convexity of `t ↦ t ^ q`.
    calc ‖a • x + b • y‖ ^ q ≤ (a * ‖x‖ + b * ‖y‖) ^ q :=
          Real.rpow_le_rpow (norm_nonneg _) hle hq0.le
      _ < a * ‖x‖ ^ q + b * ‖y‖ ^ q := by
          simpa only [smul_eq_mul] using
            (strictConvexOn_rpow hq).2 (mem_Ici.2 (norm_nonneg x)) (mem_Ici.2 (norm_nonneg y))
              hn ha hb hab
  · -- Distinct points of equal norm: strict convexity of the space.
    have hlt : ‖a • x + b • y‖ < ‖x‖ :=
      norm_combo_lt_of_ne le_rfl hn.symm.le hxy ha hb hab
    calc ‖a • x + b • y‖ ^ q < ‖x‖ ^ q := Real.rpow_lt_rpow (norm_nonneg _) hlt hq0
      _ = a * ‖x‖ ^ q + b * ‖y‖ ^ q := by rw [← hn, ← add_mul, hab, one_mul]

/-- **Internally tangent balls.** In a strictly convex real normed space, let `z` lie on
`sphere x R`. Every point `y ≠ z` of the closed ball of radius `R / 2` about the midpoint of `x`
and `z` lies in `ball x R`. -/
theorem mem_ball_of_mem_closedBall_midpoint {x y z : E} {R : ℝ} (hz : z ∈ sphere x R)
    (hy : y ∈ closedBall (midpoint ℝ x z) (R / 2)) (hne : y ≠ z) : y ∈ ball x R := by
  -- Write `y - x = a + h` with `h = midpoint ℝ x z - x = z - midpoint ℝ x z`.
  have hmid : z - midpoint ℝ x z = midpoint ℝ x z - x := by
    rw [right_sub_midpoint, midpoint_sub_left]
  have hh : ‖midpoint ℝ x z - x‖ = R / 2 := by
    rw [← dist_eq_norm, dist_comm, dist_left_midpoint, mem_sphere'.mp hz]
    norm_num [div_eq_inv_mul]
  have ha : ‖y - midpoint ℝ x z‖ ≤ R / 2 := by rwa [← dist_eq_norm, ← mem_closedBall]
  rw [mem_ball, dist_eq_norm, ← sub_add_sub_cancel y (midpoint ℝ x z) x]
  -- If `‖a + h‖ ≥ R`, the triangle inequality is an equality, so `a` and `h` are equal.
  by_contra hR
  have hle := norm_add_le (y - midpoint ℝ x z) (midpoint ℝ x z - x)
  have hah := (sameRay_iff_norm_add.mpr (by linarith)).eq_of_norm_eq (by linarith)
  exact hne (sub_left_inj.mp (hah.trans hmid.symm))

end TauCeti
