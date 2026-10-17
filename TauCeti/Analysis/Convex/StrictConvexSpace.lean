/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Strict convexity of powers of the norm

In a strictly convex real normed space, the `q`-th power of the norm is a strictly convex function
for every exponent `1 < q`. Both kinds of strictness are needed: strict convexity of `t ↦ t ^ q` on
`[0, ∞)` separates points of different norms, and strict convexity of the space separates distinct
points of equal norm. The exponent `q = 1` is excluded, since the norm itself is affine along every
ray.

This is the pointwise input for strict convexity of the spaces `Lᵖ(μ; E)` with `1 < p < ∞`
(`MeasureTheory.Lp.strictConvexSpace`).

## Main statements

* `TauCeti.strictConvexOn_norm_rpow` — `x ↦ ‖x‖ ^ q` is strictly convex on a strictly convex real
  normed space, for `1 < q`.
-/

public section

open Set

namespace TauCeti

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

end TauCeti
