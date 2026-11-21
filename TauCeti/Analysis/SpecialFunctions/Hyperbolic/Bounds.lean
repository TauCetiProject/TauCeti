/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A strict upper bound for the hyperbolic cotangent

At a positive argument, the hyperbolic cotangent is strictly smaller than the reciprocal
plus one third of the argument. Two derivative comparisons, each starting at zero, give
the strict inequality. The radius sign is essential.

This converts hyperbolic cotangent comparison terms into reciprocal-plus-linear bounds
for distance-support estimates, comparing the matched hyperbolic and linear profiles.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/SpecialFunctions/Hyperbolic/Bounds.lean` in
[ColdingMinicozziTheory][source].

[source]: https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/6966e539d9352a70e8cdeb9596f6cc098b2a18cb/ForTauCeti/Analysis/SpecialFunctions/Hyperbolic/Bounds.lean
-/

public noncomputable section

open Set

namespace Real

private theorem sinh_lt_mul_cosh_of_pos {x : ℝ} (hx : 0 < x) : sinh x < x * cosh x := by
  have hd (t : ℝ) : HasDerivAt (fun t ↦ t * cosh t - sinh t) (t * sinh t) t := by
    convert (((hasDerivAt_id t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)) using 1
    · rfl
    · dsimp
      ring
  have hmono : StrictMonoOn (fun t ↦ t * cosh t - sinh t) (Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hd t).hasDerivWithinAt) fun t ht ↦ by
        rw [interior_Ici, mem_Ioi] at ht
        exact mul_pos ht (sinh_pos_iff.mpr ht)
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  simpa only [zero_mul, sinh_zero, sub_zero, sub_pos] using h

private theorem linear_sinh_sub_mul_cosh_pos {x : ℝ} (hx : 0 < x) :
    0 < (x ^ 2 + 3) * sinh x - 3 * x * cosh x := by
  have hd (t : ℝ) : HasDerivAt (fun t ↦ (t ^ 2 + 3) * sinh t - 3 * t * cosh t)
      (t * (t * cosh t - sinh t)) t := by
    convert (((((hasDerivAt_id t).pow 2).add_const 3).mul (hasDerivAt_sinh t)).sub
      (((hasDerivAt_id t).const_mul 3).mul (hasDerivAt_cosh t))) using 1
    · rfl
    · dsimp
      ring
  have hmono : StrictMonoOn (fun t ↦ (t ^ 2 + 3) * sinh t - 3 * t * cosh t) (Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hd t).hasDerivWithinAt) fun t ht ↦ by
        rw [interior_Ici, mem_Ioi] at ht
        exact mul_pos ht (sub_pos.mpr (sinh_lt_mul_cosh_of_pos ht))
  simpa only [sinh_zero, mul_zero, zero_mul, sub_zero] using
    hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx

/-- At a positive argument, the hyperbolic cotangent is strictly less than the reciprocal
plus one third of that argument. -/
theorem cosh_div_sinh_lt_inv_add_div_three {x : ℝ} (hx : 0 < x) :
    cosh x / sinh x < x⁻¹ + x / 3 := by
  apply (div_lt_iff₀ (sinh_pos_iff.mpr hx)).mpr
  have hpos : 0 < 3 * x := by positivity
  apply (mul_lt_mul_iff_right₀ hpos).mp
  have hfactor : 3 * x * ((x⁻¹ + x / 3) * sinh x) = (x ^ 2 + 3) * sinh x := by
    field_simp [hx.ne']
    ring
  rw [hfactor]
  exact sub_pos.mp (linear_sinh_sub_mul_cosh_pos hx)

end Real
