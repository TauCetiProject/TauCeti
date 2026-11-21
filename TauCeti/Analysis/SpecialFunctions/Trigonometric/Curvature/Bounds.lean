/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# An elementary bound for the nonpositive-curvature model cotangent

For nonpositive curvature, the model cotangent is at most the sum of the square root of
minus the curvature and the reciprocal of the radial parameter. At positive radii this
turns the model Laplacian comparison into an elementary bound. The inequality also holds
at negative parameters and at the totalized value at zero.

The hyperbolic estimate follows from `1 + 2x ≤ exp (2x)`.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/Bounds.lean` in
[ColdingMinicozziTheory][source].

[source]: https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/6966e539d9352a70e8cdeb9596f6cc098b2a18cb/ForTauCeti/Analysis/SpecialFunctions/Trigonometric/Curvature/Bounds.lean
-/

public noncomputable section

namespace TauCeti

/-- An elementary upper bound for the model cotangent in nonpositive curvature. -/
theorem curvatureCotangent_le_sqrt_neg_add_inv {κ : ℝ} (hκ : κ ≤ 0) (r : ℝ) :
    curvatureCotangent κ r ≤ Real.sqrt (-κ) + r⁻¹ := by
  rcases hκ.lt_or_eq with hneg | rfl
  · rw [curvatureCotangent_of_neg hneg]
    let a := Real.sqrt (-κ)
    have ha : 0 < a := Real.sqrt_pos.mpr (neg_pos.mpr hneg)
    by_cases hr : r = 0
    · simp [hr]
    have hs : Real.sinh (a * r) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero ha.ne' hr)
    have hrs : 0 < r * Real.sinh (a * r) := by
      rcases lt_or_gt_of_ne hr with hrneg | hrpos
      · exact mul_pos_of_neg_of_neg hrneg
          (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg ha hrneg))
      · exact mul_pos hrpos (Real.sinh_pos_iff.mpr (mul_pos ha hrpos))
    have he := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (2 * (a * r))) (Real.exp_pos (-(a * r))).le
    have hcancel : Real.exp (2 * (a * r)) * Real.exp (-(a * r)) = Real.exp (a * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcancel] at he
    have hhyper : (a * r) * Real.cosh (a * r) ≤
        (1 + a * r) * Real.sinh (a * r) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      nlinarith
    -- Fold the local abbreviation `a` so denominator clearing matches `hhyper` below.
    change a * (Real.cosh (a * r) / Real.sinh (a * r)) ≤ a + r⁻¹
    apply (mul_le_mul_iff_left₀ hrs).mp
    calc
      a * (Real.cosh (a * r) / Real.sinh (a * r)) * (r * Real.sinh (a * r)) =
          (a * r) * Real.cosh (a * r) := by field_simp
      _ ≤ (1 + a * r) * Real.sinh (a * r) := hhyper
      _ = (a + r⁻¹) * (r * Real.sinh (a * r)) := by field_simp; ring
  · simp

end TauCeti
