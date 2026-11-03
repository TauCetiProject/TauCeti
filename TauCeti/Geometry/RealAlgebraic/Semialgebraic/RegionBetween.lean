/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Semialgebraic band interpolation constraints

The relation expressing affine interpolation between two pairs of endpoint coordinates is
semialgebraic, including collapsed source intervals. This coordinate-level result can be
used independently of any regularity assumptions on endpoint functions or base maps.
-/

public section

open MvPolynomial Set

namespace TauCeti

/-- The closed-interval interpolation relation is semialgebraic. When the source endpoints
coincide, the formula selects the lower target endpoint, with no condition on the upper one.
The coordinate indices need not be distinct, and their type need not be finite. -/
theorem isSemialgebraic_interpolation_constraint {R ι : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c d t s : ι) : IsSemialgebraic {z : ι → R |
      z a ≤ z t ∧ z t ≤ z b ∧ z s = z c + (z t - z a) / (z b - z a) * (z d - z c)} := by
  have h₁ := isSemialgebraic_eval_le (R := R) (X a) (X t)
  have h₂ := isSemialgebraic_eval_le (R := R) (X t) (X b)
  have h₃ := isSemialgebraic_eval_eq (R := R) (X b) (X a)
  have h₄ := isSemialgebraic_eval_eq (R := R) (X s) (X c)
  have h₅ := isSemialgebraic_eval_eq (R := R)
    ((X s - X c) * (X b - X a)) ((X t - X a) * (X d - X c))
  convert h₁.inter (h₂.inter ((h₃.inter h₄).union (h₃.compl.inter h₅))) using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_compl_iff,
    map_mul, map_sub, eval_X]
  by_cases h : z b = z a
  · simp [h]
  · simp only [h, false_and, not_false_eq_true, true_and, false_or, and_congr_right_iff]
    intro _ _
    have hne : z b - z a ≠ 0 := sub_ne_zero.mpr h
    field_simp
    constructor <;> intro heq <;> nlinarith [heq]

end TauCeti
