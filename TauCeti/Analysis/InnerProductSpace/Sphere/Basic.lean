/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner-product bounds on balls

A vector in the open unit ball has inner product strictly greater than `-1` with every vector
of the closed unit ball. These bounds ensure positivity of denominators in maps of the unit sphere.
The file also records that if `‖a‖ ≤ ‖x‖` then `x - a` points weakly outward at `x`,
`0 ≤ ⟪x - a, x⟫` (`TauCeti.inner_sub_self_nonneg_of_norm_le`).

Adapted from Giada Franz's local formalization of Hersch's balancing lemma.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the closed unit ball, `1 + ⟪a, x⟫` is positive for `‖a‖ < 1`. -/
theorem one_add_inner_pos {a x : E} (ha : ‖a‖ < 1) (hx : ‖x‖ ≤ 1) : 0 < 1 + ⟪a, x⟫ := by
  have := neg_le_of_abs_le (abs_real_inner_le_norm a x)
  have := mul_le_of_le_one_right (norm_nonneg a) hx
  linarith

/-- A vector in the open unit ball cannot have inner product `-1` with a vector of the
closed unit ball. -/
theorem inner_ne_neg_one {a x : E} (ha : ‖a‖ < 1) (hx : ‖x‖ ≤ 1) : ⟪a, x⟫ ≠ -1 := by
  have := one_add_inner_pos ha hx
  intro h
  linarith

/-- If `‖a‖ ≤ ‖x‖`, then `x - a` points weakly outward at `x`: `0 ≤ ⟪x - a, x⟫`. -/
theorem inner_sub_self_nonneg_of_norm_le {x a : E} (h : ‖a‖ ≤ ‖x‖) : 0 ≤ ⟪x - a, x⟫ := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith [real_inner_le_norm a x, norm_nonneg a]

end TauCeti
