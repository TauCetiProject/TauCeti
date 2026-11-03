/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Pointwise

/-!
# Inner parallel sets

In a seminormed additive group, the inner parallel set `{x | t ≤ infDist x Uᶜ}` of a set `U`,
thickened by the open ball of radius `t`, stays inside `U`
(`TauCeti.setOf_le_infDist_compl_add_ball_subset`).
-/

public section

open Metric Set
open scoped Pointwise

namespace TauCeti

/-- The inner parallel set `{t ≤ d}` of `U`, where `d` is the distance to the complement,
thickened by the open ball of radius `t`, stays inside `U`. -/
theorem setOf_le_infDist_compl_add_ball_subset {G : Type*} [SeminormedAddCommGroup G]
    (U : Set G) (t : ℝ) : {x | t ≤ infDist x Uᶜ} + ball (0 : G) t ⊆ U := by
  rintro _ ⟨x, hx, b, hb, rfl⟩
  by_contra h
  have : infDist x Uᶜ ≤ dist x (x + b) := infDist_le_dist_of_mem h
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg] at this
  rw [mem_ball_zero_iff] at hb
  exact absurd ((hx : t ≤ infDist x Uᶜ).trans this) (not_le.2 hb)

end TauCeti
