/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Caps of a unit sphere

For a unit vector `a` of a real inner product space and a real number `r`, the closed cap of the
unit sphere around `a` at height `r` is the set of unit vectors `x` with `⟪x, a⟫ ≥ r`. For
`r > 0` it is the closed ball around `a` of angular radius `arccos r`. This file records two
criteria, stated through inner products only, for caps to be disjoint and for a cap to lie in an
open hemisphere. They are what keeps knotted arcs confined to small caps apart when the caps are
slid along a great circle.

## Main results

* `TauCeti.inner_lt_of_le_inner`: two caps at height `r` around `a` and `b` are disjoint when
  `⟪a, b⟫ < 2 r² - 1`.
* `TauCeti.inner_pos_of_le_inner`: a cap at height `r` around `a` lies in the open hemisphere
  around `u` when `⟪a, u⟫ ≥ 0` and `1 - ⟪a, u⟫² < r²`.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {x a b u : F} {r : ℝ}

/-- **Disjoint caps.** For `r > 0`, the closed caps `⟪x, a⟫ ≥ r` and `⟪x, b⟫ ≥ r` of the unit
sphere around unit vectors `a` and `b` are disjoint when `⟪a, b⟫ < 2 r² - 1`: a unit vector `x`
in the first cap has `⟪x, b⟫ < r`. -/
theorem inner_lt_of_le_inner (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hr : 0 < r)
    (hab : ⟪a, b⟫ < 2 * r ^ 2 - 1) (hxa : r ≤ ⟪x, a⟫) : ⟪x, b⟫ < r := by
  by_contra! hxb
  have hab' : ⟪a + b, a + b⟫ = 2 + 2 * ⟪a, b⟫ := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, ha, hb, real_inner_comm a b]
    ring
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h := real_inner_mul_inner_self_le x (a + b)
  rw [hab', hxx, inner_add_right] at h
  nlinarith

/-- **A cap inside a hemisphere.** For `r > 0`, the closed cap `⟪x, a⟫ ≥ r` of the unit sphere
around a unit vector `a` lies in the open hemisphere `⟪x, u⟫ > 0` around a unit vector `u` when
`⟪a, u⟫ ≥ 0` and `1 - ⟪a, u⟫² < r²`, that is, when the component of `a` orthogonal to `u` is
shorter than `r`. -/
theorem inner_pos_of_le_inner (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (hr : 0 < r)
    (hau : 0 ≤ ⟪a, u⟫) (hau' : 1 - ⟪a, u⟫ ^ 2 < r ^ 2) (hxa : r ≤ ⟪x, a⟫) : 0 < ⟪x, u⟫ := by
  by_contra! hxu
  have hd : ⟪a - ⟪a, u⟫ • u, a - ⟪a, u⟫ • u⟫ = 1 - ⟪a, u⟫ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hu, real_inner_comm u a]
    ring
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h := real_inner_mul_inner_self_le x (a - ⟪a, u⟫ • u)
  rw [hd, hxx, inner_sub_right, real_inner_smul_right] at h
  have h₂ : r ≤ ⟪x, a⟫ - ⟪a, u⟫ * ⟪x, u⟫ := by nlinarith
  nlinarith

end TauCeti
