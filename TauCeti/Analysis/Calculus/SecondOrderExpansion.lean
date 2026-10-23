/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Uniqueness of the second-order term of a Taylor expansion

Let `u` be a real function on a real inner product space `E`. A second-order Taylor expansion of
`u` at `x` is an expansion

  `u x' = u x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)`

with `y : E` and an operator `A : E →L[ℝ] E`. Only the quadratic form of `A` is determined by `u`,
so `A` is unique once it is required to be symmetric: two symmetric second-order terms differ by a
symmetric operator whose quadratic form is `o(‖x' - x‖ ^ 2)`, hence zero along every line through
`x`, and a symmetric operator with vanishing quadratic form is zero. No differentiability of `u`
beyond the expansion itself is assumed, so the statement applies to the Alexandrov Hessian of a
convex function.

## Main statements

* `TauCeti.eq_of_isSymmetric_of_isLittleO` — the symmetric second-order term of a Taylor
  expansion is unique.
-/

public section

namespace TauCeti

open Filter Asymptotics Function
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The symmetric second-order term of a Taylor expansion is unique.** If the real function `u`
has the second-order expansions
`u x' = u x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)` and the same with `B`, and
`A` and `B` are symmetric, then `A = B`. -/
theorem eq_of_isSymmetric_of_isLittleO {u : E → ℝ} {x y : E} {A B : E →L[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hTA : (fun x' => u x' - u x - ⟪y, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2)
    (hTB : (fun x' => u x' - u x - ⟪y, x' - x⟫_ℝ - ⟪B (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2) :
    A = B := by
  -- The quadratic form of `A - B` is `o(‖x' - x‖ ^ 2)`. Restricted to the line through `x` in a
  -- direction `v` it is `t ^ 2 ⟪(A - B) v, v⟫`, so it vanishes, and a symmetric operator with
  -- vanishing quadratic form is zero.
  have hD : (fun x' => ⟪(A - B) (x' - x), x' - x⟫_ℝ) =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
    refine ((hTB.sub hTA).const_mul_left 2).congr_left fun x' => ?_
    simp only [sub_apply, inner_sub_left]
    ring
  have hq : ∀ v, ⟪(A - B) v, v⟫_ℝ = 0 := fun v => by
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝[≠] 0) (𝓝 x) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x
        (by simp)).mono_left nhdsWithin_le_nhds
    have h := ((hD.comp_tendsto hlim).mul_isBigO (isBigO_refl (fun t : ℝ => (t ^ 2)⁻¹) _))
    refine (isLittleO_const_const_iff (c := ‖v‖ ^ 2)).1 (h.congr' ?_ ?_)
    all_goals
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      simp only [comp_apply, add_sub_cancel_left, map_smul, real_inner_smul_left,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
  have h := (hA.sub hB).inner_map_self_eq_zero.1 (by simpa using hq)
  exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective (by simpa using h))

end TauCeti
