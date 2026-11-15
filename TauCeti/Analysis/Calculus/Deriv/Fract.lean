/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# The periodic quadratic `fract t ^ 2 - fract t`

The function `t ↦ fract t ^ 2 - fract t` is `1`-periodic, vanishes at the integers, and is
continuous because the quadratic `x ^ 2 - x` takes the same value at `0` and `1`. Its right
derivative everywhere is `2 fract t - 1`, and it takes values in `[-1/4, 0]`. Half of it is the
periodic kernel `P₂` against which a sawtooth remainder `fract t - 1/2` is integrated by parts
in Euler–Maclaurin type estimates.

## Main declarations

* `Int.continuous_fract_sq_sub_fract`: `t ↦ fract t ^ 2 - fract t` is continuous.
* `Int.hasDerivWithinAt_fract_sq_sub_fract`: its right derivative at `t` is `2 fract t - 1`.
* `Int.abs_fract_sq_sub_fract_le`: `|fract t ^ 2 - fract t| ≤ 1 / 4`.
-/

public section

open Set Filter

namespace Int

/-- The function `t ↦ fract t ^ 2 - fract t` is continuous: `x ^ 2 - x` agrees at `0` and `1`. -/
theorem continuous_fract_sq_sub_fract : Continuous fun t : ℝ ↦ fract t ^ 2 - fract t :=
  ContinuousOn.comp_fract'' (f := fun x : ℝ ↦ x ^ 2 - x) (by fun_prop) (by norm_num)

/-- The function `t ↦ fract t ^ 2 - fract t` has right derivative `2 fract t - 1` at every
point. -/
theorem hasDerivWithinAt_fract_sq_sub_fract (t : ℝ) :
    HasDerivWithinAt (fun u : ℝ ↦ fract u ^ 2 - fract u) (2 * fract t - 1) (Ioi t) t := by
  have hp : HasDerivAt (fun u : ℝ ↦ (u - ⌊t⌋) ^ 2 - (u - ⌊t⌋)) (2 * fract t - 1) t := by
    have h := (((hasDerivAt_id' t).sub_const (⌊t⌋ : ℝ)).pow 2).sub
      ((hasDerivAt_id' t).sub_const (⌊t⌋ : ℝ))
    refine h.congr_deriv ?_
    rw [← self_sub_floor]
    ring
  refine hp.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [← self_sub_floor])
  filter_upwards [Ioo_mem_nhdsGT (lt_floor_add_one t)] with u hu
  have hfl : ⌊u⌋ = ⌊t⌋ := by
    rw [floor_eq_iff]
    exact ⟨(floor_le t).trans hu.1.le, hu.2⟩
  rw [← self_sub_floor, hfl]

/-- `|fract t ^ 2 - fract t| ≤ 1 / 4`, since `fract t ∈ [0, 1)`. -/
theorem abs_fract_sq_sub_fract_le (t : ℝ) : |fract t ^ 2 - fract t| ≤ 1 / 4 := by
  have h0 := fract_nonneg t
  have h1 := fract_lt_one t
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (fract t - 1 / 2)]

end Int
