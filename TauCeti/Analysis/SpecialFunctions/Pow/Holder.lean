/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.SpecialFunctions.Pow.PowSign
import TauCeti.Basic.Real.Sign
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of real powers

For `0 ≤ p ≤ 1` the power `t ↦ t ^ p` is `p`-Hölder on `[0, ∞)` with constant one:
`|a ^ p - b ^ p| ≤ |a - b| ^ p` for `a, b ≥ 0`. This is the subadditivity
`(a + b) ^ p ≤ a ^ p + b ^ p` of Mathlib's `Real.rpow_add_le_add_rpow`, applied to `b` and
`a - b`. It is the estimate showing that cone-point functions such as `‖z‖ ^ p` are `p`-Hölder.

The signed powers `|x|^β sgn(x)^j` are `β`-Hölder on all of `ℝ` with constant `2`, for `β ≤ 1`
(`TauCeti.holderWith_abs_rpow_mul_sign_pow`): on one side of the origin this is the Hölder bound
of the cusp `|x| ^ β` (`TauCeti.holderWith_norm_rpow`), and across it both values are at most
`|x - y|^β` in absolute value (`TauCeti.abs_abs_rpow_mul_sign_pow_le`, in
`TauCeti.Analysis.SpecialFunctions.Pow.PowSign`). For `j = 1` this is the odd power
`sign(x) |x| ^ β`. When `0 < β ≤ 1` it is the derivative of `|x| ^ (β + 1) / (β + 1)`, which is
therefore `C^{1,β}`; at `β = 0` that primitive is `|x|`, which is not differentiable at `0`.
-/

public section

open scoped NNReal

namespace Real

/-- On `[0, ∞)` the power `t ↦ t ^ p` is `p`-Hölder with constant one, for `0 ≤ p ≤ 1`. -/
theorem abs_rpow_sub_rpow_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) : |a ^ p - b ^ p| ≤ |a - b| ^ p := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have h := rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hp hp1
  rw [sub_add_cancel] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hb hab hp)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

end Real

namespace TauCeti

/-- For `β ≤ 1`, the signed power `|x|^β sgn(x)^j` is `β`-Hölder with constant `2`. -/
theorem holderWith_abs_rpow_mul_sign_pow {β : ℝ≥0} (hβ1 : β ≤ 1) (j : ℕ) :
    HolderWith 2 β (fun x : ℝ ↦ |x| ^ (β : ℝ) * Real.sign x ^ j) := by
  refine holderOnWith_univ.mp (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  have hxy : 0 ≤ |x - y| ^ (β : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hs : Real.sign x ^ j = Real.sign y ^ j
  · -- Equal signs: the Hölder bound of the cusp `|x| ^ β`.
    have hcusp := (holderWith_norm_rpow (E := ℝ) hβ1).dist_le x y
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, Real.norm_eq_abs,
      Real.norm_eq_abs] at hcusp
    rw [hs, ← sub_mul, abs_mul]
    calc |(|x| ^ (β : ℝ) - |y| ^ (β : ℝ))| * |Real.sign y ^ j|
        ≤ |(|x| ^ (β : ℝ) - |y| ^ (β : ℝ))| :=
          mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sign_pow_le_one y j)
      _ ≤ 2 * |x - y| ^ (β : ℝ) := by linarith
  · -- Different signs: `x` and `y` lie on opposite sides of `0`, so both are at most `|x - y|`.
    have hmul : x * y ≤ 0 := by
      by_contra h
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos (not_le.1 h) with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hs (by rw [Real.sign_of_pos hx, Real.sign_of_pos hy])
      · exact hs (by rw [Real.sign_of_neg hx, Real.sign_of_neg hy])
    have hx : |x| ≤ |x - y| := sq_le_sq.mp (by nlinarith)
    have hy : |y| ≤ |x - y| := sq_le_sq.mp (by nlinarith)
    calc |(|x| ^ (β : ℝ) * Real.sign x ^ j - |y| ^ (β : ℝ) * Real.sign y ^ j)|
        ≤ |(|x| ^ (β : ℝ) * Real.sign x ^ j)| + |(|y| ^ (β : ℝ) * Real.sign y ^ j)| :=
          abs_sub _ _
      _ ≤ |x| ^ (β : ℝ) + |y| ^ (β : ℝ) :=
          add_le_add (abs_abs_rpow_mul_sign_pow_le j x) (abs_abs_rpow_mul_sign_pow_le j y)
      _ ≤ |x - y| ^ (β : ℝ) + |x - y| ^ (β : ℝ) :=
          add_le_add (Real.rpow_le_rpow (abs_nonneg _) hx β.coe_nonneg)
            (Real.rpow_le_rpow (abs_nonneg _) hy β.coe_nonneg)
      _ = 2 * |x - y| ^ (β : ℝ) := by ring

end TauCeti
