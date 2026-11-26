/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of real powers

For `0 ≤ p ≤ 1` the power `t ↦ t ^ p` is `p`-Hölder on `[0, ∞)` with constant one:
`|a ^ p - b ^ p| ≤ |a - b| ^ p` for `a, b ≥ 0`. This is the subadditivity
`(a + b) ^ p ≤ a ^ p + b ^ p` of Mathlib's `Real.rpow_add_le_add_rpow`, applied to `b` and
`a - b`. It is the estimate showing that cone-point functions such as `‖z‖ ^ p` are `p`-Hölder.

The odd power `|x| ^ (p - 1) * x = sign(x) |x| ^ p` is `p`-Hölder on all of `ℝ` with constant
`2` (`Real.holderWith_abs_rpow_sub_one_mul_self`): on each half-line it is `± |x| ^ p`, and for
`x, y` of opposite signs both `|x|` and `|y|` are at most `|x - y|`. It is the derivative of
`|x| ^ (p + 1) / (p + 1)`, which is therefore `C^{1,p}`.
-/

public section

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

/-- The odd power `x ↦ |x| ^ (p - 1) * x`, that is `sign(x) |x| ^ p`, is `p`-Hölder on `ℝ` with
constant `2`, for `0 < p ≤ 1`. -/
theorem holderWith_abs_rpow_sub_one_mul_self {p : NNReal} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    HolderWith 2 p (fun x : ℝ ↦ |x| ^ ((p : ℝ) - 1) * x) := by
  have hp₀' : (0 : ℝ) < p := NNReal.coe_pos.2 hp₀
  -- On `[0, ∞)` the odd power is `x ^ p`.
  have hnonneg {x : ℝ} (hx : 0 ≤ x) : |x| ^ ((p : ℝ) - 1) * x = x ^ (p : ℝ) := by
    rw [abs_of_nonneg hx, ← rpow_eq_rpow_sub_one_mul hx hp₀'.ne']
  -- The bound for `x ≥ 0`; the case `x ≤ 0` follows since the function is odd.
  have key : ∀ x y : ℝ, 0 ≤ x →
      |(|x| ^ ((p : ℝ) - 1) * x) - |y| ^ ((p : ℝ) - 1) * y| ≤ 2 * |x - y| ^ (p : ℝ) := by
    intro x y hx
    have h0 : 0 ≤ |x - y| ^ (p : ℝ) := by positivity
    rw [hnonneg hx]
    rcases le_total 0 y with hy | hy
    · rw [hnonneg hy]
      linarith [abs_rpow_sub_rpow_le hx hy hp₀'.le (by exact_mod_cast hp₁)]
    · have hy' : |y| ^ ((p : ℝ) - 1) * y = -((-y) ^ (p : ℝ)) := by
        rw [← hnonneg (neg_nonneg.2 hy), abs_neg]
        ring
      have hxy : |x - y| = x - y := abs_of_nonneg (by linarith)
      have h1 : x ^ (p : ℝ) ≤ |x - y| ^ (p : ℝ) := rpow_le_rpow hx (by linarith) hp₀'.le
      have h2 : (-y) ^ (p : ℝ) ≤ |x - y| ^ (p : ℝ) :=
        rpow_le_rpow (by linarith) (by linarith) hp₀'.le
      rw [hy', sub_neg_eq_add, abs_of_nonneg (add_nonneg (rpow_nonneg hx _)
        (rpow_nonneg (neg_nonneg.2 hy) _))]
      linarith
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)
  simp only [dist_eq, NNReal.coe_ofNat]
  rcases le_total 0 x with hx | hx
  · exact key x y hx
  · have h := key (-x) (-y) (neg_nonneg.2 hx)
    rw [abs_neg x, abs_neg y, show -x - -y = -(x - y) by ring, abs_neg] at h
    rwa [show (|x| ^ ((p : ℝ) - 1) * -x) - |y| ^ ((p : ℝ) - 1) * -y =
      -((|x| ^ ((p : ℝ) - 1) * x) - |y| ^ ((p : ℝ) - 1) * y) by ring, abs_neg] at h

end Real
