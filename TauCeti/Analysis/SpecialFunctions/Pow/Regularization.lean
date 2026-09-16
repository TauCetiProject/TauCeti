/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Real powers used in quadratic regularizations

This file records elementary facts about the regularization `(a ^ 2 + t) ^ e` as `t → 0⁺`.
They provide the algebraic identity at `t = 0`, convergence away from `a = 0`, and domination for
nonpositive exponents.

## Main declarations

* `TauCeti.sq_rpow_div_two`: taking the real power `s / 2` of a square gives the power `s` of a
  nonnegative base.
* `TauCeti.tendsto_sq_add_rpow`: a quadratically regularized real power converges as the
  regularization parameter tends to zero from above.
* `TauCeti.sq_add_rpow_le`: for a nonpositive exponent, the regularized power is bounded by its
  value at zero.
-/

public section

namespace TauCeti

open Filter Topology

/-- For a nonnegative real number `a`, taking the real power `s / 2` of `a ^ 2` gives `a ^ s`. -/
theorem sq_rpow_div_two {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : (a ^ 2) ^ (s / 2) = a ^ s := by
  rw [Real.rpow_div_two_eq_sqrt s (sq_nonneg a), Real.sqrt_sq ha]

/-- If `a ≠ 0`, then `(a ^ 2 + t) ^ e` converges to `(a ^ 2) ^ e` as `t → 0⁺`. -/
theorem tendsto_sq_add_rpow {a : ℝ} (ha : a ≠ 0) (e : ℝ) :
    Tendsto (fun t : ℝ ↦ (a ^ 2 + t) ^ e) (𝓝[>] 0) (𝓝 ((a ^ 2 + 0) ^ e)) :=
  ((continuousAt_const.add continuousAt_id).rpow_const
    (Or.inl (by simp [ha]))).tendsto.mono_left nhdsWithin_le_nhds

/-- If `a ≠ 0`, `t ≥ 0`, and `e ≤ 0`, then the regularized power `(a ^ 2 + t) ^ e` is bounded by
its value at `t = 0`. -/
theorem sq_add_rpow_le {a : ℝ} (ha : a ≠ 0) {t : ℝ} (ht : 0 ≤ t) {e : ℝ} (he : e ≤ 0) :
    (a ^ 2 + t) ^ e ≤ (a ^ 2 + 0) ^ e :=
  Real.rpow_le_rpow_of_nonpos (by simpa using sq_pos_of_ne_zero ha) (by linarith) he

end TauCeti
