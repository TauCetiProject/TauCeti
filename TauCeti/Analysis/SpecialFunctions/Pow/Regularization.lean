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
They provide convergence away from `a = 0` and domination for nonpositive exponents.

## Main declarations

* `TauCeti.tendsto_sq_add_rpow`: a quadratically regularized real power converges as the
  regularization parameter tends to zero from above.
* `TauCeti.sq_add_rpow_le`: for a nonpositive exponent, the regularized power is bounded by its
  value at zero.
* `TauCeti.rpow_norm_sq_add_neg_half_le`: `(‖x‖ ^ 2 + c) ^ (-1 / 2) ≤ ‖x‖⁻¹` for `c ≥ 0`.
* `TauCeti.continuous_rpow_norm_sq_add`: for `c > 0`, `x ↦ (‖x‖ ^ 2 + c) ^ q` is continuous.
* `TauCeti.continuousAt_zero_rpow_norm_sq_add_right`: for `x ≠ 0`, `c ↦ (‖x‖ ^ 2 + c) ^ q` is
  continuous at `c = 0`.
-/

public section

namespace TauCeti

open Filter Topology

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

/-! ### Regularizations of a norm -/

section Norm

variable {E : Type*} [NormedAddCommGroup E]

/-- The power `(‖x‖ ^ 2) ^ (-1 / 2)` is `‖x‖⁻¹`. -/
theorem rpow_norm_sq_neg_half (x : E) : (‖x‖ ^ 2) ^ (-(1 / 2) : ℝ) = ‖x‖⁻¹ := by
  rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- For `c ≥ 0` the regularized power `(‖x‖ ^ 2 + c) ^ (-1 / 2)` is at most `‖x‖⁻¹`. -/
theorem rpow_norm_sq_add_neg_half_le {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    (‖x‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) ≤ ‖x‖⁻¹ :=
  (sq_add_rpow_le (norm_ne_zero_iff.2 hx) hc (by norm_num)).trans_eq
    (by rw [add_zero, rpow_norm_sq_neg_half])

/-- For `c > 0` the map `x ↦ (‖x‖ ^ 2 + c) ^ q` is continuous, for every exponent `q`. -/
theorem continuous_rpow_norm_sq_add {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Continuous fun x : E => (‖x‖ ^ 2 + c) ^ q :=
  (by fun_prop : Continuous fun x : E => ‖x‖ ^ 2 + c).rpow_const fun x => Or.inl (by positivity)

/-- At a point `x ≠ 0` the power `(‖x‖ ^ 2 + c) ^ q` is continuous in `c` at `c = 0`. -/
theorem continuousAt_zero_rpow_norm_sq_add_right {x : E} (hx : x ≠ 0) (q : ℝ) :
    ContinuousAt (fun c : ℝ => (‖x‖ ^ 2 + c) ^ q) 0 :=
  (continuousAt_const.add continuousAt_id).rpow_const
    (Or.inl (by simp [hx]))

end Norm

end TauCeti
