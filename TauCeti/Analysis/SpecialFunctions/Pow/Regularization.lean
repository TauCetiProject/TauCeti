/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Real powers used in quadratic regularizations

This file records elementary facts about the regularization `(a ^ 2 + t) ^ e` as `t → 0⁺`.
They provide convergence away from `a = 0` and domination for nonpositive exponents.
For a positive regularization parameter the corresponding powers of a norm are continuous,
including at the origin.

## Main declarations

* `TauCeti.continuousAt_sq_add_rpow`: for `a ≠ 0`, the regularized power is continuous in the
  regularization parameter at zero.
* `TauCeti.tendsto_sq_add_rpow`: a quadratically regularized real power converges as the
  regularization parameter tends to zero from above.
* `TauCeti.sq_add_rpow_le`: for a nonpositive exponent, the regularized power is bounded by its
  value at zero.
* `TauCeti.norm_sq_add_rpow_div_two_le`: `(‖x‖ ^ 2 + c) ^ (q / 2) ≤ ‖x‖ ^ q` for `c ≥ 0`,
  `q ≤ 0` and `x ≠ 0`.
* `TauCeti.continuous_norm_sq_add_rpow`: for `c > 0`, `x ↦ (‖x‖ ^ 2 + c) ^ q` is continuous.
-/

public section

namespace TauCeti

open Filter Topology

/-- If `a ≠ 0`, then `t ↦ (a ^ 2 + t) ^ e` is continuous at `t = 0`. -/
theorem continuousAt_sq_add_rpow {a : ℝ} (ha : a ≠ 0) (e : ℝ) :
    ContinuousAt (fun t : ℝ ↦ (a ^ 2 + t) ^ e) 0 :=
  (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by simp [ha]))

/-- If `a ≠ 0`, then `(a ^ 2 + t) ^ e` converges to `(a ^ 2) ^ e` as `t → 0⁺`. -/
theorem tendsto_sq_add_rpow {a : ℝ} (ha : a ≠ 0) (e : ℝ) :
    Tendsto (fun t : ℝ ↦ (a ^ 2 + t) ^ e) (𝓝[>] 0) (𝓝 ((a ^ 2 + 0) ^ e)) :=
  (continuousAt_sq_add_rpow ha e).tendsto.mono_left nhdsWithin_le_nhds

/-- If `a ≠ 0`, `t ≥ 0`, and `e ≤ 0`, then the regularized power `(a ^ 2 + t) ^ e` is bounded by
its value at `t = 0`. -/
theorem sq_add_rpow_le {a : ℝ} (ha : a ≠ 0) {t : ℝ} (ht : 0 ≤ t) {e : ℝ} (he : e ≤ 0) :
    (a ^ 2 + t) ^ e ≤ (a ^ 2 + 0) ^ e :=
  Real.rpow_le_rpow_of_nonpos (by simpa using sq_pos_of_ne_zero ha) (by linarith) he

/-! ### Regularizations of a norm -/

section Norm

/-- For `c ≥ 0`, `q ≤ 0` and `x ≠ 0`, the regularized power `(‖x‖ ^ 2 + c) ^ (q / 2)` is at most
`‖x‖ ^ q`. -/
theorem norm_sq_add_rpow_div_two_le {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 ≤ c)
    {x : E} (hx : x ≠ 0) {q : ℝ} (hq : q ≤ 0) : (‖x‖ ^ 2 + c) ^ (q / 2) ≤ ‖x‖ ^ q :=
  (sq_add_rpow_le (norm_ne_zero_iff.2 hx) hc (by linarith)).trans_eq
    (by rw [add_zero, Real.sq_rpow_div_two (norm_nonneg x)])

/-- For `c > 0` the map `x ↦ (‖x‖ ^ 2 + c) ^ q` is continuous, for every exponent `q`. -/
theorem continuous_norm_sq_add_rpow {E : Type*} [SeminormedAddCommGroup E] {c : ℝ} (hc : 0 < c)
    (q : ℝ) : Continuous fun x : E => (‖x‖ ^ 2 + c) ^ q :=
  (by fun_prop : Continuous fun x : E => ‖x‖ ^ 2 + c).rpow_const fun x => Or.inl (by positivity)

end Norm

end TauCeti
