/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Real powers of a shifted squared norm

For `c > 0` the map `x ↦ (‖x‖ ^ 2 + c) ^ q` is a continuous regularisation of the norm power
`‖x‖ ^ (2 q)`. As `c → 0` it converges to that power at every `x ≠ 0`, and for `c ≥ 0` the
power `q = -1 / 2` is dominated by `‖x‖⁻¹`.

## Main declarations

* `TauCeti.rpow_norm_sq_add_neg_half_le`: `(‖x‖ ^ 2 + c) ^ (-1 / 2) ≤ ‖x‖⁻¹` for `c ≥ 0`.
* `TauCeti.continuous_rpow_norm_sq_add`: continuity in `x` for `c > 0`.
* `TauCeti.continuousAt_rpow_norm_sq_add`: continuity in `c` at `c = 0`, for `x ≠ 0`.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- For `c ≥ 0` the regularised power `(‖x‖ ^ 2 + c) ^ (-1 / 2)` is at most `‖x‖⁻¹`. -/
theorem rpow_norm_sq_add_neg_half_le {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    (‖x‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) ≤ ‖x‖⁻¹ := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  calc (‖x‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) ≤ (‖x‖ ^ 2) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    _ = ‖x‖⁻¹ := by
        rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx'.le]

/-- For `c > 0` the map `x ↦ (‖x‖ ^ 2 + c) ^ q` is continuous, for every exponent `q`. -/
theorem continuous_rpow_norm_sq_add {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Continuous fun x : E => (‖x‖ ^ 2 + c) ^ q :=
  (by fun_prop : Continuous fun x : E => ‖x‖ ^ 2 + c).rpow_const fun x => Or.inl (by positivity)

/-- At a point `x ≠ 0` the power `(‖x‖ ^ 2 + c) ^ q` is continuous in `c` at `c = 0`. -/
theorem continuousAt_rpow_norm_sq_add {x : E} (hx : x ≠ 0) (q : ℝ) :
    ContinuousAt (fun c : ℝ => (‖x‖ ^ 2 + c) ^ q) 0 := by
  have h : ‖x‖ ^ 2 + 0 ≠ 0 := by have := norm_pos_iff.2 hx; positivity
  exact (continuous_const.add continuous_id : Continuous fun c : ℝ => ‖x‖ ^ 2 + c).continuousAt
    |>.rpow_const (Or.inl h)

end TauCeti
