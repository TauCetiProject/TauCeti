/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Scaled logarithms of extended nonnegative reals

At a nonnegative multiplier `e`, the scaled logarithm `x ↦ e * log x` from `ℝ≥0∞` to `EReal` is
monotone. Exponential rates `e * log (μ A)`, as in large deviations, are therefore monotone in the
set `A`. Along a filter, with multipliers `ε i`, the upper and lower limits of the scaled
logarithms `ε i * log (u i)` are the logarithms of the upper and lower limits of the powers
`u i ^ ε i`; this turns estimates of exponential rates into estimates in `ℝ≥0∞`. Since
`0 * log x = 0`, a negative limsup of `ε i * log (u i)` forces the multipliers `ε i` to be
eventually positive.

## Main results

* `TauCeti.ENNReal.coe_mul_log_monotone`: the scaled logarithm is monotone.
* `TauCeti.ENNReal.limsup_coe_mul_log`, `TauCeti.ENNReal.liminf_coe_mul_log`: the upper and lower
  limits of scaled logarithms as logarithms of upper and lower limits of powers.
* `TauCeti.ENNReal.limsup_coe_mul_log_mono`, `TauCeti.ENNReal.liminf_coe_mul_log_mono`: the upper
  and lower limits of scaled logarithms are monotone in the sequence.
* `TauCeti.ENNReal.eventually_pos_of_limsup_coe_mul_log_lt_zero`: a negative limsup of scaled
  logarithms forces eventually positive multipliers.
-/

public section

open Filter
open scoped ENNReal NNReal

namespace TauCeti.ENNReal

/-- At a nonnegative multiplier `e`, the scaled logarithm `x ↦ e * log x` is monotone. -/
theorem coe_mul_log_monotone (e : ℝ≥0) :
    Monotone fun x : ℝ≥0∞ => ((e : ℝ) : EReal) * ENNReal.log x :=
  fun _ _ h => mul_le_mul_of_nonneg_left (ENNReal.log_monotone h) (by exact_mod_cast e.coe_nonneg)

variable {ι : Type*} {l : Filter ι} {ε : ι → ℝ≥0}

/-- The upper limit of `ε i * log (u i)` is the logarithm of the upper limit of `u i ^ ε i`. -/
theorem limsup_coe_mul_log (u : ι → ℝ≥0∞) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l =
      ENNReal.log (limsup (fun i => u i ^ (ε i : ℝ)) l) := by
  simp_rw [← ENNReal.log_rpow]
  exact ENNReal.logOrderIso.limsup_apply.symm

/-- The lower limit of `ε i * log (u i)` is the logarithm of the lower limit of `u i ^ ε i`. -/
theorem liminf_coe_mul_log (u : ι → ℝ≥0∞) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l =
      ENNReal.log (liminf (fun i => u i ^ (ε i : ℝ)) l) := by
  simp_rw [← ENNReal.log_rpow]
  exact ENNReal.logOrderIso.liminf_apply.symm

/-- The upper limit of `ε i * log (u i)` is monotone in `u`: an eventual inequality `u ≤ v`
along `l` suffices. -/
theorem limsup_coe_mul_log_mono {u v : ι → ℝ≥0∞} (h : ∀ᶠ i in l, u i ≤ v i) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l ≤
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l :=
  limsup_le_limsup (h.mono fun i hi => coe_mul_log_monotone (ε i) hi)

/-- The lower limit of `ε i * log (u i)` is monotone in `u`: an eventual inequality `u ≤ v`
along `l` suffices. -/
theorem liminf_coe_mul_log_mono {u v : ι → ℝ≥0∞} (h : ∀ᶠ i in l, u i ≤ v i) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l :=
  liminf_le_liminf (h.mono fun i hi => coe_mul_log_monotone (ε i) hi)

/-- If the scaled logarithms `ε i * log (u i)` have negative limsup, the multipliers `ε i` are
eventually positive: at `ε i = 0` the scaled logarithm is `0 * log (u i) = 0`. -/
theorem eventually_pos_of_limsup_coe_mul_log_lt_zero {u : ι → ℝ≥0∞}
    (h : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l < 0) :
    ∀ᶠ i in l, 0 < ε i := by
  filter_upwards [eventually_lt_of_limsup_lt h] with i hi
  refine pos_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at hi

end TauCeti.ENNReal
