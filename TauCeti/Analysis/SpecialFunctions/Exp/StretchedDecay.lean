/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Stretched exponential decay implies rapid power decay

For positive `c` and `α`, the stretched exponential `exp (-c * t ^ α)` decays faster
than every real power of `t` at infinity. Consequently an error bounded by this
exponential satisfies the power-decay hypotheses in `WeakFEPair` and hence in the
Mellin-transform construction of completed zeta and L-functions.

The estimate is obtained from Mathlib's `isLittleO_exp_neg_mul_rpow_atTop` by the
substitution `u = t ^ α`. No regularity of the dominated function is needed, and its
values may lie in any type carrying a norm.
-/

public section

open Asymptotics Filter

namespace TauCeti

/-- A stretched exponential with positive rate and exponent is little-o of every real
power at infinity. The power `r` may be negative. -/
theorem isLittleO_exp_neg_mul_rpow_rpow_atTop {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (r : ℝ) :
    (fun t : ℝ ↦ Real.exp (-c * t ^ α)) =o[atTop] fun t ↦ t ^ r := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (r / α)).comp_tendsto
    (tendsto_rpow_atTop hα)
  refine h.congr' .rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, ← Real.rpow_mul ht, mul_div_cancel₀ r hα.ne']

/-- Exponential decay supplies the rapid power bounds required by the Mellin principle:
`f = O(exp (-c t^α))` implies `f = O(t^r)` for every real `r`, when `c, α > 0`. -/
theorem isBigO_rpow_of_isBigO_exp_neg {E : Type*} [Norm E] {f : ℝ → E} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hf : f =O[atTop] fun t ↦ Real.exp (-c * t ^ α)) (r : ℝ) :
    f =O[atTop] fun t ↦ t ^ r :=
  (hf.trans_isLittleO (isLittleO_exp_neg_mul_rpow_rpow_atTop hc hα r)).isBigO

end TauCeti
