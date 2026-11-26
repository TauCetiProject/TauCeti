/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.OrderAtInfty
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.Analysis.Analytic.Order

/-!
# Analytic order and q-expansion order

The formal order of the q-expansion of an upper-half-plane function equals the analytic
order of its cusp function at zero, whenever that cusp function is analytic there. This
comparison applies both to periodic functions and to twisted functions used to construct
Laurent expansions at cusps, including the zero germ with infinite order.

Mathlib's `UpperHalfPlane.analyticOrderAt_eq_qExpansion_order` is the special case of a periodic,
holomorphic function bounded at infinity, where analyticity of the cusp function is automatic.
For such a function, Mathlib's `UpperHalfPlane.orderAtInfty_eq_qExpansion_order` relates the
order at `i ∞` to the order of the `q`-expansion; this file reads off the latter as a natural
number from the former.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft from which the order comparison is ported.
-/

public noncomputable section

open UpperHalfPlane

open scoped Manifold

namespace TauCeti

variable {h : ℝ}

/-- The order of the `q`-expansion equals the analytic order of the `cuspFunction` at `0`. -/
lemma qExpansion_order_eq_analyticOrderAt_cuspFunction {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    (qExpansion h f).order = analyticOrderAt (cuspFunction h f) 0 := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf, PowerSeries.nat_le_order_iff]
  simp [qExpansion_coeff, Nat.factorial_ne_zero]

/-- If an `h`-periodic holomorphic function bounded at `i ∞` has order `n / h` at `i ∞`, then
its `q`-expansion at period `h` vanishes to order exactly `n`. -/
lemma qExpansion_order_eq_of_orderAtInfty_eq {f : ℍ → ℂ} {n : ℕ} (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hf : orderAtInfty f = ((n / h : ℝ) : EReal)) :
    (qExpansion h f).order = n := by
  rw [orderAtInfty_eq_qExpansion_order hh hfper hfhol hfbdd,
    EReal.div_eq_iff (by simp) (by simp) (by simpa using hh.ne')] at hf
  have : ((qExpansion h f).order : EReal) = ((n : ℕ∞) : EReal) := by
    simpa [← EReal.coe_mul, hh.ne'] using hf
  exact_mod_cast this

end TauCeti
