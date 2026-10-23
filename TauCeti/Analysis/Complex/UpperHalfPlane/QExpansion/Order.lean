/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.Analysis.Analytic.Order

/-!
# Analytic order and q-expansion order

The formal order of the q-expansion of an upper-half-plane function equals the analytic
order of its cusp function at zero, whenever that cusp function is analytic there. This
comparison applies both to periodic functions and to twisted functions used to construct
Laurent expansions at cusps, including the zero germ with infinite order.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft from which the order comparison is ported.
-/

public noncomputable section

open UpperHalfPlane

namespace TauCeti

variable {h : ℝ}

/-- The order of the `q`-expansion equals the analytic order of the `cuspFunction` at `0`. -/
lemma qExpansion_order_eq_analyticOrderAt_cuspFunction {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    (qExpansion h f).order = analyticOrderAt (cuspFunction h f) 0 := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  refine ⟨fun H i hi ↦ ?_, fun H ↦ PowerSeries.nat_le_order _ _ fun i hi ↦ ?_⟩
  · have hcoeff : (qExpansion h f).coeff i = 0 :=
      PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (mod_cast hi) H)
    rw [qExpansion_coeff] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (inv_ne_zero (mod_cast Nat.factorial_ne_zero i))
  · rw [qExpansion_coeff, H i hi, mul_zero]

end TauCeti
