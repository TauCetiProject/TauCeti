/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.LaurentSeries

/-!
# The real order valuation on Laurent series

For a domain `R`, the order of vanishing `ord = HahnSeries.orderTop` on `R⸨X⸩`, with
`ord(0) = ⊤` and `ord(X) = 1`, becomes a real additive valuation `LaurentSeries.realAddVal R`
after the inclusion `ℤ → ℝ`. Real values are what the general Newton-polygon API expects of
coefficient heights, so this lets it apply to polynomials over `R⸨X⸩`.

## Main definitions

* `LaurentSeries.realAddVal R`: the real additive valuation `ord` on `R⸨X⸩`.

## Main results

* `LaurentSeries.realAddVal_apply`: `realAddVal R f` is `f.orderTop` cast to the reals.
* `LaurentSeries.realAddVal_eq_top_iff`: only zero has infinite valuation.
* `LaurentSeries.realAddVal_le_of_coeff_ne_zero`: a nonzero coefficient at `k` bounds the
  valuation by `k`.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace LaurentSeries

variable (R : Type*) [Ring R] [IsDomain R]

/-- The order of vanishing `ord = orderTop` on `R⸨X⸩` as a real additive valuation: a nonzero
Laurent series of order `n` has valuation `n`, and zero has valuation `⊤`. -/
noncomputable def realAddVal : AddValuation R⸨X⸩ (WithTop ℝ) :=
  (HahnSeries.addVal ℤ R).map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h => Int.cast_le.mpr h }
    rfl

variable {R}

/-- The real valuation of a Laurent series is its order, cast to the reals. -/
@[simp]
theorem realAddVal_apply (f : R⸨X⸩) :
    realAddVal R f = f.orderTop.map ((↑) : ℤ → ℝ) := by
  rw [← HahnSeries.addVal_apply (Γ := ℤ)]
  -- By construction, `realAddVal R` is `HahnSeries.addVal ℤ R` followed by `WithTop.map`.
  rfl

/-- The real valuation of a nonzero Laurent series is its order. -/
theorem realAddVal_of_ne_zero {f : R⸨X⸩} (hf : f ≠ 0) :
    realAddVal R f = ((f.order : ℝ) : WithTop ℝ) := by
  rw [realAddVal_apply, ← order_eq_orderTop_of_ne_zero hf, WithTop.map_coe]

/-- Only the zero Laurent series has infinite valuation. -/
theorem realAddVal_eq_top_iff {f : R⸨X⸩} : realAddVal R f = ⊤ ↔ f = 0 := by
  simp

/-- The monomial `r Xⁿ`, for `r ≠ 0`, has valuation `n`; in particular `X` has valuation one. -/
theorem realAddVal_single (n : ℤ) {r : R} (hr : r ≠ 0) :
    realAddVal R (single n r) = ((n : ℝ) : WithTop ℝ) := by
  rw [realAddVal_apply, orderTop_single hr, WithTop.map_coe]

/-- A Laurent series with a nonzero coefficient at `k` has valuation at most `k`. -/
theorem realAddVal_le_of_coeff_ne_zero {f : R⸨X⸩} {k : ℤ} (hk : f.coeff k ≠ 0) :
    realAddVal R f ≤ ((k : ℝ) : WithTop ℝ) := by
  rw [realAddVal_of_ne_zero (ne_zero_of_coeff_ne_zero hk), WithTop.coe_le_coe, Int.cast_le]
  exact order_le_of_coeff_ne_zero hk

end LaurentSeries
