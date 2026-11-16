/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Finite Dirichlet convolution products of `L`-series

Mathlib's `Mathlib.NumberTheory.LSeries.Convolution` proves that the `L`-series of the Dirichlet
convolution of two arithmetic functions equals the product of their `L`-series wherever both
converge absolutely (`ArithmeticFunction.LSeriesHasSum_mul`, `ArithmeticFunction.LSeries_mul'`,
`ArithmeticFunction.LSeriesSummable_mul`). This file extends those identities to the convolution
unit `1 : ArithmeticFunction ℂ` and to arbitrary finite products `∏ i ∈ t, f i`.

## Main results

* `ArithmeticFunction.LSeriesHasSum_one`: the `L`-series of `1 : ArithmeticFunction ℂ` converges
  absolutely to `1` at every complex number `s`.
* `ArithmeticFunction.LSeriesHasSum_finsetProd`: if each `f i` (`i ∈ t`) has an absolutely
  convergent `L`-series with sum `a i`, then `∏ i ∈ t, f i` has an absolutely convergent `L`-series
  with sum `∏ i ∈ t, a i`.
* `ArithmeticFunction.LSeriesSummable_finsetProd`: a finite Dirichlet convolution product of
  `LSeriesSummable` arithmetic functions is `LSeriesSummable`.
* `ArithmeticFunction.LSeries_finsetProd`: the `L`-series of a finite Dirichlet convolution product
  equals the product of the individual `L`-series wherever each factor is `LSeriesSummable`.
-/

public section

open scoped LSeries.notation

namespace ArithmeticFunction

/-- The `L`-series of the Dirichlet convolution unit `1 : ArithmeticFunction ℂ` converges
absolutely to `1` at every complex number `s`. -/
protected theorem LSeriesHasSum_one (s : ℂ) : LSeriesHasSum ↗(1 : ArithmeticFunction ℂ) s 1 := by
  rw [LSeriesHasSum]
  convert hasSum_ite_eq (1 : ℕ) (1 : ℂ) using 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero]
  · rcases eq_or_ne n 1 with rfl | hn1
    · simp [LSeries.term_of_ne_zero]
    · simp [LSeries.term_of_ne_zero hn0, ArithmeticFunction.one_apply, hn1]

/-- The `L`-series of the Dirichlet convolution unit `1 : ArithmeticFunction ℂ` is summable at
every complex number `s`. -/
@[simp]
protected theorem LSeriesSummable_one (s : ℂ) : LSeriesSummable ↗(1 : ArithmeticFunction ℂ) s :=
  (ArithmeticFunction.LSeriesHasSum_one s).LSeriesSummable

/-- The `L`-series of the Dirichlet convolution unit `1 : ArithmeticFunction ℂ` equals `1` at every
complex number `s`. -/
@[simp]
protected theorem LSeries_one (s : ℂ) : LSeries ↗(1 : ArithmeticFunction ℂ) s = 1 :=
  (ArithmeticFunction.LSeriesHasSum_one s).LSeries_eq

/-- The `L`-series of a finite Dirichlet convolution product converges absolutely to the product of
the individual sums whenever each factor has an absolutely convergent `L`-series. -/
theorem LSeriesHasSum_finsetProd {ι : Type*} {t : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {s : ℂ} {a : ι → ℂ} (hf : ∀ i ∈ t, LSeriesHasSum ↗(f i) s (a i)) :
    LSeriesHasSum ↗(∏ i ∈ t, f i) s (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using ArithmeticFunction.LSeriesHasSum_one s
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact LSeriesHasSum_mul (hf i (Finset.mem_insert_self i t))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- A finite Dirichlet convolution product of `LSeriesSummable` arithmetic functions is
`LSeriesSummable`. -/
theorem LSeriesSummable_finsetProd {ι : Type*} {t : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {s : ℂ} (hf : ∀ i ∈ t, LSeriesSummable ↗(f i) s) :
    LSeriesSummable ↗(∏ i ∈ t, f i) s :=
  (LSeriesHasSum_finsetProd fun i hi ↦ (hf i hi).LSeriesHasSum).LSeriesSummable

/-- The `L`-series of a finite Dirichlet convolution product equals the product of the individual
`L`-series wherever each factor is `LSeriesSummable`. -/
theorem LSeries_finsetProd {ι : Type*} {t : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {s : ℂ} (hf : ∀ i ∈ t, LSeriesSummable ↗(f i) s) :
    LSeries ↗(∏ i ∈ t, f i) s = ∏ i ∈ t, LSeries ↗(f i) s :=
  (LSeriesHasSum_finsetProd fun i hi ↦ (hf i hi).LSeriesHasSum).LSeries_eq

end ArithmeticFunction
