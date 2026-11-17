/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution

/-!
# L-series of finite Dirichlet-convolution products

This file extends Mathlib's binary convolution lemmas `ArithmeticFunction.LSeriesHasSum_mul`,
`ArithmeticFunction.LSeriesSummable_mul`, `ArithmeticFunction.LSeries_mul'`, and
`ArithmeticFunction.LSeries_mul` to finite products `∏ i ∈ s, f i` of `ℂ`-valued arithmetic
functions.

## Main results

* `ArithmeticFunction.LSeriesHasSum_one`: the `LSeries` of `(1 : ArithmeticFunction ℂ)` sums to
  `1` at every complex number `s`.
* `ArithmeticFunction.LSeriesHasSum_finset_prod`: if each `LSeries ↗(f i) z` sums to `a i`, then
  `LSeries ↗(∏ i ∈ s, f i) z` sums to `∏ i ∈ s, a i`.
* `ArithmeticFunction.LSeriesSummable_finset_prod`: summability of a finite convolution product.
* `ArithmeticFunction.LSeries_finset_prod'`:
  `LSeries ↗(∏ i ∈ s, f i) z = ∏ i ∈ s, LSeries ↗(f i) z` when each factor is summable.
* `ArithmeticFunction.LSeries_finset_prod`: the same identity in the common half-plane of absolute
  convergence.
-/

public section

open scoped LSeries.notation

namespace ArithmeticFunction

/-- The `LSeries` of the convolution identity `(1 : ArithmeticFunction ℂ)` has sum `1` at every
`s : ℂ`. -/
theorem LSeriesHasSum_one (s : ℂ) : LSeriesHasSum ↗(1 : ArithmeticFunction ℂ) s 1 := by
  rw [LSeriesHasSum]
  convert hasSum_ite_eq (1 : ℕ) (1 : ℂ) with n
  by_cases hn : n = 1
  · subst hn; simp [LSeries.term]
  · simp [LSeries.term, ArithmeticFunction.one_apply_ne hn, hn]

/-- The `LSeries` of a finite Dirichlet-convolution product of `ℂ`-valued arithmetic functions
converges to the product of their sums whenever every factor converges. -/
theorem LSeriesHasSum_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {a : ι → ℂ} {z : ℂ} (hf : ∀ i ∈ s, LSeriesHasSum ↗(f i) z (a i)) :
    LSeriesHasSum ↗(∏ i ∈ s, f i) z (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using LSeriesHasSum_one z
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact LSeriesHasSum_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- The `LSeries` of a finite Dirichlet-convolution product is summable when every factor is
summable. -/
theorem LSeriesSummable_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {z : ℂ} (hf : ∀ i ∈ s, LSeriesSummable ↗(f i) z) :
    LSeriesSummable ↗(∏ i ∈ s, f i) z :=
  (LSeriesHasSum_finset_prod fun i hi ↦ (hf i hi).LSeriesHasSum).LSeriesSummable

/-- The `LSeries` of a finite Dirichlet-convolution product equals the product of the individual
`LSeries`, assuming each factor is summable. -/
theorem LSeries_finset_prod' {ι : Type*} {s : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {z : ℂ} (hf : ∀ i ∈ s, LSeriesSummable ↗(f i) z) :
    LSeries ↗(∏ i ∈ s, f i) z = ∏ i ∈ s, LSeries ↗(f i) z :=
  (LSeriesHasSum_finset_prod fun i hi ↦ (hf i hi).LSeriesHasSum).LSeries_eq

/-- The `LSeries` of a finite Dirichlet-convolution product equals the product of the individual
`LSeries` in the common half-plane of absolute convergence. -/
theorem LSeries_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ArithmeticFunction ℂ}
    {z : ℂ} (hf : ∀ i ∈ s, LSeries.abscissaOfAbsConv ↗(f i) < z.re) :
    LSeries ↗(∏ i ∈ s, f i) z = ∏ i ∈ s, LSeries ↗(f i) z :=
  LSeries_finset_prod' fun i hi ↦ LSeriesSummable_of_abscissaOfAbsConv_lt_re (hf i hi)

end ArithmeticFunction
