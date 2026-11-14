/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Finite convolution products of `L`-series

Mathlib's `ArithmeticFunction.LSeriesHasSum_mul`, `ArithmeticFunction.LSeries_mul'`,
`ArithmeticFunction.LSeries_mul` and `ArithmeticFunction.LSeriesSummable_mul` relate the binary
Dirichlet convolution product in `ArithmeticFunction ℂ` to pointwise multiplication of `L`-series.
This file extends those statements to finite `Finset` products, starting from the convolution
identity `1`, whose `L`-series is the constant `1`.

## Main results

* `ArithmeticFunction.LSeriesHasSum_one`: `(1 : ArithmeticFunction ℂ)` has `L`-series sum `1` at
  every `s : ℂ`.
* `ArithmeticFunction.LSeriesSummable_one`: `(1 : ArithmeticFunction ℂ)` has an absolutely
  convergent `L`-series at every `s : ℂ`.
* `ArithmeticFunction.LSeries_one`: `LSeries ↗(1 : ArithmeticFunction ℂ) s = 1`.
* `ArithmeticFunction.LSeriesHasSum_prod`: if each `f i` (`i ∈ t`) has `L`-series sum `a i` at
  `s`, their convolution product `∏ i ∈ t, f i` has `L`-series sum `∏ i ∈ t, a i`.
* `ArithmeticFunction.LSeriesSummable_prod`: finite convolution products preserve `LSeriesSummable`.
* `ArithmeticFunction.LSeries_prod'`, `ArithmeticFunction.LSeries_prod`: the `L`-series of a finite
  convolution product of `ℂ`-valued arithmetic functions is the product of their `L`-series.
-/

public section

open scoped LSeries.notation

namespace ArithmeticFunction

variable {ι : Type*}

/-- The multiplicative identity `1 : ArithmeticFunction ℂ` has `L`-series sum `1` everywhere. -/
protected theorem LSeriesHasSum_one (s : ℂ) : LSeriesHasSum ↗(1 : ArithmeticFunction ℂ) s 1 := by
  rw [one_eq_delta, LSeriesHasSum, funext (LSeries.term_delta s)]
  exact hasSum_ite_eq (1 : ℕ) (1 : ℂ)

/-- The multiplicative identity `1 : ArithmeticFunction ℂ` has an absolutely convergent `L`-series
at every `s : ℂ`. -/
protected theorem LSeriesSummable_one (s : ℂ) : LSeriesSummable ↗(1 : ArithmeticFunction ℂ) s :=
  (ArithmeticFunction.LSeriesHasSum_one s).LSeriesSummable

/-- The `L`-series of the convolution identity `1 : ArithmeticFunction ℂ` is identically `1`. -/
@[simp]
protected theorem LSeries_one (s : ℂ) : LSeries ↗(1 : ArithmeticFunction ℂ) s = 1 :=
  (ArithmeticFunction.LSeriesHasSum_one s).LSeries_eq

/-- **Finite convolution product of `LSeriesHasSum`.** If each `f i` (`i ∈ t`) has `L`-series sum
`a i` at `s`, then the Dirichlet convolution product `∏ i ∈ t, f i` has `L`-series sum
`∏ i ∈ t, a i` at `s`. -/
theorem LSeriesHasSum_prod {t : Finset ι} {f : ι → ArithmeticFunction ℂ} {a : ι → ℂ} {s : ℂ}
    (hf : ∀ i ∈ t, LSeriesHasSum ↗(f i) s (a i)) :
    LSeriesHasSum ↗(∏ i ∈ t, f i) s (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using ArithmeticFunction.LSeriesHasSum_one s
  | insert i t hit ih =>
    rw [Finset.prod_insert hit, Finset.prod_insert hit]
    exact LSeriesHasSum_mul (hf i (Finset.mem_insert_self i t))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- **Finite convolution product of `LSeriesSummable`.** If each `f i` (`i ∈ t`) has an absolutely
convergent `L`-series at `s`, so does `∏ i ∈ t, f i`. -/
theorem LSeriesSummable_prod {t : Finset ι} {f : ι → ArithmeticFunction ℂ} {s : ℂ}
    (hf : ∀ i ∈ t, LSeriesSummable ↗(f i) s) :
    LSeriesSummable ↗(∏ i ∈ t, f i) s :=
  (LSeriesHasSum_prod fun i hi ↦ (hf i hi).LSeriesHasSum).LSeriesSummable

/-- **The `L`-series of a finite convolution product** of `ℂ`-valued arithmetic functions is the
product of their `L`-series wherever each factor is `LSeriesSummable`. -/
theorem LSeries_prod' {t : Finset ι} {f : ι → ArithmeticFunction ℂ} {s : ℂ}
    (hf : ∀ i ∈ t, LSeriesSummable ↗(f i) s) :
    LSeries ↗(∏ i ∈ t, f i) s = ∏ i ∈ t, LSeries ↗(f i) s :=
  (LSeriesHasSum_prod fun i hi ↦ (hf i hi).LSeriesHasSum).LSeries_eq

/-- **The `L`-series of a finite convolution product** on the common half-plane of absolute
convergence of its factors. -/
theorem LSeries_prod {t : Finset ι} {f : ι → ArithmeticFunction ℂ} {s : ℂ}
    (hf : ∀ i ∈ t, LSeries.abscissaOfAbsConv ↗(f i) < s.re) :
    LSeries ↗(∏ i ∈ t, f i) s = ∏ i ∈ t, LSeries ↗(f i) s :=
  LSeries_prod' fun i hi ↦ LSeriesSummable_of_abscissaOfAbsConv_lt_re (hf i hi)

end ArithmeticFunction
