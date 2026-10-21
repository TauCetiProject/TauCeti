/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Products of expanded power series

For power series `f i` and positive integers `d i`, the product `∏ i ∈ s, f i (X ^ d i)` of the
expanded series `PowerSeries.expand (d i) _ (f i)` has `n`-th coefficient

`∑ l, ∏ i ∈ s, [X ^ l i] f i`,

the sum running over the multiplicity functions `l` supported on `s` with `∑ i ∈ s, l i * d i = n`.
This is the generating-function form of independent-component expansion: the factor `i` occurs
with multiplicity `l i` and contributes `l i * d i` to the total degree.

## Main results

* `PowerSeries.coeff_prod_expand`: the coefficients of a finite product of expanded series, as a
  sum over multiplicity functions.
* `PowerSeries.X_pow_dvd_expand_sub_C_constantCoeff`: `f (X ^ p) - f(0)` is divisible by `X ^ p`.
-/

public section

open Finset

namespace PowerSeries

variable {R ι : Type*} [CommRing R]

/-- **Coefficients of a product of expanded series.** The `n`-th coefficient of
`∏ i ∈ s, f i (X ^ d i)` is the sum, over all multiplicity functions `l` supported on `s` with
`∑ i ∈ s, l i * d i = n`, of `∏ i ∈ s, coeff (l i) (f i)`. The bound `l i ≤ n` in the index set
is automatic, since every `d i` is positive. -/
theorem coeff_prod_expand (s : Finset ι) (d : ι → ℕ) (hd : ∀ i, d i ≠ 0)
    (f : ι → R⟦X⟧) (n : ℕ) :
    coeff n (∏ i ∈ s, expand (d i) (hd i) (f i)) =
      ∑ l ∈ s.finsupp (fun _ ↦ range (n + 1)) with ∑ i ∈ s, l i * d i = n,
        ∏ i ∈ s, coeff (l i) (f i) := by
  classical
  rw [coeff_prod]
  -- A multiplicity function `l` corresponds to the degree distribution `i ↦ l i * d i`; the
  -- remaining degree distributions contribute `0`, since some `d i` does not divide their value.
  let e : (ι →₀ ℕ) → ι →₀ ℕ := fun l ↦
    Finsupp.onFinset l.support (fun i ↦ l i * d i) fun i hi ↦ by
      simpa using left_ne_zero_of_mul hi
  have he (l : ι →₀ ℕ) (i : ι) : e l i = l i * d i := Finsupp.onFinset_apply ..
  refine (sum_of_injOn e ?_ ?_ ?_ ?_).symm
  · intro l _ l' _ h
    ext i
    simpa [he, hd i] using DFunLike.congr_fun h i
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq, mem_finsupp_iff] at hl
    refine mem_finsuppAntidiag.2 ⟨by simpa [he] using hl.2, fun i hi ↦ ?_⟩
    rw [Finsupp.mem_support_iff, he] at hi
    exact hl.1.1 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hi))
  · intro k hk hke
    rw [mem_finsuppAntidiag] at hk
    by_cases hdvd : ∀ i ∈ s, d i ∣ k i
    swap
    · push Not at hdvd
      obtain ⟨i, hi, hndvd⟩ := hdvd
      exact prod_eq_zero hi (coeff_expand_of_not_dvd _ _ _ hndvd)
    exfalso
    refine hke ⟨Finsupp.onFinset k.support (fun i ↦ k i / d i) fun i hi ↦ ?_, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff]
      rintro h
      simp [h] at hi
    · have hle (i : ι) (hi : i ∈ s) : k i / d i ≤ n :=
        (Nat.div_le_self _ _).trans (hk.1 ▸ single_le_sum (by simp) hi)
      simp only [coe_filter, Set.mem_ofPred_eq, mem_finsupp_iff, Finsupp.onFinset_apply,
        mem_range, Nat.lt_succ_iff]
      refine ⟨⟨fun i hi ↦ hk.2 (by simpa using Finsupp.support_onFinset_subset hi), hle⟩, ?_⟩
      rw [← hk.1]
      exact sum_congr rfl fun i hi ↦ Nat.div_mul_cancel (hdvd i hi)
    · ext i
      rw [he, Finsupp.onFinset_apply]
      by_cases hi : i ∈ s
      · exact Nat.div_mul_cancel (hdvd i hi)
      · have : k i = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hi (hk.2 h)
        simp [this]
  · intro l _
    refine prod_congr rfl fun i _ ↦ ?_
    rw [he, mul_comm, coeff_expand_mul]

/-- An expanded series `f (X ^ p)` agrees with its constant coefficient modulo `X ^ p`. -/
theorem X_pow_dvd_expand_sub_C_constantCoeff (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    X ^ p ∣ expand p hp f - C (constantCoeff f) := by
  obtain ⟨g, hg⟩ := X_dvd_iff.2 (by simp : constantCoeff (f - C (constantCoeff f)) = 0)
  refine ⟨expand p hp g, ?_⟩
  rw [← expand_C p hp, ← map_sub, hg, map_mul, expand_X]

end PowerSeries
