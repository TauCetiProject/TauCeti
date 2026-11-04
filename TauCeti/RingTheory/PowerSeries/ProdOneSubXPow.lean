/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Products of the series `1 - X ^ d`

For a finite family of positive integers `d i`, the product `∏ i, (1 - X ^ d i)` is invertible in
`R⟦X⟧`, and its inverse `∏ i, (1 - X ^ d i)⁻¹` counts the solutions of `∑ i, e i * d i = n` in
natural numbers: its `n`-th coefficient is the number of `e : ι →₀ ℕ` of weight `n` for the
weights `d` (`Finsupp.weight d e = n`). This is the Hilbert series of a polynomial algebra whose
generators have the degrees `d i`.

Conversely, the product `∏ i, (1 - X ^ d i)` determines the multiset of the positive integers
`d i`, over any coefficient ring of characteristic zero. If every exponent is at least `n > 0`, the
coefficient of `X ^ n` in the product is minus the number of exponents equal to `n`; applied to
the least exponent occurring in either of two equal products, this lets one cancel a common
factor and induct. So the counting functions `n ↦ #{e | Finsupp.weight d e = n}` determine the
multiset of the weights `d i`.

## Main results

* `PowerSeries.coeff_prod_expand_mk_one`: the `n`-th coefficient of `∏ c ∈ s, (1 - X ^ m c)⁻¹`,
  written as the product of the expanded geometric series, is the size of the weighted
  antidiagonal.
* `PowerSeries.mk_natCard_weight_mul_prod_one_sub_X_pow`: the series counting the
  `e : ι →₀ ℕ` of each weight for positive weights `d` is the inverse of `∏ i, (1 - X ^ d i)`.
* `Multiset.eq_of_prod_map_one_sub_X_pow_eq`: the product `∏ d ∈ s, (1 - X ^ d)` over a
  multiset `s` of positive integers determines `s`, in characteristic zero.
* `Multiset.map_univ_eq_of_natCard_weight_eq`: the counting functions of the weights determine
  the multiset of the weights.
-/

public section

open Finset

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- **The expanded geometric series.** `∑ X ^ (p * k)` inverts `1 - X ^ p`. -/
theorem expand_mk_one_mul_one_sub_X_pow (p : ℕ) (hp : p ≠ 0) :
    expand p hp (mk 1 : R⟦X⟧) * (1 - X ^ p) = 1 := by
  simpa using congrArg (expand p hp) (mk_one_mul_one_sub_eq_one (S := R))

/-- The `n`-th coefficient of the product of the expanded geometric series `∑ X ^ (m c * k)`,
that is of `∏ c ∈ s, (1 - X ^ m c)⁻¹`, is the number of `l` supported in `s` with
`∑ c ∈ s, m c * l c = n`. -/
theorem coeff_prod_expand_mk_one {ι : Type*} (s : Finset ι) (m : ι → ℕ+) (n : ℕ) :
    coeff n (∏ c ∈ s, expand (m c) (m c).ne_zero (mk 1 : R⟦X⟧)) =
      #(s.weightedFinsuppAntidiag m n) := by
  simp [coeff_prod_expand]

/-- **Counting solutions of `∑ i, e i * d i = n`.** For positive weights `d i`, the series whose
`n`-th coefficient is the number of `e : ι →₀ ℕ` of weight `n` is the inverse of
`∏ i, (1 - X ^ d i)`. -/
theorem mk_natCard_weight_mul_prod_one_sub_X_pow {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i ≠ 0) :
    mk (fun n ↦ (Nat.card {e : ι →₀ ℕ // Finsupp.weight d e = n} : R)) *
      ∏ i, (1 - X ^ d i) = 1 := by
  set m : ι → ℕ+ := fun i ↦ ⟨d i, Nat.pos_of_ne_zero (hd i)⟩
  have hcard (n : ℕ) : Nat.card {e : ι →₀ ℕ // Finsupp.weight d e = n} =
      #(univ.weightedFinsuppAntidiag m n) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e ↦ ?_)
    rw [mem_weightedFinsuppAntidiag]
    simp [m, Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm]
  have hmk : mk (fun n ↦ (Nat.card {e : ι →₀ ℕ // Finsupp.weight d e = n} : R)) =
      ∏ i, expand (m i) (m i).ne_zero (mk 1 : R⟦X⟧) := by
    ext n
    rw [coeff_mk, hcard, coeff_prod_expand_mk_one]
  rw [hmk, ← prod_mul_distrib]
  exact prod_eq_one fun i _ ↦ expand_mk_one_mul_one_sub_X_pow (m i) _

/-- If every exponent in the multiset `s` is at least `n > 0`, the coefficient of `X ^ n` in
`∏ d ∈ s, (1 - X ^ d)` is minus the number of exponents equal to `n`. -/
theorem coeff_prod_map_one_sub_X_pow_of_le {n : ℕ} (hn : n ≠ 0) {s : Multiset ℕ}
    (hs : ∀ d ∈ s, n ≤ d) :
    coeff n (s.map fun d ↦ (1 - X ^ d : R⟦X⟧)).prod = -(s.count n : R) := by
  induction s using Multiset.induction_on with
  | empty => simp [coeff_one, hn]
  | cons a s ih =>
    have ha : n ≤ a := hs a (Multiset.mem_cons_self a s)
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, one_mul, map_sub, coeff_X_pow_mul',
      ih fun d hd ↦ hs d (Multiset.mem_cons_of_mem hd), Multiset.count_cons]
    rcases ha.eq_or_lt with rfl | ha
    · -- The remaining exponents are positive, so the product has constant coefficient `1`.
      have h0 : constantCoeff (s.map fun d ↦ (1 - X ^ d : R⟦X⟧)).prod = 1 := by
        rw [map_multiset_prod, Multiset.map_map]
        refine Multiset.prod_eq_one fun x hx ↦ ?_
        obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 hx
        have : d ≠ 0 := by have := hs d (Multiset.mem_cons_of_mem hd); omega
        simp [this]
      simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_zero_eq_constantCoeff, h0]
      push_cast
      ring
    · simp [ha.not_ge, ha.ne]

end PowerSeries

namespace Multiset

open PowerSeries

variable {R : Type*} [CommRing R] [CharZero R]

/-- **The exponents of `∏ (1 - X ^ d)`.** Over a coefficient ring of characteristic zero, the
product `∏ d ∈ s, (1 - X ^ d)` determines the multiset `s` of positive integers. -/
theorem eq_of_prod_map_one_sub_X_pow_eq {s t : Multiset ℕ} (hs : 0 ∉ s) (ht : 0 ∉ t)
    (h : (s.map fun d ↦ (1 - X ^ d : R⟦X⟧)).prod = (t.map fun d ↦ (1 - X ^ d : R⟦X⟧)).prod) :
    s = t := by
  induction hst : card s + card t using Nat.strong_induction_on generalizing s t with
  | _ k ih =>
  subst hst
  rcases (s + t).empty_or_exists_mem with h0 | ⟨a, ha⟩
  · rw [add_eq_zero] at h0
    rw [h0.1, h0.2]
  -- Compare the coefficients of `X ^ n` for the least exponent `n` occurring in `s` or `t`.
  classical
  obtain ⟨n, hn, hle⟩ : ∃ n ∈ s + t, ∀ d ∈ s + t, n ≤ d :=
    ⟨Nat.find ⟨a, ha⟩, Nat.find_spec ⟨a, ha⟩, fun _ hd ↦ Nat.find_min' _ hd⟩
  have hn0 : n ≠ 0 := by
    rintro hn0
    rw [hn0, mem_add] at hn
    exact hn.elim hs ht
  have hcount : s.count n = t.count n := by
    have := congrArg (coeff n) h
    rwa [coeff_prod_map_one_sub_X_pow_of_le hn0 fun d hd ↦ hle d (mem_add.2 (.inl hd)),
      coeff_prod_map_one_sub_X_pow_of_le hn0 fun d hd ↦ hle d (mem_add.2 (.inr hd)), neg_inj,
      Nat.cast_inj] at this
  -- So `n` lies in both `s` and `t`; cancel the invertible factor `1 - X ^ n`.
  have hns : n ∈ s := by
    rcases mem_add.1 hn with hn | hn
    · exact hn
    · rw [← count_pos, hcount]
      exact count_pos.2 hn
  have hnt : n ∈ t := by rwa [← count_pos, ← hcount, count_pos]
  obtain ⟨s', rfl⟩ := exists_cons_of_mem hns
  obtain ⟨t', rfl⟩ := exists_cons_of_mem hnt
  have hunit : IsUnit (1 - X ^ n : R⟦X⟧) := isUnit_iff_constantCoeff.2 (by simp [hn0])
  rw [map_cons, map_cons, prod_cons, prod_cons, hunit.mul_right_inj] at h
  rw [ih (card s' + card t') (by simp; omega) (fun h0 ↦ hs (mem_cons_of_mem h0))
    (fun h0 ↦ ht (mem_cons_of_mem h0)) h rfl]

/-- **Weights from their counting functions.** If two finite families of positive weights have
the same number of `e` of each weight `n`, then they have the same multiset of weights. -/
theorem map_univ_eq_of_natCard_weight_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ι → ℕ}
    {d' : κ → ℕ} (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0)
    (h : ∀ n, Nat.card {e : ι →₀ ℕ // Finsupp.weight d e = n} =
      Nat.card {e : κ →₀ ℕ // Finsupp.weight d' e = n}) :
    Finset.univ.val.map d = Finset.univ.val.map d' := by
  refine eq_of_prod_map_one_sub_X_pow_eq (R := ℤ) (by simpa using hd) (by simpa using hd') ?_
  have h₁ := mk_natCard_weight_mul_prod_one_sub_X_pow (R := ℤ) hd
  have h₂ := mk_natCard_weight_mul_prod_one_sub_X_pow (R := ℤ) hd'
  simp_rw [h] at h₁
  -- Both products are inverse to the same series.
  simpa [map_map, Function.comp_def] using left_inv_eq_right_inv ((mul_comm _ _).trans h₁) h₂

end Multiset
