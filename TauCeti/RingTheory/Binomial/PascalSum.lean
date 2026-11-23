/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Pascal sum identities for generalized binomial coefficients

Summing Pascal's recurrence `Ring.choose (m + 1) (i + 1) = Ring.choose m i + Ring.choose m (i + 1)`
and its alternating-sign counterpart against a sequence `u : ℕ → M` over `Finset.range (N + 1)`
and over `ℕ` via `finsum` when `u` has finite support.

## Main results

* `TauCeti.Ring.sum_range_choose_add_one_smul`:
  `∑ i ∈ range (N + 1), (m + 1 choose i) • u i =`
  `∑ i ∈ range (N + 1), (m choose i) • u i + ∑ i ∈ range N, (m choose i) • u (i + 1)`.
* `TauCeti.Ring.sum_range_neg_one_pow_mul_choose_smul`:
  `∑ i ∈ range (N + 1), (-1)ⁱ (n choose i) • u i =`
  `∑ i ∈ range N, (-1)ⁱ (n choose i) • u (i + 1) +`
  `∑ i ∈ range (N + 1), (-1)ⁱ (n + 1 choose i) • u i`.
* `TauCeti.Ring.finsum_choose_add_one_smul` and
  `TauCeti.Ring.finsum_neg_one_pow_mul_choose_smul`: `finsum` forms for finitely supported
  sequences `u : ℕ → M`.
-/

public section

open Finset

namespace TauCeti.Ring

private theorem exists_finsum_smul_eq_sum_range {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {u : ℕ → M} (hu : Function.HasFiniteSupport u) :
    ∃ N : ℕ,
      (∀ c : ℕ → R, (∑ᶠ i : ℕ, c i • u i) = ∑ i ∈ range (N + 2), c i • u i) ∧
      (∀ c : ℕ → R, (∑ᶠ i : ℕ, c i • u (i + 1)) = ∑ i ∈ range (N + 1), c i • u (i + 1)) := by
  obtain ⟨N, hN⟩ := hu.bddAbove
  have hzero (i : ℕ) (hi : N + 1 ≤ i) : u i = 0 :=
    Function.notMem_support.1 fun h ↦ (hN h).not_gt hi
  exact ⟨N,
    fun c ↦ TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hzero i (by omega)],
    fun c ↦ TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by
      simp [hzero (i + 1) (by omega)]⟩

variable {R : Type*} [Ring R] [BinomialRing R]

/-- Pascal's identity summed over `Finset.range (N + 1)`:
`∑_{i ≤ N} (m + 1 choose i) • u i` equals
`∑_{i ≤ N} (m choose i) • u i + ∑_{i < N} (m choose i) • u (i + 1)`. -/
theorem sum_range_choose_add_one_smul {M : Type*} [AddCommMonoid M] [Module R M]
    (N : ℕ) (m : R) (u : ℕ → M) :
    (∑ i ∈ range (N + 1), _root_.Ring.choose (m + 1) i • u i) =
      (∑ i ∈ range (N + 1), _root_.Ring.choose m i • u i) +
        ∑ i ∈ range N, _root_.Ring.choose m i • u (i + 1) := by
  rw [sum_range_succ' _ N, sum_range_succ' _ N]
  simp only [_root_.Ring.choose_zero_right, one_smul, _root_.Ring.choose_succ_succ, add_smul,
    sum_add_distrib]; ac_rfl

/-- Alternating-sign Pascal identity summed over `Finset.range (N + 1)`:
`∑_{i ≤ N} (-1)ⁱ (n choose i) • u i =`
`∑_{i < N} (-1)ⁱ (n choose i) • u (i + 1) + ∑_{i ≤ N} (-1)ⁱ (n + 1 choose i) • u i`. -/
theorem sum_range_neg_one_pow_mul_choose_smul {M : Type*} [AddCommGroup M] [Module R M]
    (N : ℕ) (n : R) (u : ℕ → M) :
    (∑ i ∈ range (N + 1), ((-1 : R) ^ i * _root_.Ring.choose n i) • u i) =
      (∑ i ∈ range N, ((-1 : R) ^ i * _root_.Ring.choose n i) • u (i + 1)) +
        ∑ i ∈ range (N + 1), ((-1 : R) ^ i * _root_.Ring.choose (n + 1) i) • u i := by
  rw [sum_range_succ' _ N, sum_range_succ' _ N]
  simp only [pow_zero, _root_.Ring.choose_zero_right, one_mul, one_smul]
  rw [← add_assoc, ← sum_add_distrib]; congr 1
  exact sum_congr rfl fun i _ ↦ by
    rw [← add_smul, _root_.Ring.choose_succ_succ, pow_succ, mul_add]
    congr 1; simp only [mul_neg_one, neg_mul]; abel

/-- Pascal's identity as a `finsum` for a finitely supported sequence `u : ℕ → M`:
`∑ᶠ i : ℕ, (m + 1 choose i) • u i =`
`(∑ᶠ i : ℕ, (m choose i) • u i) + ∑ᶠ i : ℕ, (m choose i) • u (i + 1)`. -/
theorem finsum_choose_add_one_smul {M : Type*} [AddCommMonoid M] [Module R M]
    (m : R) {u : ℕ → M} (hu : Function.HasFiniteSupport u) :
    (∑ᶠ i : ℕ, _root_.Ring.choose (m + 1) i • u i) =
      (∑ᶠ i : ℕ, _root_.Ring.choose m i • u i) +
        ∑ᶠ i : ℕ, _root_.Ring.choose m i • u (i + 1) := by
  obtain ⟨N, h₁, h₂⟩ := exists_finsum_smul_eq_sum_range (R := R) hu
  rw [h₁ (fun i ↦ _root_.Ring.choose (m + 1) i), h₁ (fun i ↦ _root_.Ring.choose m i),
    h₂ (fun i ↦ _root_.Ring.choose m i), sum_range_choose_add_one_smul]

/-- Alternating-sign Pascal identity as a `finsum` for a finitely supported sequence `u : ℕ → M`:
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • u i =`
`(∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • u (i + 1)) + ∑ᶠ i : ℕ, (-1)ⁱ (n + 1 choose i) • u i`. -/
theorem finsum_neg_one_pow_mul_choose_smul {M : Type*} [AddCommGroup M] [Module R M]
    (n : R) {u : ℕ → M} (hu : Function.HasFiniteSupport u) :
    (∑ᶠ i : ℕ, ((-1 : R) ^ i * _root_.Ring.choose n i) • u i) =
      (∑ᶠ i : ℕ, ((-1 : R) ^ i * _root_.Ring.choose n i) • u (i + 1)) +
        ∑ᶠ i : ℕ, ((-1 : R) ^ i * _root_.Ring.choose (n + 1) i) • u i := by
  obtain ⟨N, h₁, h₂⟩ := exists_finsum_smul_eq_sum_range (R := R) hu
  rw [h₁ (fun i ↦ (-1 : R) ^ i * _root_.Ring.choose n i),
    h₂ (fun i ↦ (-1 : R) ^ i * _root_.Ring.choose n i),
    h₁ (fun i ↦ (-1 : R) ^ i * _root_.Ring.choose (n + 1) i),
    sum_range_neg_one_pow_mul_choose_smul]

end TauCeti.Ring
