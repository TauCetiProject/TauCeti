/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
import TauCeti.Algebra.BigOperators.AlternatingSum
import Mathlib.Tactic.Abel

/-!
# Multiples of `1 + X` and alternating partial sums

For a finite sequence `d₀, …, d_N` in a ring, write
`qₙ = dₙ - dₙ₋₁ + ⋯ ± d₀ = ∑ᵢ₌₀ⁿ (-1)ⁿ⁻ⁱ dᵢ` for its alternating partial sums. Telescoping gives
the decomposition `∑ᵢ₌₀ᴺ dᵢ Xⁱ = (1 + X) ∑ₙ₌₀ᴺ⁻¹ qₙ Xⁿ + q_N X^N`
(`Polynomial.sum_range_monomial_eq_one_add_X_mul_add_monomial`). So `1 + X` divides the polynomial
exactly when `q_N = 0`, and then the quotient is `∑ₙ₌₀ᴺ⁻¹ qₙ Xⁿ`
(`Polynomial.sum_range_monomial_eq_one_add_X_mul_iff`).

Over `ℕ` this characterizes the numerical shape of the Morse inequalities. For sequences
`b, c : ℕ → ℕ`, there is a polynomial `Q` with natural coefficients such that
`∑ᵢ₌₀ᴺ cᵢ Xⁱ = ∑ᵢ₌₀ᴺ bᵢ Xⁱ + (1 + X) Q` if and only if the alternating partial sums satisfy
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀` for `n < N`, with equality for `n = N`
(`Polynomial.exists_sum_range_monomial_eq_add_one_add_X_mul_iff`). If moreover `bᵢ = cᵢ` for
`i > N`, then the coefficient of `Xⁿ` in `Q` is the difference of the two alternating partial sums
in degree `n`, for every `n` (`Polynomial.coeff_eq_sum_range_neg_one_pow_mul_sub`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

open Finset

namespace Polynomial

section Ring

variable {R : Type*} [Ring R]

/-- **Telescoping against `1 + X`.** `∑ᵢ₌₀ᴺ dᵢ Xⁱ = (1 + X) ∑ₙ₌₀ᴺ⁻¹ qₙ Xⁿ + q_N X^N`, where
`qₙ = ∑ᵢ₌₀ⁿ (-1)ⁿ⁻ⁱ dᵢ`. This is not division with remainder by the monic `1 + X` (whose
remainder is the constant `(-1)ᴺ q_N`), but it shows that `1 + X` divides the left side when
`q_N = 0`. -/
theorem sum_range_monomial_eq_one_add_X_mul_add_monomial (d : ℕ → R) (N : ℕ) :
    ∑ i ∈ range (N + 1), monomial i (d i) =
      (1 + X) * ∑ n ∈ range N, monomial n (∑ i ∈ range (n + 1), (-1) ^ (n - i) * d i) +
        monomial N (∑ i ∈ range (N + 1), (-1) ^ (N - i) * d i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun i ↦ monomial i (d i)), ih,
      sum_range_succ (fun n ↦ monomial n (∑ i ∈ range (n + 1), (-1 : R) ^ (n - i) * d i)) N,
      TauCeti.sum_range_succ_neg_one_pow_sub_mul, monomial_sub]
    rw [mul_add, add_mul 1 X (monomial N _), one_mul, X_mul_monomial]
    abel

/-- `1 + X` divides `∑ᵢ₌₀ᴺ dᵢ Xⁱ`, with quotient `Q`, exactly when the alternating sum
`q_N = ∑ᵢ₌₀ᴺ (-1)ᴺ⁻ⁱ dᵢ` vanishes and `Q = ∑ₙ₌₀ᴺ⁻¹ qₙ Xⁿ`. -/
theorem sum_range_monomial_eq_one_add_X_mul_iff (d : ℕ → R) (N : ℕ) {Q : R[X]} :
    ∑ i ∈ range (N + 1), monomial i (d i) = (1 + X) * Q ↔
      ∑ i ∈ range (N + 1), (-1) ^ (N - i) * d i = 0 ∧
        Q = ∑ n ∈ range N, monomial n (∑ i ∈ range (n + 1), (-1) ^ (n - i) * d i) := by
  rw [sum_range_monomial_eq_one_add_X_mul_add_monomial]
  set S := ∑ n ∈ range N, monomial n (∑ i ∈ range (n + 1), (-1 : R) ^ (n - i) * d i)
  set q := ∑ i ∈ range (N + 1), (-1 : R) ^ (N - i) * d i
  constructor
  · intro h
    -- Evaluating at `-1` kills the multiples of `1 + X`, leaving `q (-1)ᴺ = 0`.
    have hq : q = 0 := by
      have he := congrArg (eval (-1)) h
      simpa only [add_mul, one_mul, (commute_X _).eq, eval_add, eval_mul_X, mul_neg_one,
        add_neg_cancel, zero_add, eval_monomial, eq_comm (a := (0 : R)),
        mul_neg_one_pow_eq_zero_iff] using he
    refine ⟨hq, ?_⟩
    rw [hq, map_zero, add_zero] at h
    have hmonic : (1 + X : R[X]).Monic := by
      simpa only [map_one, add_comm] using monic_X_add_C (1 : R)
    rw [← sub_eq_zero, ← hmonic.mul_right_eq_zero_iff, mul_sub, ← h, sub_self]
  · rintro ⟨hq, rfl⟩
    rw [hq, map_zero, add_zero]

end Ring

section Nat

variable (b c : ℕ → ℕ) (N : ℕ)

/-- Mapping an identity `∑ᵢ₌₀ᴺ cᵢ Xⁱ = ∑ᵢ₌₀ᴺ bᵢ Xⁱ + (1 + X) Q` over `ℕ` to `ℤ` exhibits
`∑ᵢ₌₀ᴺ (cᵢ - bᵢ) Xⁱ` as a multiple of `1 + X`. -/
private theorem sum_range_monomial_sub_eq_one_add_X_mul {Q : ℕ[X]}
    (h : ∑ i ∈ range (N + 1), monomial i (c i) =
      ∑ i ∈ range (N + 1), monomial i (b i) + (1 + X) * Q) :
    ∑ i ∈ range (N + 1), monomial i ((c i : ℤ) - b i) = (1 + X) * Q.map (Nat.castRingHom ℤ) := by
  have h' := congrArg (map (Nat.castRingHom ℤ)) h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_one,
    map_X, map_monomial, eq_natCast] at h'
  simp only [monomial_sub, sum_sub_distrib, h']
  ring

/-- The alternating partial sums of `c - b` are the differences of those of `c` and `b`. -/
private theorem sum_range_neg_one_pow_mul_natCast_sub (n : ℕ) :
    ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((c i : ℤ) - b i) =
      ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * c i -
        ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * b i := by
  simp only [mul_sub, sum_sub_distrib]

variable {b c} in
/-- If `Q ∈ ℕ[X]` maps to `∑ₙ₌₀ᴹ⁻¹ qₙ Xⁿ` in `ℤ[X]`, where `qₙ` are the alternating partial sums of
`c - b`, then for `n < M` the coefficient of `Xⁿ` in `Q` is `qₙ`. -/
private theorem coeff_eq_of_map_eq_sum_range_monomial {Q : ℕ[X]} {M : ℕ}
    (hQ : Q.map (Nat.castRingHom ℤ) =
      ∑ n ∈ range M, monomial n (∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((c i : ℤ) - b i)))
    {n : ℕ} (hn : n < M) :
    (Q.coeff n : ℤ) = ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * c i -
      ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * b i := by
  simpa [coeff_map, finsetSum_coeff, coeff_monomial, hn,
    sum_range_neg_one_pow_mul_natCast_sub] using congrArg (coeff · n) hQ

/-- **Polynomial form of the Morse inequalities.** For `b, c : ℕ → ℕ`, there is a polynomial
`Q ∈ ℕ[X]` with `∑ᵢ₌₀ᴺ cᵢ Xⁱ = ∑ᵢ₌₀ᴺ bᵢ Xⁱ + (1 + X) Q` if and only if
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀` for every `n < N`, with equality for `n = N`. -/
theorem exists_sum_range_monomial_eq_add_one_add_X_mul_iff :
    (∃ Q : ℕ[X], ∑ i ∈ range (N + 1), monomial i (c i) =
        ∑ i ∈ range (N + 1), monomial i (b i) + (1 + X) * Q) ↔
      (∀ n < N, ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * b i ≤
          ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * c i) ∧
        ∑ i ∈ range (N + 1), (-1 : ℤ) ^ (N - i) * b i =
          ∑ i ∈ range (N + 1), (-1 : ℤ) ^ (N - i) * c i := by
  have hsub := sum_range_neg_one_pow_mul_natCast_sub b c
  constructor
  · rintro ⟨Q, h⟩
    obtain ⟨hN, hQ⟩ := (sum_range_monomial_eq_one_add_X_mul_iff _ N).1
      (sum_range_monomial_sub_eq_one_add_X_mul b c N h)
    refine ⟨fun n hn ↦ ?_, by rw [hsub] at hN; linarith⟩
    -- The coefficients of `Q` are the differences of the alternating partial sums.
    linarith [coeff_eq_of_map_eq_sum_range_monomial hQ hn,
      (Nat.cast_nonneg (Q.coeff n) : (0 : ℤ) ≤ _)]
  · rintro ⟨hle, heq⟩
    refine ⟨∑ n ∈ range N,
      monomial n (∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((c i : ℤ) - b i)).toNat, ?_⟩
    apply map_injective (Nat.castRingHom ℤ) Nat.cast_injective
    have hS : ∑ n ∈ range N, monomial n
          ((∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((c i : ℤ) - b i)).toNat : ℤ) =
        ∑ n ∈ range N, monomial n
          (∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((c i : ℤ) - b i)) :=
      sum_congr rfl fun n hn ↦ by
        rw [Int.toNat_of_nonneg (by rw [hsub]; linarith [hle n (mem_range.1 hn)])]
    have hd := sum_range_monomial_eq_one_add_X_mul_add_monomial (fun i ↦ (c i : ℤ) - b i) N
    rw [hsub, ← heq, sub_self, map_zero, add_zero] at hd
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_one,
      map_X, map_monomial, eq_natCast, hS, ← hd, monomial_sub, sum_sub_distrib]
    ring

variable {b c N} in
/-- If `∑ᵢ₌₀ᴺ cᵢ Xⁱ = ∑ᵢ₌₀ᴺ bᵢ Xⁱ + (1 + X) Q` in `ℕ[X]`, and `bᵢ = cᵢ` for `i > N`, then the
coefficient of `Xⁿ` in `Q` is `(cₙ - cₙ₋₁ + ⋯ ± c₀) - (bₙ - bₙ₋₁ + ⋯ ± b₀)`, for every `n`. -/
theorem coeff_eq_sum_range_neg_one_pow_mul_sub {Q : ℕ[X]}
    (h : ∑ i ∈ range (N + 1), monomial i (c i) =
      ∑ i ∈ range (N + 1), monomial i (b i) + (1 + X) * Q)
    (hbc : ∀ i, N < i → b i = c i) (n : ℕ) :
    (Q.coeff n : ℤ) = ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * c i -
      ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * b i := by
  -- Since `cᵢ - bᵢ` vanishes for `i > N`, the sum may be extended to degree `N + n + 1 > n`.
  have hext : ∑ i ∈ range (N + 1), monomial i ((c i : ℤ) - b i) =
      ∑ i ∈ range (N + n + 1 + 1), monomial i ((c i : ℤ) - b i) :=
    sum_subset (range_subset_range.2 (by omega)) fun i _ hi ↦ by
      rw [hbc i (by simpa using hi), sub_self, map_zero]
  have hQ := ((sum_range_monomial_eq_one_add_X_mul_iff _ _).1
    (hext ▸ sum_range_monomial_sub_eq_one_add_X_mul b c N h)).2
  exact coeff_eq_of_map_eq_sum_range_monomial hQ (by omega)

end Nat

end Polynomial
