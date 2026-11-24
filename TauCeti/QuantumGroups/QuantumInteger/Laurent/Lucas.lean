/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Binomial
public import TauCeti.QuantumGroups.QuantumInteger.Lucas

import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# The quantum Lucas theorem for signed Laurent Gaussians

This file evaluates the signed Laurent Gaussian `[m choose r]_v` of
`TauCeti.signedLaurentQuantumBinomial` at a root of unity, for every integer upper argument `m`.
If `ζ²` is a primitive `l`-th root of unity in a field, `m = m₁ l + m₀` with `m₁ ∈ ℤ` and
`0 ≤ m₀ < l`, and `r = r₁ l + r₀` with `0 ≤ r₀ < l`, then

`[m choose r]_ζ = ζ^(l(r₁ m₀ - m₁ r₀) + (m₁ + 1) r₁ l²) [m₀ choose r₀]_ζ binom(m₁, r₁)`,

where `binom(m₁, r₁) = Ring.choose m₁ r₁` is the integer-valued binomial coefficient, so that
`binom(-1, 1) = -1` rather than `0`. The power of `ζ` is a sign `±1`. Toral elements of a
quantum group act on a weight vector of an arbitrary, possibly negative, integral weight through
such signed Gaussians, and this formula computes those eigenvalues at a root of unity.

For `m ≥ 0` this is the field-valued theorem `TauCeti.quantumBinomial_mul_add_mul_add`. For
`m < 0` the reflection `[-a choose r]_v = (-1)^r [a + r - 1 choose r]_v` reduces it to a
natural upper argument; comparing the resulting binomial coefficient with
`binom(m₁, r₁) = (-1)^r₁ binom(-m₁ + r₁ - 1, r₁)` uses two facts at the root of unity: the shift
`[m - l choose r]_ζ = ζ^(lr) [m choose r]_ζ` for `r < l`, which holds because `[l]_ζ = 0` while
`[r]_ζ! ≠ 0`, and the sign `ζ^(l(l+1)) = (-1)^(l+1)` of
`IsPrimitiveRoot.pow_mul_add_one_eq_neg_one_pow`.

## Main results

* `TauCeti.laurentEval_signedLaurentQuantumBinomial_mul_add_mul_add`: the quantum Lucas theorem
  for every integer upper argument.
* `TauCeti.laurentEval_signedLaurentQuantumBinomial_eq_zero_of_dvd_of_not_dvd`: if `l ∣ m` and
  `l ∤ r` then `[m choose r]_ζ = 0`, for every integer `m`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Chapter 34, for the
  Gaussian binomials with negative upper argument at roots of unity.
* K. McGerty, *Hall algebras and quantum Frobenius*, arXiv math/0601150, Lemma 2.7, for the
  quantum Lucas theorem with nonnegative upper argument.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti

variable {K : Type*} [Field K]

/-- If `q²` is a primitive `l`-th root of unity and `r < l`, then
`[m - l choose r]_q = q^(lr) [m choose r]_q` for every integer `m`: each factor of
`[m - l]_q ⋯ [m - l - r + 1]_q` is `q^l` times the corresponding factor for `m`, and the quantum
factorial `[r]_q!` is nonzero. -/
private theorem laurentEval_signedLaurentQuantumBinomial_sub {ζ : Kˣ} {l : ℕ}
    (hζ : IsPrimitiveRoot ((ζ : K) ^ 2) l) (m : ℤ) {r : ℕ} (hr : r < l) :
    laurentEval ζ (signedLaurentQuantumBinomial (m - l) r) =
      (ζ : K) ^ (l * r) * laurentEval ζ (signedLaurentQuantumBinomial m r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr₀
  · simp
  have hF := (quantumFactorial_ne_zero_iff_lt hζ (by omega)).mpr hr
  have hu := sub_inv_ne_zero_of_quantumFactorial_ne_zero hr₀.ne' hF
  -- `[x - l]_q = q^l [x]_q`, since `[l]_q = 0` and `q^(-(-l)) = q^l`.
  have hshift (x : ℤ) :
      quantumInteger (ζ : K) (x - l) = (ζ : K) ^ l * quantumInteger (ζ : K) x := by
    have hl : quantumInteger (ζ : K) l = 0 :=
      (quantumInteger_eq_zero_iff_dvd ζ.ne_zero hζ l).mpr dvd_rfl
    rw [sub_eq_add_neg, quantumInteger_add, quantumInteger_neg, hl, neg_neg, zpow_natCast]
    ring
  have key (n : ℤ) := congrArg (laurentEval ζ)
    (signedLaurentQuantumBinomial_mul_laurentQuantumFactorial n r)
  simp only [map_mul, map_prod, laurentEval_laurentQuantumFactorial hu,
    laurentEval_laurentQuantumInteger hu] at key
  refine mul_right_cancel₀ hF ?_
  rw [key, mul_assoc, key]
  simp only [sub_right_comm _ (l : ℤ), hshift, prod_mul_distrib, prod_const, card_range, ← pow_mul]

/-- The signs and powers of `q` in the quantum Lucas theorem at the negative upper argument
`-(a + 1) l + m₀`: if `q²` is a primitive `l`-th root of unity and `n₀ + m₀ + 1 = l + r₀`, the sign
`(-1)^(r₁ l + r₀)` of the reflection, the factor `(-1)^r₀ q^(l r₀)` relating `[n₀ choose r₀]_q` to
`[m₀ choose r₀]_q` and the Lucas exponent for `(a + r₁) l + n₀` combine to the Lucas exponent for
`-(a + 1)` times the sign `(-1)^r₁` of `binom(-(a + 1), r₁)`. -/
private theorem neg_one_pow_mul_zpow_lucas {q : K} {l : ℕ} (hq : IsPrimitiveRoot (q ^ 2) l)
    (hl : 0 < l) (a r₁ : ℕ) {m₀ r₀ n₀ : ℕ} (hn₀ : n₀ + m₀ + 1 = l + r₀) :
    (-1) ^ (r₁ * l + r₀) *
        q ^ ((l : ℤ) * (r₁ * n₀ - ((a + r₁ : ℕ) : ℤ) * r₀) +
          (((a + r₁ : ℕ) : ℤ) + 1) * r₁ * l ^ 2) *
        ((-1) ^ r₀ * q ^ ((l : ℤ) * r₀)) =
      q ^ ((l : ℤ) * (r₁ * m₀ - -((a : ℤ) + 1) * r₀) + (-((a : ℤ) + 1) + 1) * r₁ * l ^ 2) *
        (-1) ^ r₁ := by
  have hq₀ : q ≠ 0 := fun h => by simpa [h, hl.ne'] using hq.pow_eq_one
  have hll : q ^ ((l : ℤ) * (l + 1)) = (-1) ^ (l + 1) := by
    exact_mod_cast hq.pow_mul_add_one_eq_neg_one_pow hl
  -- The signs: `q^(l(l+1)r₁) (-1)^r₁ = (-1)^(r₁ l + r₀) (-1)^r₀`, both being `(-1)^(r₁ l)`.
  have hsign : q ^ ((l : ℤ) * (l + 1) * r₁) * (-1) ^ r₁ = (-1) ^ (r₁ * l + r₀) * (-1) ^ r₀ := by
    rw [zpow_mul, hll, zpow_natCast, ← pow_mul, ← pow_add, ← pow_add,
      show (l + 1) * r₁ + r₁ = r₁ * l + 2 * r₁ by ring,
      show r₁ * l + r₀ + r₀ = r₁ * l + 2 * r₀ by ring]
    simp [pow_add, pow_mul]
  -- The exponents differ by a multiple of `2l`, using that `r₁ (r₁ + 1)` is even.
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self (r₁ : ℤ)
  have hexp : q ^ ((l : ℤ) * (r₁ * m₀ - -((a : ℤ) + 1) * r₀) + (-((a : ℤ) + 1) + 1) * r₁ * l ^ 2) =
      q ^ ((l : ℤ) * (r₁ * n₀ - ((a + r₁ : ℕ) : ℤ) * r₀) + (((a + r₁ : ℕ) : ℤ) + 1) * r₁ * l ^ 2) *
        q ^ ((l : ℤ) * r₀) * q ^ ((l : ℤ) * (l + 1) * r₁) := by
    -- Exponents of `q` only matter modulo `2l`.
    have h2l : q ^ (2 * l : ℤ) = 1 := by exact_mod_cast (pow_mul q 2 l).trans hq.pow_eq_one
    have hper (x e : ℤ) : q ^ (x + 2 * l * e) = q ^ x := by
      rw [zpow_add₀ hq₀, zpow_mul, h2l, one_zpow, mul_one]
    rw [← zpow_add₀ hq₀, ← zpow_add₀ hq₀,
      ← hper _ (-(r₁ * m₀ + a * r₀ - l * t - l * r₁ - a * r₁ * l))]
    congr 1
    have hn₀z : (n₀ : ℤ) = l + r₀ - m₀ - 1 := by omega
    push_cast
    rw [hn₀z]
    linear_combination (-(l : ℤ) ^ 2) * ht
  rw [hexp, mul_assoc _ (q ^ ((l : ℤ) * (l + 1) * r₁)), hsign]
  ring

/-- **The quantum Lucas theorem for signed Laurent Gaussians**. If `ζ²` is a primitive `l`-th
root of unity, `m₀ < l` and `r₀ < l`, then for every integer `m₁` and natural number `r₁`,
`[m₁ l + m₀ choose r₁ l + r₀]_ζ` equals
`ζ^(l(r₁ m₀ - m₁ r₀) + (m₁ + 1) r₁ l²) [m₀ choose r₀]_ζ binom(m₁, r₁)`, with
`binom(m₁, r₁) = Ring.choose m₁ r₁` the integer-valued binomial coefficient. The power of `ζ` is a
sign `±1`, and it is `1` when `ζ` has odd order. -/
theorem laurentEval_signedLaurentQuantumBinomial_mul_add_mul_add {ζ : Kˣ} {l : ℕ}
    (hζ : IsPrimitiveRoot ((ζ : K) ^ 2) l) (m₁ : ℤ) (r₁ : ℕ) {m₀ r₀ : ℕ} (hm₀ : m₀ < l)
    (hr₀ : r₀ < l) :
    laurentEval ζ (signedLaurentQuantumBinomial (m₁ * l + m₀) (r₁ * l + r₀)) =
      (ζ : K) ^ ((l : ℤ) * (r₁ * m₀ - m₁ * r₀) + (m₁ + 1) * r₁ * l ^ 2) *
        quantumBinomial (ζ : K) m₀ r₀ * (Ring.choose m₁ r₁ : ℤ) := by
  rcases m₁ with n | a
  · -- A nonnegative upper argument: this is the field-valued quantum Lucas theorem.
    rw [Int.ofNat_eq_natCast, show (n : ℤ) * l + m₀ = ((n * l + m₀ : ℕ) : ℤ) by push_cast; ring,
      signedLaurentQuantumBinomial_natCast,
      laurentEval_laurentQuantumBinomial, quantumBinomial_mul_add_mul_add hζ n r₁ hm₀ hr₀,
      Ring.choose_natCast]
    norm_cast
  -- A negative upper argument `m₁ = -(a + 1)`. Write `m₁ l + m₀ = -(N + 1)` with `N ≥ 0`, so that
  -- `[m₁ l + m₀ choose r]_v = (-1)^r [N + r choose r]_v`.
  have hlm : m₀ + 1 ≤ a * l + l := by nlinarith
  obtain ⟨N, hN⟩ : ∃ N, a * l + l = N + m₀ + 1 := ⟨a * l + l - m₀ - 1, by omega⟩
  have hNz : (a * l + l : ℤ) = N + m₀ + 1 := by exact_mod_cast hN
  rw [show Int.negSucc a * l + m₀ = -((N : ℤ) + 1) by rw [Int.negSucc_eq]; linear_combination -hNz,
    signedLaurentQuantumBinomial_neg_succ, map_mul, map_pow, map_neg, map_one,
    laurentEval_laurentQuantumBinomial]
  -- `binom(-(a + 1), r₁) = (-1)^r₁ binom(a + r₁, r₁)`.
  have hchoose : (Ring.choose (Int.negSucc a) r₁ : ℤ) = (-1) ^ r₁ * ((a + r₁).choose r₁ : ℤ) := by
    rw [Int.negSucc_eq, Ring.choose_neg, show (a : ℤ) + 1 + r₁ - 1 = ((a + r₁ : ℕ) : ℤ) by
      push_cast; ring, Ring.choose_natCast]
    simp [Units.smul_def, Int.coe_negOnePow_natCast]
  rw [hchoose, Int.negSucc_eq]
  rcases le_or_gt r₀ m₀ with hrm | hrm
  · -- If `r₀ ≤ m₀`, then `N + r = (a + r₁) l + n₀` with `n₀ = l - 1 - m₀ + r₀ < l`.
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ + m₀ + 1 = l + r₀ := ⟨l + r₀ - m₀ - 1, by omega⟩
    have hNr : N + (r₁ * l + r₀) = (a + r₁) * l + n₀ := by rw [add_mul]; omega
    rw [hNr, quantumBinomial_mul_add_mul_add hζ (a + r₁) r₁ (by omega) hr₀]
    -- The reflection and the shift give `[n₀ choose r₀]_ζ = (-1)^r₀ ζ^(l r₀) [m₀ choose r₀]_ζ`.
    have hrefl := congrArg (laurentEval ζ) (signedLaurentQuantumBinomial_neg ((l : ℤ) - m₀) r₀)
    rw [neg_sub, show (l : ℤ) - m₀ + r₀ - 1 = n₀ by omega,
      laurentEval_signedLaurentQuantumBinomial_sub hζ m₀ hr₀] at hrefl
    simp only [signedLaurentQuantumBinomial_natCast, laurentEval_laurentQuantumBinomial, map_mul,
      map_pow, map_neg, map_one] at hrefl
    have hn₀' : quantumBinomial (ζ : K) n₀ r₀ =
        (-1) ^ r₀ * (ζ : K) ^ ((l : ℤ) * r₀) * quantumBinomial (ζ : K) m₀ r₀ := by
      have hs : ((-1 : K) ^ r₀) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨r₀, by ring⟩
      rw [show (l : ℤ) * r₀ = ((l * r₀ : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      linear_combination -(-1) ^ r₀ * hrefl - quantumBinomial (ζ : K) n₀ r₀ * hs
    rw [hn₀']
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    linear_combination (quantumBinomial (ζ : K) m₀ r₀ * ((a + r₁).choose r₁ : K)) *
      neg_one_pow_mul_zpow_lucas hζ (by omega) a r₁ hn₀
  · -- If `r₀ > m₀`, both sides vanish: `N + r = (a + 1 + r₁) l + (r₀ - m₀ - 1)`.
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ + m₀ + 1 = r₀ := ⟨r₀ - m₀ - 1, by omega⟩
    have hNr : N + (r₁ * l + r₀) = (a + 1 + r₁) * l + n₀ := by rw [add_mul, add_mul]; omega
    rw [hNr, quantumBinomial_mul_add_mul_add hζ (a + 1 + r₁) r₁ (by omega) hr₀,
      quantumBinomial_eq_zero_of_lt _ (by omega : n₀ < r₀),
      quantumBinomial_eq_zero_of_lt _ hrm]
    simp

/-- If `ζ²` is a primitive `l`-th root of unity, then `[m choose r]_ζ = 0` whenever `l ∣ m` and
`l ∤ r`, for every integer upper argument `m`. -/
theorem laurentEval_signedLaurentQuantumBinomial_eq_zero_of_dvd_of_not_dvd {ζ : Kˣ} {l : ℕ}
    (hζ : IsPrimitiveRoot ((ζ : K) ^ 2) l) {m : ℤ} {r : ℕ} (hm : (l : ℤ) ∣ m) (hr : ¬l ∣ r) :
    laurentEval ζ (signedLaurentQuantumBinomial m r) = 0 := by
  obtain ⟨m₁, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · -- For `l = 0`, `m = 0` and `r > 0`, so `[0 choose r]_v = 0` already.
    have hr₀ : 0 < r := Nat.pos_of_ne_zero (by simpa using hr)
    rw [Nat.cast_zero, zero_mul, ← Nat.cast_zero, signedLaurentQuantumBinomial_natCast,
      laurentQuantumBinomial_eq_zero_of_lt hr₀, map_zero]
  have hr₀ : 0 < r % l := Nat.pos_of_ne_zero fun h => hr (Nat.dvd_of_mod_eq_zero h)
  rw [← Nat.div_add_mod' r l, mul_comm (l : ℤ) m₁, ← add_zero (m₁ * l), ← Nat.cast_zero,
    laurentEval_signedLaurentQuantumBinomial_mul_add_mul_add hζ m₁ (r / l) hl (Nat.mod_lt r hl),
    quantumBinomial_eq_zero_of_lt _ hr₀]
  simp

/-- At a primitive cube root of unity `ζ`, so that `ζ²` has order `3`, the quantum Lucas theorem
gives `[-3 choose 3]_ζ = ζ⁰ [0 choose 0]_ζ binom(-1, 1) = -1`; a Gaussian vanishing at negative
upper arguments would give `0`. -/
example {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : K) ^ 2) 3) :
    laurentEval ζ (signedLaurentQuantumBinomial (-3) 3) = -1 := by
  have h := laurentEval_signedLaurentQuantumBinomial_mul_add_mul_add hζ (-1) 1
    (m₀ := 0) (r₀ := 0) (by norm_num) (by norm_num)
  norm_num [Ring.choose_one_right] at h
  exact h

end TauCeti
