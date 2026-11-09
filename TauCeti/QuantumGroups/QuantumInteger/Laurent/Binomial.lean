/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Basic
public import Mathlib.RingTheory.Binomial

/-!
# Signed symmetric Laurent Gaussian coefficients

`laurentQuantumBinomial n r` is the symmetric Gaussian coefficient in `ℤ[v, v⁻¹]`.
`signedLaurentQuantumBinomial m r` extends it to every integer upper argument by
`[-a choose r] = (-1)^r [a+r-1 choose r]`. These integral coefficients can be
specialized at every unit, including roots of unity where the quotient of quantum
factorials is undefined.

Evaluation recovers `quantumBinomial` over a field, with no genericity assumption.
At `v = 1`, the signed coefficients recover `Ring.choose` on integers. In particular,
negative weights are retained rather than being truncated to zero.

The normalization and negative-upper-argument convention are those of G. Lusztig,
*Introduction to Quantum Groups*, Chapters 1 and 34.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

/-- The symmetric Laurent Gaussian `[n choose r]_v`, defined by the Pascal recurrence
with coefficients `v^(n-r)` and `v^(-(r+1))`. -/
def laurentQuantumBinomial : ℕ → ℕ → ℤ[T;T⁻¹]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 =>
    T ((n : ℤ) - r) * laurentQuantumBinomial n r +
      T (-((r : ℤ) + 1)) * laurentQuantumBinomial n (r + 1)

/-- The zeroth Laurent Gaussian column is constantly one. -/
@[simp]
theorem laurentQuantumBinomial_zero_right (n : ℕ) : laurentQuantumBinomial n 0 = 1 := by
  cases n <;> rfl

/-- Positive entries of the zeroth row vanish. -/
theorem laurentQuantumBinomial_zero_succ (r : ℕ) :
    laurentQuantumBinomial 0 (r + 1) = 0 := (rfl)

/-- The defining symmetric Pascal recurrence, with integer exponents. -/
theorem laurentQuantumBinomial_succ_succ (n r : ℕ) :
    laurentQuantumBinomial (n + 1) (r + 1) =
      T ((n : ℤ) - r) * laurentQuantumBinomial n r +
        T (-((r : ℤ) + 1)) * laurentQuantumBinomial n (r + 1) := (rfl)

/-- Laurent Gaussian coefficients vanish above the diagonal. -/
@[simp]
theorem laurentQuantumBinomial_eq_zero_of_lt {n r : ℕ} (h : n < r) :
    laurentQuantumBinomial n r = 0 := by
  induction n generalizing r with
  | zero => cases r <;> simp_all [laurentQuantumBinomial_zero_succ]
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r => simp [laurentQuantumBinomial_succ_succ, ih (by omega : n < r),
        ih (by omega : n < r + 1)]

/-- Diagonal Laurent Gaussian coefficients are one. -/
@[simp]
theorem laurentQuantumBinomial_self (n : ℕ) : laurentQuantumBinomial n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [laurentQuantumBinomial_succ_succ, ih]

/-- The first Laurent Gaussian column is the Laurent quantum integer. -/
@[simp]
theorem laurentQuantumBinomial_one_right (n : ℕ) :
    laurentQuantumBinomial n 1 = laurentQuantumInteger n := by
  have key : ∀ n : ℕ, (T 1 - T (-1)) * laurentQuantumBinomial n 1 = T n - T (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [laurentQuantumBinomial_succ_succ]
      simp only [Nat.cast_zero, sub_zero, laurentQuantumBinomial_zero_right, mul_one,
        zero_add]
      calc
        _ = (T 1 - T (-1)) * T (n : ℤ) +
            T (-1) * ((T 1 - T (-1)) * laurentQuantumBinomial n 1) := by ring
        _ = T ((n : ℤ) + 1) - T (-((n : ℤ) + 1)) := by
          rw [ih]
          simp only [sub_mul, mul_sub, ← T_add]
          ring_nf
  apply mul_left_cancel₀ (T_sub_T_ne_zero (by decide : (1 : ℤ) ≠ -1))
  rw [key, T_sub_T_neg_mul_laurentQuantumInteger]

/-- Specialization at an arbitrary field unit agrees with the field-valued Pascal
coefficients, even at roots of unity and at `±1`. -/
@[simp]
theorem laurentEval_laurentQuantumBinomial {K : Type*} [Field K] (u : Kˣ) (n r : ℕ) :
    laurentEval u (laurentQuantumBinomial n r) = quantumBinomial (u : K) n r := by
  induction n generalizing r with
  | zero => cases r <;> simp
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [laurentQuantumBinomial_succ_succ, quantumBinomial_succ_succ]
      simp only [map_add, map_mul, laurentEval_T, ih, Units.val_zpow_eq_zpow_val]
      rw [← Nat.cast_add_one, zpow_neg, zpow_natCast, inv_pow]
      by_cases h : r ≤ n
      · rw [← Nat.cast_sub h, zpow_natCast]
      · simp [quantumBinomial_eq_zero_of_lt _ (by omega : n < r)]

/-- Specialization at `1` gives ordinary binomial coefficients over any ring. -/
@[simp]
theorem laurentEval_one_laurentQuantumBinomial {R : Type*} [Ring R] (n r : ℕ) :
    laurentEval (1 : Rˣ) (laurentQuantumBinomial n r) = n.choose r := by
  induction n generalizing r with
  | zero => cases r <;> simp
  | succ n ih => cases r <;> simp [laurentQuantumBinomial_succ_succ, ih,
      Nat.choose_succ_succ]

/-- The Laurent Gaussian with signed upper argument. For `a > 0`, its value at `-a`
is `(-1)^r [a+r-1 choose r]_v`. -/
def signedLaurentQuantumBinomial : ℤ → ℕ → ℤ[T;T⁻¹]
  | .ofNat n, r => laurentQuantumBinomial n r
  | .negSucc n, r => (-1) ^ r * laurentQuantumBinomial (n + r) r

/-- At nonnegative upper arguments, the signed extension is the ordinary Laurent Gaussian. -/
@[simp]
theorem signedLaurentQuantumBinomial_natCast (n r : ℕ) :
    signedLaurentQuantumBinomial n r = laurentQuantumBinomial n r := (rfl)

/-- The negative-upper-argument reflection formula, without natural subtraction. -/
theorem signedLaurentQuantumBinomial_neg_succ (n r : ℕ) :
    signedLaurentQuantumBinomial (-((n : ℤ) + 1)) r =
      (-1) ^ r * laurentQuantumBinomial (n + r) r := (rfl)

/-- The zeroth signed Laurent Gaussian column is constantly one. -/
@[simp]
theorem signedLaurentQuantumBinomial_zero_right (m : ℤ) :
    signedLaurentQuantumBinomial m 0 = 1 := by
  cases m <;> simp [signedLaurentQuantumBinomial]

/-- Every coefficient in the row with upper argument `-1` is a sign. -/
@[simp]
theorem signedLaurentQuantumBinomial_neg_one (r : ℕ) :
    signedLaurentQuantumBinomial (-1) r = (-1) ^ r := by
  simpa only [Nat.cast_zero, zero_add, laurentQuantumBinomial_self, mul_one] using
    signedLaurentQuantumBinomial_neg_succ 0 r

/-- The first signed Laurent Gaussian column agrees with the Laurent quantum
integer at every integer index. -/
@[simp]
theorem signedLaurentQuantumBinomial_one_right (m : ℤ) :
    signedLaurentQuantumBinomial m 1 = laurentQuantumInteger m := by
  cases m with
  | ofNat n => simp
  | negSucc n =>
    simp only [signedLaurentQuantumBinomial, pow_one, neg_one_mul,
      laurentQuantumBinomial_one_right, Int.negSucc_eq]
    rw [← Nat.cast_add_one, laurentQuantumInteger_neg]

/-- The signed Laurent Gaussian specializes at `1` to the integer-valued binomial
coefficient, also for negative upper arguments. -/
@[simp]
theorem laurentEval_one_signedLaurentQuantumBinomial {R : Type*} [Ring R] (m : ℤ) (r : ℕ) :
    laurentEval (1 : Rˣ) (signedLaurentQuantumBinomial m r) = (Ring.choose m r : ℤ) := by
  cases m with
  | ofNat n => simp [Ring.choose_natCast]
  | negSucc n =>
    rw [Int.negSucc_eq, signedLaurentQuantumBinomial_neg_succ, map_mul, map_pow,
      map_neg, map_one, laurentEval_one_laurentQuantumBinomial, Ring.choose_neg]
    have he : (n : ℤ) + 1 + r - 1 = (n + r : ℕ) := by omega
    rw [he, Ring.choose_natCast, Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]

-- Small normalization witnesses: these are symmetric, not the polynomial `1 + v²`.
example : laurentQuantumBinomial 2 1 = T 1 + T (-1) := by
  norm_num [laurentQuantumBinomial_succ_succ]

example : signedLaurentQuantumBinomial (-2) 1 = -(T 1 + T (-1)) := by
  have h := signedLaurentQuantumBinomial_neg_succ 1 1
  norm_num [laurentQuantumBinomial_succ_succ] at h
  simpa only [signedLaurentQuantumBinomial_one_right, laurentQuantumInteger_neg,
    neg_add_rev] using h

end TauCeti
