/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Factorial
public import Mathlib.RingTheory.Binomial

import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic

/-!
# Laurent Gaussian binomials

This file defines the symmetric Gaussian binomial `[n choose r]_v` in `ℤ[v, v⁻¹]` by the Pascal
recursion
`[n+1 choose r+1]_v = v^(n-r) [n choose r]_v + v^(-(r+1)) [n choose r+1]_v`,
with `[n choose 0]_v = 1` and `[0 choose r+1]_v = 0`, and its extension
`[m choose r]_v` to an arbitrary integer upper argument `m`, given for `m = -a < 0` by the
reflection `[-a choose r]_v = (-1)^r [a+r-1 choose r]_v`.

The Laurent polynomial `[n choose r]_v` is the integral form of the field-valued symmetric quantum
binomial `TauCeti.quantumBinomial`: it takes the value `[n choose r]_q` at every unit `q` of a
field, including roots of unity, and the ordinary binomial coefficient at `v = 1`. The signed
extension is the Laurent polynomial
`[m choose r]_v = [m]_v [m-1]_v ⋯ [m-r+1]_v / [r]_v!`, and it specializes at `v = 1` to Mathlib's
integer-valued binomial `Ring.choose m r`. These are the coefficients of the divided powers and
toral binomials of integral forms of quantized enveloping algebras, whose specializations at roots
of unity are computed from them.

The identities of `[n choose r]_v` that hold over every field, such as the second Pascal rule,
invariance under `v ↦ v⁻¹` and the factorial formula, are deduced from those of
`TauCeti.quantumBinomial` by `TauCeti.eq_of_forall_laurentEval_eq`. The identities of the signed
extension follow from its product formula, since `[r]_v! ≠ 0` in the domain `ℤ[v, v⁻¹]`.

## Main definitions

* `TauCeti.laurentQuantumBinomial n r`: the Gaussian binomial `[n choose r]_v` in `ℤ[v, v⁻¹]`.
* `TauCeti.signedLaurentQuantumBinomial m r`: its extension to an integer upper argument `m`.

## Main results

* `TauCeti.laurentEval_laurentQuantumBinomial`: the value at a unit `q` of a field is the
  symmetric quantum binomial `[n choose r]_q`.
* `TauCeti.laurentEval_one_laurentQuantumBinomial`: the value at `v = 1` is `n.choose r`.
* `TauCeti.laurentQuantumBinomial_succ_succ'`, `TauCeti.laurentQuantumBinomial_invert` and
  `TauCeti.laurentQuantumBinomial_symm`: the second Pascal rule, invariance under `v ↦ v⁻¹`, and
  the symmetry `[n choose n - r]_v = [n choose r]_v` for `r ≤ n`.
* `TauCeti.laurentQuantumBinomial_mul_laurentQuantumFactorial_mul_laurentQuantumFactorial`:
  `[n choose r]_v [r]_v! [n - r]_v! = [n]_v!` for `r ≤ n`.
* `TauCeti.signedLaurentQuantumBinomial_neg`: the reflection
  `[-m choose r]_v = (-1)^r [m + r - 1 choose r]_v` for every integer `m`.
* `TauCeti.signedLaurentQuantumBinomial_succ_succ`: the Pascal rule for every integer upper
  argument.
* `TauCeti.signedLaurentQuantumBinomial_mul_laurentQuantumFactorial`: the product formula
  `[m choose r]_v [r]_v! = [m]_v [m-1]_v ⋯ [m-r+1]_v`, which determines `[m choose r]_v`.
* `TauCeti.laurentEval_one_signedLaurentQuantumBinomial`: the value at `v = 1` is
  `Ring.choose m r`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Section 1.3, for the
  Gaussian binomials `[m choose r]_v` in `ℤ[v, v⁻¹]` with integer upper argument.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Chapter 0, for
  the symmetric normalization.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti

/-! ### The Gaussian binomial with natural upper argument -/

/-- The symmetric Gaussian binomial `[n choose r]_v` in `ℤ[v, v⁻¹]`, defined by
`[n choose 0]_v = 1`, `[0 choose r+1]_v = 0` and the Pascal rule
`[n+1 choose r+1]_v = v^(n-r) [n choose r]_v + v^(-(r+1)) [n choose r+1]_v`. -/
noncomputable def laurentQuantumBinomial : ℕ → ℕ → ℤ[T;T⁻¹]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 =>
    T ((n : ℤ) - r) * laurentQuantumBinomial n r +
      T (-((r : ℤ) + 1)) * laurentQuantumBinomial n (r + 1)

/-- `[n choose 0]_v = 1`. -/
@[simp]
theorem laurentQuantumBinomial_zero_right (n : ℕ) : laurentQuantumBinomial n 0 = 1 := by
  cases n <;> simp [laurentQuantumBinomial]

/-- `[0 choose r + 1]_v = 0`. -/
theorem laurentQuantumBinomial_zero_succ (r : ℕ) : laurentQuantumBinomial 0 (r + 1) = 0 := by
  simp [laurentQuantumBinomial]

/-- The defining Pascal rule
`[n+1 choose r+1]_v = v^(n-r) [n choose r]_v + v^(-(r+1)) [n choose r+1]_v`. -/
theorem laurentQuantumBinomial_succ_succ (n r : ℕ) :
    laurentQuantumBinomial (n + 1) (r + 1) =
      T ((n : ℤ) - r) * laurentQuantumBinomial n r +
        T (-((r : ℤ) + 1)) * laurentQuantumBinomial n (r + 1) := by
  rw [laurentQuantumBinomial]

/-- `[n choose r]_v = 0` for `n < r`. -/
@[simp]
theorem laurentQuantumBinomial_eq_zero_of_lt {n r : ℕ} (h : n < r) :
    laurentQuantumBinomial n r = 0 := by
  induction n generalizing r with
  | zero =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
    exact laurentQuantumBinomial_zero_succ r
  | succ n ih =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : r ≠ 0)
    rw [laurentQuantumBinomial_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- `[n choose n]_v = 1`. -/
@[simp]
theorem laurentQuantumBinomial_self (n : ℕ) : laurentQuantumBinomial n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [laurentQuantumBinomial_succ_succ, ih,
      laurentQuantumBinomial_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp

/-- At a unit `q` of a field, the Gaussian binomial `[n choose r]_v` takes the value of the
symmetric quantum binomial `[n choose r]_q`. This includes roots of unity and `q = ±1`. -/
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
      rcases le_or_gt r n with h | h
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        simp only [map_add, map_mul, laurentEval_T, ih, Units.val_zpow_eq_zpow_val]
        rw [Nat.cast_add, add_sub_cancel_left, zpow_natCast, Nat.add_sub_cancel_left, inv_pow,
          ← zpow_natCast (u : K) (r + 1), ← zpow_neg, Nat.cast_add_one]
      · simp [ih, quantumBinomial_eq_zero_of_lt _ h,
          quantumBinomial_eq_zero_of_lt _ (h.trans r.lt_succ_self)]

/-- At `v = 1` the Gaussian binomial `[n choose r]_v` is the binomial coefficient
`n.choose r`. -/
@[simp]
theorem laurentEval_one_laurentQuantumBinomial {A : Type*} [Ring A] (n r : ℕ) :
    laurentEval (1 : Aˣ) (laurentQuantumBinomial n r) = n.choose r := by
  induction n generalizing r with
  | zero => cases r <;> simp
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r => simp [laurentQuantumBinomial_succ_succ, ih, Nat.choose_succ_succ, add_comm]

/-! ### Identities transported from the fraction field -/

/-- The second Pascal rule
`[n+1 choose r+1]_v = v^(-(n-r)) [n choose r]_v + v^(r+1) [n choose r+1]_v`, the image of the
defining rule under `v ↦ v⁻¹`. -/
theorem laurentQuantumBinomial_succ_succ' (n r : ℕ) :
    laurentQuantumBinomial (n + 1) (r + 1) =
      T (-((n : ℤ) - r)) * laurentQuantumBinomial n r +
        T ((r : ℤ) + 1) * laurentQuantumBinomial n (r + 1) := by
  refine eq_of_forall_laurentEval_eq fun K _ u _ => ?_
  rw [laurentEval_laurentQuantumBinomial, quantumBinomial_succ_succ']
  rcases le_or_gt r n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [map_add, map_mul, laurentEval_T, laurentEval_laurentQuantumBinomial,
      Units.val_zpow_eq_zpow_val]
    rw [Nat.cast_add, add_sub_cancel_left, zpow_neg, zpow_natCast, Nat.add_sub_cancel_left,
      inv_pow, ← Nat.cast_add_one, zpow_natCast]
  · simp [quantumBinomial_eq_zero_of_lt _ h,
      quantumBinomial_eq_zero_of_lt _ (h.trans r.lt_succ_self), Units.val_zpow_eq_zpow_val]

/-- The Gaussian binomials are invariant under `v ↦ v⁻¹`. -/
@[simp]
theorem laurentQuantumBinomial_invert (n r : ℕ) :
    invert (laurentQuantumBinomial n r) = laurentQuantumBinomial n r := by
  refine eq_of_forall_laurentEval_eq fun K _ u _ => ?_
  simp [Units.val_inv_eq_inv_val]

/-- The symmetry `[n choose n - r]_v = [n choose r]_v` for `r ≤ n`. -/
theorem laurentQuantumBinomial_symm {n r : ℕ} (h : r ≤ n) :
    laurentQuantumBinomial n (n - r) = laurentQuantumBinomial n r := by
  refine eq_of_forall_laurentEval_eq fun K _ u _ => ?_
  simp [quantumBinomial_symm _ h]

/-- `[n choose 1]_v = [n]_v`. -/
@[simp]
theorem laurentQuantumBinomial_one_right (n : ℕ) :
    laurentQuantumBinomial n 1 = laurentQuantumInteger n := by
  refine eq_of_forall_laurentEval_eq fun K _ u hu => ?_
  rw [laurentEval_laurentQuantumBinomial, laurentEval_laurentQuantumInteger hu,
    quantumBinomial_one_right hu]

/-- The absorption identity `[n choose r + 1]_v [r + 1]_v = [n choose r]_v [n - r]_v`. -/
theorem laurentQuantumBinomial_succ_right_eq (n r : ℕ) :
    laurentQuantumBinomial n (r + 1) * laurentQuantumInteger (r + 1) =
      laurentQuantumBinomial n r * laurentQuantumInteger (n - r) := by
  refine eq_of_forall_laurentEval_eq fun K _ u hu => ?_
  simpa [laurentEval_laurentQuantumInteger hu] using quantumBinomial_succ_right_eq (u : K) n r

/-- The Gaussian binomial times the two complementary quantum factorials is the quantum
factorial: `[n choose r]_v [r]_v! [n - r]_v! = [n]_v!` for `r ≤ n`. -/
theorem laurentQuantumBinomial_mul_laurentQuantumFactorial_mul_laurentQuantumFactorial
    {n r : ℕ} (h : r ≤ n) :
    laurentQuantumBinomial n r * laurentQuantumFactorial r * laurentQuantumFactorial (n - r) =
      laurentQuantumFactorial n := by
  refine eq_of_forall_laurentEval_eq fun K _ u hu => ?_
  simpa [laurentEval_laurentQuantumFactorial hu] using
    quantumBinomial_mul_quantumFactorial_mul_quantumFactorial (u : K) h

/-! ### The Gaussian binomial with integer upper argument -/

/-- The Gaussian binomial `[m choose r]_v` in `ℤ[v, v⁻¹]` with integer upper argument `m`: it is
`TauCeti.laurentQuantumBinomial m r` for `m ≥ 0`, and `(-1)^r [a + r - 1 choose r]_v` for
`m = -a < 0`. It is the Laurent polynomial `[m]_v [m-1]_v ⋯ [m-r+1]_v / [r]_v!`. -/
noncomputable def signedLaurentQuantumBinomial : ℤ → ℕ → ℤ[T;T⁻¹]
  | (n : ℕ), r => laurentQuantumBinomial n r
  | Int.negSucc a, r => (-1) ^ r * laurentQuantumBinomial (a + r) r

/-- For a natural upper argument the signed Gaussian binomial is `[n choose r]_v`. -/
@[simp]
theorem signedLaurentQuantumBinomial_natCast (n r : ℕ) :
    signedLaurentQuantumBinomial n r = laurentQuantumBinomial n r :=
  signedLaurentQuantumBinomial.eq_1 r n

/-- For the negative upper argument `-(a + 1)`, the signed Gaussian binomial is
`(-1)^r [a + r choose r]_v`. -/
theorem signedLaurentQuantumBinomial_negSucc (a r : ℕ) :
    signedLaurentQuantumBinomial (Int.negSucc a) r = (-1) ^ r * laurentQuantumBinomial (a + r) r :=
  signedLaurentQuantumBinomial.eq_2 r a

/-- `[m choose 0]_v = 1`. -/
@[simp]
theorem signedLaurentQuantumBinomial_zero_right (m : ℤ) : signedLaurentQuantumBinomial m 0 = 1 := by
  cases m <;> simp [signedLaurentQuantumBinomial_negSucc]

/-- Reflecting a product of `r` consecutive quantum integers through zero:
`[-m]_v [-m-1]_v ⋯ [-m-r+1]_v = (-1)^r [m+r-1]_v [m+r-2]_v ⋯ [m]_v`. -/
private theorem prod_laurentQuantumInteger_neg_sub (m : ℤ) (r : ℕ) :
    ∏ j ∈ range r, laurentQuantumInteger (-m - j) =
      (-1) ^ r * ∏ j ∈ range r, laurentQuantumInteger (m + r - 1 - j) := by
  have h : ∀ j ∈ range r, laurentQuantumInteger (-m - j) =
      -laurentQuantumInteger (m + r - 1 - ((r - 1 - j : ℕ) : ℤ)) := by
    intro j hj
    have := mem_range.mp hj
    rw [← laurentQuantumInteger_neg]
    congr 1
    omega
  rw [prod_congr rfl h, prod_neg, card_range,
    prod_range_reflect (fun j : ℕ => laurentQuantumInteger (m + r - 1 - j)) r]

/-- The product formula `[m choose r]_v [r]_v! = [m]_v [m-1]_v ⋯ [m-r+1]_v` for every integer
`m`. Since `[r]_v! ≠ 0` in the domain `ℤ[v, v⁻¹]`, it determines `[m choose r]_v`. -/
theorem signedLaurentQuantumBinomial_mul_laurentQuantumFactorial (m : ℤ) (r : ℕ) :
    signedLaurentQuantumBinomial m r * laurentQuantumFactorial r =
      ∏ j ∈ range r, laurentQuantumInteger (m - j) := by
  -- For a natural upper argument this follows from the absorption identity by induction on `r`.
  have hnat (n : ℕ) : laurentQuantumBinomial n r * laurentQuantumFactorial r =
      ∏ j ∈ range r, laurentQuantumInteger ((n : ℤ) - j) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [laurentQuantumFactorial_succ, prod_range_succ, ← ih]
      linear_combination laurentQuantumFactorial r * laurentQuantumBinomial_succ_right_eq n r
  cases m with
  | ofNat n => exact hnat n
  | negSucc a =>
    rw [signedLaurentQuantumBinomial_negSucc, mul_assoc, hnat, Int.negSucc_eq,
      prod_laurentQuantumInteger_neg_sub]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring

/-- The reflection identity `[-m choose r]_v = (-1)^r [m + r - 1 choose r]_v` for every integer
`m`. -/
theorem signedLaurentQuantumBinomial_neg (m : ℤ) (r : ℕ) :
    signedLaurentQuantumBinomial (-m) r =
      (-1) ^ r * signedLaurentQuantumBinomial (m + r - 1) r := by
  refine mul_right_cancel₀ (laurentQuantumFactorial_ne_zero r) ?_
  rw [mul_assoc, signedLaurentQuantumBinomial_mul_laurentQuantumFactorial,
    signedLaurentQuantumBinomial_mul_laurentQuantumFactorial, prod_laurentQuantumInteger_neg_sub]

/-- The Pascal rule
`[m+1 choose r+1]_v = v^(m-r) [m choose r]_v + v^(-(r+1)) [m choose r+1]_v`, for every integer
upper argument `m`. -/
theorem signedLaurentQuantumBinomial_succ_succ (m : ℤ) (r : ℕ) :
    signedLaurentQuantumBinomial (m + 1) (r + 1) =
      T (m - r) * signedLaurentQuantumBinomial m r +
        T (-((r : ℤ) + 1)) * signedLaurentQuantumBinomial m (r + 1) := by
  refine mul_right_cancel₀ (laurentQuantumFactorial_ne_zero (r + 1)) ?_
  -- Both sides become multiples of `P = [m]_v ⋯ [m-r+1]_v`; the coefficients agree by the
  -- addition formula `[m + 1]_v = v^(m-r) [r+1]_v + v^(-(r+1)) [m-r]_v`.
  have hL : ∏ j ∈ range (r + 1), laurentQuantumInteger (m + 1 - j) =
      (∏ j ∈ range r, laurentQuantumInteger (m - j)) * laurentQuantumInteger (m + 1) := by
    rw [prod_range_succ']
    simp only [Nat.cast_add_one, Nat.cast_zero, sub_zero, add_sub_add_right_eq_sub]
  have hadd := laurentQuantumInteger_add (m - r) (r + 1)
  rw [show m - r + (r + 1) = m + 1 by ring] at hadd
  have h₁ := signedLaurentQuantumBinomial_mul_laurentQuantumFactorial m r
  have h₂ := signedLaurentQuantumBinomial_mul_laurentQuantumFactorial m (r + 1)
  have h₃ := signedLaurentQuantumBinomial_mul_laurentQuantumFactorial (m + 1) (r + 1)
  rw [laurentQuantumFactorial_succ, prod_range_succ] at h₂
  rw [laurentQuantumFactorial_succ, hL] at h₃
  rw [laurentQuantumFactorial_succ]
  linear_combination h₃ - T (m - r) * laurentQuantumInteger (r + 1) * h₁ -
    T (-((r : ℤ) + 1)) * h₂ + (∏ j ∈ range r, laurentQuantumInteger (m - j)) * hadd

/-- The signed Gaussian binomials are invariant under `v ↦ v⁻¹`. -/
@[simp]
theorem signedLaurentQuantumBinomial_invert (m : ℤ) (r : ℕ) :
    invert (signedLaurentQuantumBinomial m r) = signedLaurentQuantumBinomial m r := by
  cases m <;> simp [signedLaurentQuantumBinomial_negSucc]

/-- At `v = 1` the signed Gaussian binomial `[m choose r]_v` is the integer-valued binomial
`Ring.choose m r`. -/
@[simp]
theorem laurentEval_one_signedLaurentQuantumBinomial {A : Type*} [Ring A] (m : ℤ) (r : ℕ) :
    laurentEval (1 : Aˣ) (signedLaurentQuantumBinomial m r) = (Ring.choose m r : ℤ) := by
  cases m with
  | ofNat n => simp [Ring.choose_natCast]
  | negSucc a =>
    rw [signedLaurentQuantumBinomial_negSucc, Int.negSucc_eq, Ring.choose_neg,
      show (a : ℤ) + 1 + r - 1 = ((a + r : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
      Units.smul_def, Int.coe_negOnePow_natCast]
    simp

end TauCeti
