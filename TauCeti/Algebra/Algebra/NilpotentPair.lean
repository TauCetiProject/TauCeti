/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import TauCeti.Algebra.Algebra.CyclicQuotient
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# A square-zero and a cube-zero element with a nilpotent sum

Let `x` and `y` be elements of an `R`-algebra with `x ^ 2 = 0` and `y ^ 3 = 0`. If moreover
`(x + y) ^ 3 = 0`, then **every product of six factors from `{x, y}` vanishes**; if instead
`(x + y) ^ 5 = 0`, then **every product of fifteen factors from `{x, y}` vanishes**. So the sixth,
respectively fifteenth, power of the span of `{x, y}` is zero.

The products of factors from `{x, y}` which survive the relations `x ^ 2 = 0` and `y ^ 3 = 0`
are the words with no factor `x x` and no factor `y y y`.

For `(x + y) ^ 3 = 0`, expanding the cube leaves the four such words of length three, so

```text
y y x = -(y x y + x y y + x y x).
```

Multiplying this relation by `x` on the left and on the right and comparing gives
`y x y x = x y x y`. These four rewriting rules `x x ↦ 0`, `y y y ↦ 0`,
`y y x ↦ -(y x y + x y y + x y x)` and `y x y x ↦ x y x y` lower words in the degree-lexicographic
order with `x < y`, and every word of length six is rewritten to zero by them.

For `(x + y) ^ 5 = 0`, use the degree-lexicographic order with `y < x` instead. Expanding the
fifth power leaves the seven surviving words of length five, which give a rule for `x y x y x`.
Comparing the ways of rewriting overlapping leading words gives three more rules, for the words
`x y x y y x`, `x y y x y y x y x y` and `x y y x y y x y y x y y`; all six rules have integer
coefficients and leading coefficient one. The words containing none of the six leading words are
at most six in each length, there are none of length fifteen, and every product of a reduced word
with `x` or `y` is rewritten to an integer combination of reduced words. Hence the products of each
length lie in the integer span of the reduced words of that length, and those of length fifteen
vanish.

These are the relations satisfied at the branch node of the `E₆` and `E₈` diagrams by the
backtracks into their arms of lengths one and two, in the preprojective algebra: the backtrack into
the third arm, of length two for `E₆` and of length four for `E₈`, is `-(x + y)`.

For `(x + y) ^ 3 = 0` the reduced words also control the cyclic quotient `A / [A, A]` of the
ambient ring: if `x`, `y`, `y ^ 2` and `(x + y) ^ 2` are sums of commutators and `2` and `3` are
units, then so is every product of a positive number of factors from `{x, y}`. This is the step
at the branch node in the vanishing of the cyclic quotient of the `E₆` preprojective algebra in
positive degrees.

## Main results

* `TauCeti.span_pair_pow_six_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, then the
  sixth power of the span of `{x, y}` is zero.
* `TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow`: if moreover `x`, `y`, `y ^ 2` and
  `(x + y) ^ 2` are sums of commutators and `2` and `3` are units, then every product of a positive
  number of factors from `{x, y}` is a sum of commutators.
* `TauCeti.span_pair_pow_fifteen_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0`, then
  the fifteenth power of the span of `{x, y}` is zero.
-/

public section

namespace TauCeti

open Submodule
open scoped Pointwise

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {x y : A}

/-- The reduced words of length `t + 1` for the rewriting rules `x x ↦ 0`, `y y y ↦ 0`,
`y y x ↦ -(y x y + x y y + x y x)` and `y x y x ↦ x y x y`: the words containing none of the four
leading words. There are none of length six. -/
private def cubeZeroWords (x y : A) : ℕ → Set A
  | 0 => {x, y}
  | 1 => {x * y, y * x, y * y}
  | 2 => {x * y * x, x * y * y, y * x * y}
  | 3 => {x * y * x * y, y * x * y * y}
  | 4 => {x * y * x * y * y}
  | _ => ∅

/-- If `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, every product of `t + 1` factors from
`{x, y}` is an integer combination of the reduced words of length `t + 1`. -/
private theorem span_pair_pow_succ_le_span_cubeZeroWords (hx : x ^ 2 = 0) (hy : y ^ 3 = 0)
    (hxy : (x + y) ^ 3 = 0) (t : ℕ) :
    span ℤ {x, y} ^ (t + 1) ≤ span ℤ (cubeZeroWords x y t) := by
  -- The rewriting rules, applied after an arbitrary left factor `a`.
  have r₀ (a : A) : a * x * x = 0 := by rw [mul_assoc, ← sq, hx, mul_zero]
  have r₁ (a : A) : a * y * y * y = 0 := by rw [mul_assoc, mul_assoc, ← pow_three, hy, mul_zero]
  -- Expanding `(x + y) ^ 3` leaves the four words with no `x x` and no `y y y`.
  have r₂ (a : A) : a * y * y * x = -(a * y * x * y + a * x * y * y + a * x * y * x) := by
    linear_combination (norm := skip) a * hxy
    simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, ← mul_assoc, r₀, r₁, zero_add,
      add_zero]
    noncomm_ring
  -- Multiplying the cubic relation by `x` on either side gives `y x y x = x y x y`.
  have r₃ (a : A) : a * y * x * y * x = a * x * y * x * y := by
    linear_combination (norm := skip) r₂ a * x - r₂ (a * x)
    simp only [add_mul, neg_mul, r₀, add_zero]
    noncomm_ring
  have r₀' := r₀ 1
  have r₁' := r₁ 1
  have r₂' := r₂ 1
  have r₃' := r₃ 1
  simp only [one_mul] at r₀' r₁' r₂' r₃'
  -- Each product of a reduced word with `x` or `y` is rewritten to reduced words of the next
  -- length.
  have hS (t : ℕ) : ∀ b ∈ cubeZeroWords x y t,
      b * x ∈ span ℤ (cubeZeroWords x y (t + 1)) ∧ b * y ∈ span ℤ (cubeZeroWords x y (t + 1)) := by
    rcases Nat.lt_or_ge t 5 with ht | ht
    · interval_cases t
      all_goals
        simp only [cubeZeroWords, Set.forall_mem_insert, Set.forall_mem_singleton]
        repeat' apply And.intro
        all_goals try simp only [r₀, r₁, r₂, r₃, r₀', r₁', r₂', r₃', zero_mul, neg_zero, add_zero]
        all_goals repeat' first | exact zero_mem _ | apply add_mem | apply neg_mem |
          exact subset_span (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 5 := ⟨t - 5, by omega⟩
      simp [cubeZeroWords]
  induction t with
  | zero => exact (pow_one _).le
  | succ t ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ?_
    rw [span_mul_span, span_le]
    rintro _ ⟨b, hb, c, hc, rfl⟩
    have h := hS t b hb
    rcases hc with rfl | rfl
    exacts [h.1, h.2]

/-- **A square-zero and a cube-zero element with a cube-zero sum.** If `x ^ 2 = 0`, `y ^ 3 = 0`
and `(x + y) ^ 3 = 0`, then every product of six factors from `{x, y}` vanishes. -/
theorem span_pair_pow_six_eq_bot (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 3 = 0) :
    span R {x, y} ^ 6 = ⊥ := by
  -- There are no reduced words of length six.
  have h6 : span ℤ {x, y} ^ 6 = ⊥ :=
    le_bot_iff.1 <| (span_pair_pow_succ_le_span_cubeZeroWords hx hy hxy 5).trans_eq span_empty
  rw [span_pow, span_eq_bot]
  intro w hw
  have hw' : w ∈ span ℤ {x, y} ^ 6 := span_pow (R := ℤ) {x, y} 6 ▸ subset_span hw
  rwa [h6, mem_bot] at hw'

/-- **Words in a square-zero and a cube-zero element with a cube-zero sum are sums of
commutators.** Let `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, and suppose that `x`, `y`,
`y ^ 2` and `(x + y) ^ 2` lie in the commutator submodule `[B, B]`. If `2` and `3` are units in
`k`, then every product of a positive number of factors from `{x, y}` lies in `[B, B]`.

Up to rotation the reduced words are `x y`, `x y y`, `x y x y` and `x y x y y`, besides the
words with a rotation containing `x x` or `y y y`. Twice `x y` is `(x + y) ^ 2 - y ^ 2` up to
commutators, and three times `x y y` is minus `x y x` up to commutators, by the expansion of
`(x + y) ^ 3`; these are the places where `2` and `3` must be units. Multiplying the expansion by
`x` and by `y ^ 2` on the left gives the two longer words. -/
theorem mem_commutatorSubmodule_of_mem_span_pair_pow {B : Type*} [Ring B] {k : Type*} [Semiring k]
    [Module k B] {x y : B} (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) (hx : x ^ 2 = 0)
    (hy : y ^ 3 = 0) (hxy : (x + y) ^ 3 = 0) (hx₀ : x ∈ commutatorSubmodule k B)
    (hy₀ : y ∈ commutatorSubmodule k B) (hy₁ : y ^ 2 ∈ commutatorSubmodule k B)
    (hs : (x + y) ^ 2 ∈ commutatorSubmodule k B) {t : ℕ} {w : B}
    (hw : w ∈ span ℤ {x, y} ^ (t + 1)) : w ∈ commutatorSubmodule k B := by
  let C := commutatorSubmodule k B
  have hxx : x * x = 0 := by rw [← sq, hx]
  have hyyy : y * y * y = 0 := by rw [← pow_three', hy]
  -- The expansion of `(x + y) ^ 3` with the words containing `x x` or `y y y` removed.
  have r₀ (a : B) : a * x * x = 0 := by rw [mul_assoc, hxx, mul_zero]
  have r₁ (a : B) : a * y * y * y = 0 := by rw [mul_assoc, mul_assoc, ← mul_assoc y, hyyy, mul_zero]
  have hT : x * y * x + x * y * y + y * x * y + y * y * x = 0 := by
    have h : (x + y) ^ 3 = x * x * x + x * x * y + x * y * x + x * y * y + y * x * x +
        y * x * y + y * y * x + y * y * y := by
      noncomm_ring
    simpa only [hxy, hxx, hyyy, r₀, zero_mul, zero_add, add_zero, eq_comm] using h
  -- The commutator submodule is closed under negation and integer multiples.
  have hneg {a : B} (h : a ∈ C) : -a ∈ C := neg_mem_commutatorSubmodule h
  have hzsmul (n : ℤ) {a : B} (h : a ∈ C) : n • a ∈ C := by
    cases n with
    | ofNat m => simpa using C.toAddSubmonoid.nsmul_mem h m
    | negSucc m =>
      rw [negSucc_zsmul]
      exact hneg (C.toAddSubmonoid.nsmul_mem h (m + 1))
  -- Rotations: a product lies in `[B, B]` exactly when its rotation does.
  have hrot {a b : B} (h : b * a ∈ commutatorSubmodule k B) : a * b ∈ commutatorSubmodule k B :=
    mul_mem_commutatorSubmodule_comm.2 h
  have hzero {a : B} (h : a = 0) : a ∈ commutatorSubmodule k B := h ▸ zero_mem _
  have hxyx : x * y * x ∈ commutatorSubmodule k B :=
    hrot (hzero (by rw [← mul_assoc, hxx, zero_mul]))
  -- Twice `x y` is `(x + y) ^ 2 - y ^ 2` plus the commutator `x y - y x`.
  have hxy₀ : x * y ∈ commutatorSubmodule k B := by
    have h : (2 : k) • (x * y) = (x + y) ^ 2 + -y ^ 2 + (x * y - y * x) := by
      rw [two_smul, sq, sq]
      simp only [mul_add, add_mul, hxx]
      abel
    have hmem : (2 : k) • (x * y) ∈ commutatorSubmodule k B := by
      rw [h]
      exact add_mem (add_mem hs (hneg hy₁)) (mul_sub_mul_mem_commutatorSubmodule k B x y)
    exact (Submodule.smul_mem_iff_of_isUnit _ h2).1 hmem
  -- Three times `x y y` is minus `x y x` plus two commutators.
  have hxyy : x * y * y ∈ commutatorSubmodule k B := by
    have h : (3 : k) • (x * y * y) = -(x * y * x) + (x * (y * y) - y * y * x) +
        (x * y * y - y * (x * y)) := by
      rw [show (3 : k) = 2 + 1 by norm_num, add_smul, two_smul, one_smul]
      linear_combination (norm := skip) hT
      noncomm_ring
    have hmem : (3 : k) • (x * y * y) ∈ commutatorSubmodule k B := by
      rw [h]
      exact add_mem (add_mem (hneg hxyx) (mul_sub_mul_mem_commutatorSubmodule k B _ _))
        (mul_sub_mul_mem_commutatorSubmodule k B _ _)
    exact (Submodule.smul_mem_iff_of_isUnit _ h3).1 hmem
  -- `x y x y` is minus `x y y x`, which rotates into `x x y y = 0`.
  have hxyxy : x * y * x * y ∈ commutatorSubmodule k B := by
    have h : x * y * x * y = -(x * y * y * x) := by
      linear_combination (norm := skip) x * hT
      simp only [mul_add, ← mul_assoc, hxx, zero_mul]
      noncomm_ring
    rw [h]
    exact hneg (hrot (hzero (by rw [← mul_assoc, ← mul_assoc, hxx, zero_mul, zero_mul])))
  -- `x y x y y` rotates into `y y x y x`, which is minus `y y x y y`, which rotates into
  -- `x y y y y = 0`.
  have hxyxyy : x * y * x * y * y ∈ commutatorSubmodule k B := by
    have h : y * y * (x * y * x) = -(y * y * (x * y * y)) := by
      linear_combination (norm := skip) y * y * hT
      simp only [mul_add, ← mul_assoc, hyyy, zero_mul]
      noncomm_ring
    have hrot₁ : y * y * (x * y * y) ∈ commutatorSubmodule k B :=
      hrot (hzero (by simp only [← mul_assoc, r₁, zero_mul]))
    have hmem : y * y * (x * y * x) ∈ commutatorSubmodule k B := h ▸ hneg hrot₁
    rw [show x * y * x * y * y = x * y * x * (y * y) by noncomm_ring]
    exact hrot hmem
  -- Every reduced word of positive length lies in `[B, B]`.
  have hwords : ∀ b ∈ cubeZeroWords x y t, b ∈ commutatorSubmodule k B := by
    rcases Nat.lt_or_ge t 5 with ht | ht
    · interval_cases t <;>
        simp only [cubeZeroWords, Set.forall_mem_insert, Set.forall_mem_singleton]
      · exact ⟨hx₀, hy₀⟩
      · exact ⟨hxy₀, hrot hxy₀, by rwa [sq] at hy₁⟩
      · exact ⟨hxyx, hxyy, by rw [mul_assoc]; exact hrot hxyy⟩
      · refine ⟨hxyxy, ?_⟩
        rw [show y * x * y * y = y * (x * y * y) by noncomm_ring]
        exact hrot (hzero (r₁ x))
      · exact hxyxyy
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 5 := ⟨t - 5, by omega⟩
      simp [cubeZeroWords]
  have hle := span_pair_pow_succ_le_span_cubeZeroWords hx hy hxy t hw
  clear hw
  induction hle using Submodule.span_induction with
  | mem b hb => exact hwords b hb
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul n a _ ha => exact hzsmul n ha

/-- **A square-zero and a cube-zero element with a fifth-power-zero sum.** If `x ^ 2 = 0`,
`y ^ 3 = 0` and `(x + y) ^ 5 = 0`, then every product of fifteen factors from `{x, y}`
vanishes. -/
theorem span_pair_pow_fifteen_eq_bot (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 5 = 0) :
    span R {x, y} ^ 15 = ⊥ := by
  -- The rewriting rules, applied after an arbitrary left factor `a`; each rule after the first two
  -- is an integer combination of instances of the previous ones.
  have r₀ (a : A) : a * x * x = 0 := by rw [mul_assoc, ← sq, hx, mul_zero]
  have r₁ (a : A) : a * y * y * y = 0 := by rw [mul_assoc, mul_assoc, ← pow_three, hy, mul_zero]
  have r₂ (a : A) : a * x * y * x * y * x = -(a * x * y * x * y * y + a * x * y * y * x * y +
      a * y * x * y * x * y + a * y * x * y * y * x + a * y * y * x * y * x +
      a * y * y * x * y * y) := by
    linear_combination (norm := skip) a * hxy
    simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, ← mul_assoc, r₀, r₁, zero_add,
      add_zero]
    noncomm_ring
  have r₃ (a : A) : a * x * y * x * y * y * x = -(a * x * y * y * x * y * x) +
      a * y * x * y * x * y * y + a * y * x * y * y * x * y + a * y * y * x * y * x * y := by
    linear_combination (norm := skip) r₂ (a * x) - r₂ a * y
    simp only [add_mul, neg_mul, r₀, r₁, zero_add, add_zero]
    noncomm_ring
  have r₄ (a : A) : a * x * y * y * x * y * y * x * y * x * y =
      -(a * x * y * y * x * y * y * x * y * y * x + a * y * x * y * y * x * y * y * x * y * x +
        a * y * x * y * y * x * y * y * x * y * y + a * y * y * x * y * y * x * y * y * x * y) := by
    linear_combination (norm := skip) -r₃ a * (y * x * y * x) + r₂ (a * x * y * x * y * y) -
      r₃ a * (y * x * y * y) - r₃ a * (y * y * x * y) + r₂ (a * x * y * y) * (y * x) +
      r₂ (a * x * y * y) * (y * y) + r₃ (a * x * y * y) * y - r₃ (a * y * y) * (y * x) -
      r₃ (a * y * y) * (y * y) + r₂ (a * y * y * x * y * y)
    simp only [add_mul, neg_mul, ← mul_assoc, r₁, zero_add, add_zero]
    noncomm_ring
  have r₅ (a : A) : a * x * y * y * x * y * y * x * y * y * x * y * y =
      a * y * x * y * y * x * y * y * x * y * y * x * y -
        a * y * y * x * y * y * x * y * y * x * y * y * x := by
    linear_combination (norm := skip) r₄ a * (y * y) - r₄ (a * y) * y + r₄ (a * y * y)
    simp only [add_mul, neg_mul, ← mul_assoc, r₁, zero_add, add_zero]
    noncomm_ring
  -- The same rules at the left end of a word.
  have r₀' := r₀ 1
  have r₁' := r₁ 1
  have r₂' := r₂ 1
  have r₃' := r₃ 1
  have r₄' := r₄ 1
  have r₅' := r₅ 1
  simp only [one_mul] at r₀' r₁' r₂' r₃' r₄' r₅'
  -- The reduced words of each length `k + 1`: the words containing none of the six leading words.
  let S : ℕ → Set A := fun
    | 0 => {x, y}
    | 1 => {x * y, y * x, y * y}
    | 2 => {x * y * x, x * y * y, y * x * y, y * y * x}
    | 3 => {x * y * x * y, x * y * y * x, y * x * y * x, y * x * y * y, y * y * x * y}
    | 4 => {x * y * x * y * y, x * y * y * x * y, y * x * y * x * y, y * x * y * y * x,
        y * y * x * y * x, y * y * x * y * y}
    | 5 => {x * y * y * x * y * x, x * y * y * x * y * y, y * x * y * x * y * y,
        y * x * y * y * x * y, y * y * x * y * x * y, y * y * x * y * y * x}
    | 6 => {x * y * y * x * y * x * y, x * y * y * x * y * y * x, y * x * y * y * x * y * x,
        y * x * y * y * x * y * y, y * y * x * y * x * y * y, y * y * x * y * y * x * y}
    | 7 => {x * y * y * x * y * x * y * y, x * y * y * x * y * y * x * y,
        y * x * y * y * x * y * x * y, y * x * y * y * x * y * y * x,
        y * y * x * y * y * x * y * x, y * y * x * y * y * x * y * y}
    | 8 => {x * y * y * x * y * y * x * y * x, x * y * y * x * y * y * x * y * y,
        y * x * y * y * x * y * x * y * y, y * x * y * y * x * y * y * x * y,
        y * y * x * y * y * x * y * x * y, y * y * x * y * y * x * y * y * x}
    | 9 => {x * y * y * x * y * y * x * y * y * x, y * x * y * y * x * y * y * x * y * x,
        y * x * y * y * x * y * y * x * y * y, y * y * x * y * y * x * y * x * y * y,
        y * y * x * y * y * x * y * y * x * y}
    | 10 => {x * y * y * x * y * y * x * y * y * x * y, y * x * y * y * x * y * y * x * y * y * x,
        y * y * x * y * y * x * y * y * x * y * x, y * y * x * y * y * x * y * y * x * y * y}
    | 11 => {x * y * y * x * y * y * x * y * y * x * y * x,
        y * x * y * y * x * y * y * x * y * y * x * y,
        y * y * x * y * y * x * y * y * x * y * y * x}
    | 12 => {y * x * y * y * x * y * y * x * y * y * x * y * x,
        y * y * x * y * y * x * y * y * x * y * y * x * y}
    | 13 => {y * y * x * y * y * x * y * y * x * y * y * x * y * x}
    | _ => ∅
  -- Each product of a reduced word with `x` or `y` is rewritten to reduced words of the next
  -- length.
  have hS (k : ℕ) (hk : k < 14) :
      ∀ b ∈ S k, b * x ∈ span ℤ (S (k + 1)) ∧ b * y ∈ span ℤ (S (k + 1)) := by
    interval_cases k
    all_goals
      simp only [S, Set.forall_mem_insert, Set.forall_mem_singleton]
      repeat' apply And.intro
      all_goals try simp only [r₀, r₁, r₂, r₃, r₄, r₅, r₀', r₁', r₂', r₃', r₄', r₅',
        sub_mul, zero_mul, neg_zero, add_zero, sub_zero]
      all_goals repeat' first | exact zero_mem _ | apply add_mem | apply sub_mem | apply neg_mem |
        exact subset_span (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
  -- Hence the products of each length lie in the integer span of the reduced words.
  have hspan (k : ℕ) (hk : k < 15) : span ℤ {x, y} ^ (k + 1) ≤ span ℤ (S k) := by
    induction k with
    | zero => exact (pow_one _).le
    | succ k ih =>
      rw [pow_succ]
      refine (mul_le_mul' (ih (by omega)) le_rfl).trans ?_
      rw [span_mul_span, span_le]
      rintro _ ⟨b, hb, c, hc, rfl⟩
      have h := hS k (by omega) b hb
      rcases hc with rfl | rfl
      exacts [h.1, h.2]
  -- There are no reduced words of length fifteen.
  have h15 : span ℤ {x, y} ^ 15 = ⊥ := le_bot_iff.1 <| (hspan 14 (by norm_num)).trans_eq span_empty
  rw [span_pow, span_eq_bot]
  intro w hw
  have hw' : w ∈ span ℤ {x, y} ^ 15 := span_pow (R := ℤ) {x, y} 15 ▸ subset_span hw
  rwa [h15, mem_bot] at hw'

end TauCeti
