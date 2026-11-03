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
import Mathlib.Tactic.Module
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

For `(x + y) ^ 4 = 0`, use the degree-lexicographic order with `y < x`. Expanding the fourth power
leaves the five surviving words of length four, which give a rule for `x y x y`; its overlap with
`y y y` gives one more rule, for `x y y x y y`. The reduced words number `2, 3, 4, 4, 4, 3, 2, 1`
in the lengths one to eight, and there are none of length nine.

These are the relations satisfied at the branch node of the `E₆`, `E₇` and `E₈` diagrams by the
backtracks into their arms of lengths one and two, in the preprojective algebra: the backtrack into
the third arm, of length two for `E₆`, three for `E₇` and four for `E₈`, is `-(x + y)`.

For `(x + y) ^ 4 = 0` the reduced words also control the cyclic quotient `A / [A, A]` of the
ambient ring: if `x`, `y`, `y ^ 2`, `(x + y) ^ 2` and `(x + y) ^ 3` are sums of commutators and `2`
and `3` are units, then so is every product of a positive number of factors from `{x, y}`. Since
`(x + y) ^ 3 = 0` implies `(x + y) ^ 4 = 0`, this also covers the cube-zero case. This is the step
at the branch node in the vanishing of the cyclic quotient of the `E₆` and `E₇` preprojective
algebras in positive degrees.

For `(x + y) ^ 5 = 0` the same holds if `x`, `y`, `y ^ 2` and the powers `(x + y) ^ j` for
`2 ≤ j < 5` are sums of commutators and `2`, `3` and `5` are units. In each length, the commutators
of `x` and of `y` with the reduced words of the previous length, rewritten into reduced words, and
in lengths at most four the hypotheses, are integer relations among the reduced words modulo
`[A, A]`. In every length from one to fourteen they express `1`, `2`, `3` or `5` times each reduced
word as a sum of commutators: the factor `5` occurs for `x y x y y`, through the expansion of
`(x + y) ^ 5` itself. This is the step at the branch node for the `E₈` preprojective algebra.

## Main results

* `TauCeti.span_pair_pow_six_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, then the
  sixth power of the span of `{x, y}` is zero.
* `TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four`: if `x ^ 2 = 0`,
  `y ^ 3 = 0` and `(x + y) ^ 4 = 0`, if `x`, `y`, `y ^ 2`, `(x + y) ^ 2` and `(x + y) ^ 3` are sums
  of commutators, and if `2` and `3` are units, then every product of a positive number of factors
  from `{x, y}` is a sum of commutators.
* `TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow`: the same conclusion if `(x + y) ^ 3 = 0`,
  assuming only `x`, `y`, `y ^ 2` and `(x + y) ^ 2` are sums of commutators.
* `TauCeti.span_pair_pow_fifteen_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0`, then
  the fifteenth power of the span of `{x, y}` is zero.
* `TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_five`: if moreover `x`, `y`,
  `y ^ 2`, `(x + y) ^ 2`, `(x + y) ^ 3` and `(x + y) ^ 4` are sums of commutators and `2`, `3` and
  `5` are units, then every product of a positive number of factors from `{x, y}` is a sum of
  commutators.
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

/-- The reduced words of length `t + 1` for the rewriting rules `x x ↦ 0`, `y y y ↦ 0`,
`x y x y ↦ -(x y y x + y x y x + y x y y + y y x y)` and
`x y y x y y ↦ y x y y x y - y y x y y x`: the words containing none of the four leading words.
There are none of length nine. -/
private def quarticWords (x y : A) : ℕ → Set A
  | 0 => {x, y}
  | 1 => {x * y, y * x, y * y}
  | 2 => {x * y * x, x * y * y, y * x * y, y * y * x}
  | 3 => {x * y * y * x, y * x * y * x, y * x * y * y, y * y * x * y}
  | 4 => {x * y * y * x * y, y * x * y * y * x, y * y * x * y * x, y * y * x * y * y}
  | 5 => {x * y * y * x * y * x, y * x * y * y * x * y, y * y * x * y * y * x}
  | 6 => {y * x * y * y * x * y * x, y * y * x * y * y * x * y}
  | 7 => {y * y * x * y * y * x * y * x}
  | _ => ∅

/-- If `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 4 = 0`, every product of `t + 1` factors from
`{x, y}` is an integer combination of the reduced words of length `t + 1`. -/
private theorem span_pair_pow_succ_le_span_quarticWords (hx : x ^ 2 = 0) (hy : y ^ 3 = 0)
    (hxy : (x + y) ^ 4 = 0) (t : ℕ) :
    span ℤ {x, y} ^ (t + 1) ≤ span ℤ (quarticWords x y t) := by
  -- The rewriting rules, applied after an arbitrary left factor `a`.
  have r₀ (a : A) : a * x * x = 0 := by rw [mul_assoc, ← sq, hx, mul_zero]
  have r₁ (a : A) : a * y * y * y = 0 := by rw [mul_assoc, mul_assoc, ← pow_three, hy, mul_zero]
  -- Expanding `(x + y) ^ 4` leaves the five words with no `x x` and no `y y y`.
  have r₂ (a : A) : a * x * y * x * y =
      -(a * x * y * y * x + a * y * x * y * x + a * y * x * y * y + a * y * y * x * y) := by
    linear_combination (norm := skip) a * hxy
    simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, ← mul_assoc, r₀, r₁, zero_add,
      add_zero]
    noncomm_ring
  -- The overlap of `x y x y` with `y y y` gives the last rule.
  have r₃ (a : A) : a * x * y * y * x * y * y =
      a * y * x * y * y * x * y - a * y * y * x * y * y * x := by
    linear_combination (norm := skip) r₂ a * (y * y) - r₂ (a * y) * y + r₂ (a * y * y)
    simp only [add_mul, neg_mul, ← mul_assoc, r₁, zero_add, add_zero]
    noncomm_ring
  have r₀' := r₀ 1
  have r₁' := r₁ 1
  have r₂' := r₂ 1
  have r₃' := r₃ 1
  simp only [one_mul] at r₀' r₁' r₂' r₃'
  -- Each product of a reduced word with `x` or `y` is rewritten to reduced words of the next
  -- length.
  have hS (t : ℕ) : ∀ b ∈ quarticWords x y t,
      b * x ∈ span ℤ (quarticWords x y (t + 1)) ∧ b * y ∈ span ℤ (quarticWords x y (t + 1)) := by
    rcases Nat.lt_or_ge t 8 with ht | ht
    · interval_cases t
      all_goals
        simp only [quarticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
        repeat' apply And.intro
        all_goals try simp only [r₀, r₁, r₂, r₃, r₀', r₁', r₂', r₃', sub_mul, zero_mul,
          neg_zero, add_zero, sub_zero]
        all_goals repeat' first
          | exact zero_mem _
          | apply add_mem
          | apply sub_mem
          | apply neg_mem
          | exact subset_span (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 8 := ⟨t - 8, by omega⟩
      simp [quarticWords]
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

/-- **Words in a square-zero and a cube-zero element with a fourth-power-zero sum are sums of
commutators.** Let `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 4 = 0`, and suppose that `x`, `y`,
`y ^ 2`, `(x + y) ^ 2` and `(x + y) ^ 3` lie in the commutator submodule `[B, B]`. If `2` and `3`
are units in `k`, then every product of a positive number of factors from `{x, y}` lies in
`[B, B]`.

Up to rotation, the reduced words not containing `x x` or `y y y` cyclically are the products of
the blocks `a = x y` and `b = x y y`. Twice `a` is `(x + y) ^ 2 - y ^ 2` up to commutators, three
times `b` is `(x + y) ^ 3` up to commutators and `x y x`, and twice `a a` is a sum of commutators
by the expansion of `(x + y) ^ 4`; these are the places where `2` and `3` must be units.
Multiplying that expansion on the left by `y - x`, `y y`, `x y y` and `x y y x` gives `a b`,
`b b`, `a a b` and twice `a b b`. -/
theorem mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four {B : Type*} [Ring B]
    {k : Type*} [Semiring k] [Module k B] {x y : B} (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 4 = 0) (hx₀ : x ∈ commutatorSubmodule k B)
    (hy₀ : y ∈ commutatorSubmodule k B) (hy₁ : y ^ 2 ∈ commutatorSubmodule k B)
    (hs : (x + y) ^ 2 ∈ commutatorSubmodule k B) (hc : (x + y) ^ 3 ∈ commutatorSubmodule k B)
    {t : ℕ} {w : B} (hw : w ∈ span ℤ {x, y} ^ (t + 1)) : w ∈ commutatorSubmodule k B := by
  let C := commutatorSubmodule k B
  have hxx : x * x = 0 := by rw [← sq, hx]
  have hyyy : y * y * y = 0 := by rw [← pow_three', hy]
  have r₀ (a : B) : a * x * x = 0 := by rw [mul_assoc, hxx, mul_zero]
  have r₁ (a : B) : a * y * y * y = 0 := by rw [mul_assoc, mul_assoc, ← mul_assoc y, hyyy, mul_zero]
  -- The expansions of `(x + y) ^ 3` and `(x + y) ^ 4` with the words containing `x x` or `y y y`
  -- removed.
  have hcube : (x + y) ^ 3 = x * y * x + x * y * y + y * x * y + y * y * x := by
    simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, hxx, hyyy, r₀, zero_add, add_zero]
    noncomm_ring
  have hT : x * y * x * y + x * y * y * x + y * x * y * x + y * x * y * y + y * y * x * y = 0 := by
    linear_combination (norm := skip) hxy
    simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, hxx, hyyy, r₀, r₁, zero_add,
      add_zero]
    noncomm_ring
  have hneg {a : B} (h : a ∈ C) : -a ∈ C := neg_mem_commutatorSubmodule h
  -- Rotations: a product lies in `[B, B]` exactly when its rotation does, here up to
  -- reassociating the rotated product or the target.
  have hrot {a b : B} (h : b * a ∈ C) : a * b ∈ C := mul_mem_commutatorSubmodule_comm.2 h
  have hrotEq {a b c : B} (e : b * a = c) (h : c ∈ C) : a * b ∈ C := hrot (e ▸ h)
  have hrotAssoc {a b c : B} (e : a * b = c) (h : b * a ∈ C) : c ∈ C := e ▸ hrot h
  have hzero {a : B} (h : a = 0) : a ∈ C := h ▸ zero_mem _
  have hcomm (a b : B) : a * b - b * a ∈ C := mul_sub_mul_mem_commutatorSubmodule k B a b
  -- Length two: twice `x y` is `(x + y) ^ 2 - y ^ 2` plus the commutator `x y - y x`.
  have hxy₀ : x * y ∈ C := by
    have h : (2 : k) • (x * y) = (x + y) ^ 2 + -y ^ 2 + (x * y - y * x) := by
      rw [two_smul, sq, sq]
      simp only [mul_add, add_mul, hxx]
      abel
    have hmem : (2 : k) • (x * y) ∈ C := by
      rw [h]
      exact add_mem (add_mem hs (hneg hy₁)) (hcomm x y)
    exact (Submodule.smul_mem_iff_of_isUnit _ h2).1 hmem
  -- Length three: `x y x` rotates into `x x y = 0`, and three times `x y y` is `(x + y) ^ 3`
  -- minus `x y x` up to two commutators.
  have hxyx : x * y * x ∈ C := hrot (hzero (by rw [← mul_assoc, hxx, zero_mul]))
  have hxyy : x * y * y ∈ C := by
    have h : (3 : k) • (x * y * y) = (x + y) ^ 3 + -(x * y * x) + -(y * (x * y) - x * y * y) +
        -(y * y * x - x * (y * y)) := by
      rw [hcube, ← two_add_one_eq_three, add_smul, two_smul, one_smul]
      noncomm_ring
    have hmem : (3 : k) • (x * y * y) ∈ C := by
      rw [h]
      exact add_mem (add_mem (add_mem hc (hneg hxyx)) (hneg (hcomm _ _))) (hneg (hcomm _ _))
    exact (Submodule.smul_mem_iff_of_isUnit _ h3).1 hmem
  -- Length four: `x y y x`, `y x y y` and `y y x y` rotate into words containing `x x` or
  -- `y y y`, and then twice `y x y x` is a sum of commutators.
  have hxyyx : x * y * y * x ∈ C := hrot (hzero (by simp only [← mul_assoc, hxx, zero_mul]))
  have hyxyy : y * x * y * y ∈ C := hrotAssoc (by simp only [mul_assoc]) (hzero (r₁ x))
  have hyyxy : y * y * x * y ∈ C := hrotAssoc (by simp only [mul_assoc]) hyxyy
  have hyxyx : y * x * y * x ∈ C := by
    have h : (2 : k) • (y * x * y * x) = -(x * (y * x * y) - y * x * y * x) + -(x * y * y * x) +
        -(y * x * y * y) + -(y * y * x * y) := by
      rw [two_smul]
      linear_combination (norm := skip) hT
      noncomm_ring
    have hmem : (2 : k) • (y * x * y * x) ∈ C := by
      rw [h]
      exact add_mem (add_mem (add_mem (hneg (hcomm _ _)) (hneg hxyyx)) (hneg hyxyy)) (hneg hyyxy)
    exact (Submodule.smul_mem_iff_of_isUnit _ h2).1 hmem
  -- Length five: the difference of the expansion multiplied by `y` and by `x` leaves `x y y x y`
  -- up to commutators and words rotating into `x x` or `y y y`.
  have hyyxyy : y * y * x * y * y ∈ C :=
    hrotAssoc (by simp only [mul_assoc]) (hzero (r₁ (y * x)))
  have hxyxyx : x * y * x * y * x ∈ C :=
    hrotAssoc (by simp only [mul_assoc]) (hzero (r₀ (y * x * y)))
  have hxyyxy : x * y * y * x * y ∈ C := by
    have h : x * y * y * x * y = -(y * (x * y * x * y) - x * y * x * y * y) +
        -(y * (x * y * y * x) - x * y * y * x * y) + -(y * y * x * y * x - x * (y * y * x * y)) +
        -(y * y * x * y * y) + x * y * x * y * x := by
      linear_combination (norm := skip) y * hT - x * hT
      simp only [mul_add, ← mul_assoc, hxx, hyyy, zero_mul, zero_add, add_zero]
      noncomm_ring
    rw [h]
    exact add_mem (add_mem (add_mem (add_mem (hneg (hcomm _ _)) (hneg (hcomm _ _)))
      (hneg (hcomm _ _))) (hneg hyyxyy)) hxyxyx
  -- Length six: the expansion multiplied by `y y` leaves `y y x y y x` up to a word rotating into
  -- `y y y`.
  have hyyxyyx : y * y * x * y * y * x ∈ C := by
    have h : y * y * x * y * y * x = -(y * y * (x * y * x * y)) := by
      linear_combination (norm := skip) y * y * hT
      simp only [mul_add, ← mul_assoc, hyyy, zero_mul, add_zero]
      noncomm_ring
    rw [h]
    exact hneg (hrot (hzero (by simp only [← mul_assoc, r₁])))
  -- Length seven: the expansion multiplied by `x y y` leaves `x y y x y x y` up to a word rotating
  -- into `x x`.
  have hxyyxyxy : x * y * y * x * y * x * y ∈ C := by
    have h : x * y * y * x * y * x * y = -(x * y * y * x * y * y * x) := by
      linear_combination (norm := skip) x * y * y * hT
      simp only [mul_add, ← mul_assoc, r₁, zero_mul, add_zero]
      noncomm_ring
    rw [h]
    exact hneg (hrot (hzero (by simp only [← mul_assoc, hxx, zero_mul])))
  -- Length eight: the expansion multiplied by `x y y x` shows that twice `y y x y y x y x` is a
  -- sum of commutators and a word rotating into `x x`.
  have hxyyxyxyx : x * y * y * x * y * x * y * x ∈ C := by
    exact hrot (hzero (by simp only [← mul_assoc, hxx, zero_mul]))
  have hyyxyyxyx : y * y * x * y * y * x * y * x ∈ C := by
    have h : (2 : k) • (y * y * x * y * y * x * y * x) =
        -(x * y * y * x * y * x * (y * y) - y * y * (x * y * y * x * y * x)) +
        -(x * (y * y * x * y * y * x * y) - y * y * x * y * y * x * y * x) +
        -(x * y * y * x * y * x * y * x) := by
      rw [two_smul]
      linear_combination (norm := skip) x * y * y * x * hT
      simp only [mul_add, ← mul_assoc, r₀, zero_mul, zero_add, add_zero]
      noncomm_ring
    have hmem : (2 : k) • (y * y * x * y * y * x * y * x) ∈ C := by
      rw [h]
      exact add_mem (add_mem (hneg (hcomm _ _)) (hneg (hcomm _ _))) (hneg hxyyxyxyx)
    exact (Submodule.smul_mem_iff_of_isUnit _ h2).1 hmem
  -- Every reduced word of positive length lies in `[B, B]`.
  have hwords : ∀ b ∈ quarticWords x y t, b ∈ C := by
    rcases Nat.lt_or_ge t 8 with ht | ht
    · interval_cases t <;>
        simp only [quarticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
      · exact ⟨hx₀, hy₀⟩
      · exact ⟨hxy₀, hrot hxy₀, by rwa [sq] at hy₁⟩
      · refine ⟨hxyx, hxyy, ?_, ?_⟩
        · rw [mul_assoc]
          exact hrot hxyy
        · exact hrot (by rw [← mul_assoc]; exact hxyy)
      · exact ⟨hxyyx, hyxyx, hyxyy, hyyxy⟩
      · exact ⟨hxyyxy, hrotAssoc (by simp only [mul_assoc]) hxyyxy,
          hrotEq (by noncomm_ring) hxyyxy, hyyxyy⟩
      · exact ⟨hrot (hzero (by simp only [← mul_assoc, hxx, zero_mul])),
          hrotEq (by simp only [mul_assoc]) hyyxyyx, hyyxyyx⟩
      · exact ⟨hrotAssoc (by simp only [mul_assoc]) hxyyxyxy,
          hrot (hzero (by simp only [← mul_assoc, hyyy, zero_mul]))⟩
      · exact hyyxyyxyx
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 8 := ⟨t - 8, by omega⟩
      simp [quarticWords]
  have hle := span_pair_pow_succ_le_span_quarticWords hx hy hxy t hw
  clear hw
  induction hle using Submodule.span_induction with
  | mem b hb => exact hwords b hb
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul n a _ ha => exact zsmul_mem_commutatorSubmodule ha n

/-- **Words in a square-zero and a cube-zero element with a cube-zero sum are sums of
commutators.** Let `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, and suppose that `x`, `y`,
`y ^ 2` and `(x + y) ^ 2` lie in the commutator submodule `[B, B]`. If `2` and `3` are units in
`k`, then every product of a positive number of factors from `{x, y}` lies in `[B, B]`.

This is the case `(x + y) ^ 3 = 0` of
`mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four`. -/
theorem mem_commutatorSubmodule_of_mem_span_pair_pow {B : Type*} [Ring B] {k : Type*} [Semiring k]
    [Module k B] {x y : B} (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) (hx : x ^ 2 = 0)
    (hy : y ^ 3 = 0) (hxy : (x + y) ^ 3 = 0) (hx₀ : x ∈ commutatorSubmodule k B)
    (hy₀ : y ∈ commutatorSubmodule k B) (hy₁ : y ^ 2 ∈ commutatorSubmodule k B)
    (hs : (x + y) ^ 2 ∈ commutatorSubmodule k B) {t : ℕ} {w : B}
    (hw : w ∈ span ℤ {x, y} ^ (t + 1)) : w ∈ commutatorSubmodule k B :=
  mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four h2 h3 hx hy
    (by rw [pow_succ, hxy, zero_mul]) hx₀ hy₀ hy₁ hs (hxy ▸ zero_mem _) hw

/-- The rewriting rules for `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0` in the
degree-lexicographic order with `y < x`, applied after an arbitrary left factor `a`. The third is
the expansion of `(x + y) ^ 5`, and each later rule is an integer combination of instances of the
previous ones. -/
private theorem quintic_rewriting_rules (hx : x ^ 2 = 0) (hy : y ^ 3 = 0)
    (hxy : (x + y) ^ 5 = 0) :
    (∀ a : A, a * x * x = 0) ∧ (∀ a : A, a * y * y * y = 0) ∧
    (∀ a : A, a * x * y * x * y * x = -(a * x * y * x * y * y + a * x * y * y * x * y +
      a * y * x * y * x * y + a * y * x * y * y * x + a * y * y * x * y * x +
      a * y * y * x * y * y)) ∧
    (∀ a : A, a * x * y * x * y * y * x = -(a * x * y * y * x * y * x) +
      a * y * x * y * x * y * y + a * y * x * y * y * x * y + a * y * y * x * y * x * y) ∧
    (∀ a : A, a * x * y * y * x * y * y * x * y * x * y =
      -(a * x * y * y * x * y * y * x * y * y * x + a * y * x * y * y * x * y * y * x * y * x +
        a * y * x * y * y * x * y * y * x * y * y + a * y * y * x * y * y * x * y * y * x * y)) ∧
    (∀ a : A, a * x * y * y * x * y * y * x * y * y * x * y * y =
      a * y * x * y * y * x * y * y * x * y * y * x * y -
        a * y * y * x * y * y * x * y * y * x * y * y * x) := by
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
  refine ⟨r₀, r₁, r₂, r₃, r₄, fun a => ?_⟩
  linear_combination (norm := skip) r₄ a * (y * y) - r₄ (a * y) * y + r₄ (a * y * y)
  simp only [add_mul, neg_mul, ← mul_assoc, r₁, zero_add, add_zero]
  noncomm_ring

/-- The reduced words of length `t + 1` for the rewriting rules of
`quintic_rewriting_rules`: the words containing none of the six leading words `x x`, `y y y`,
`x y x y x`, `x y x y y x`, `x y y x y y x y x y` and `x y y x y y x y y x y y`. There are none
of length fifteen. -/
private def quinticWords (x y : A) : ℕ → Set A
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

/-- If `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0`, every product of `t + 1` factors from
`{x, y}` is an integer combination of the reduced words of length `t + 1`. -/
private theorem span_pair_pow_succ_le_span_quinticWords (hx : x ^ 2 = 0) (hy : y ^ 3 = 0)
    (hxy : (x + y) ^ 5 = 0) (t : ℕ) :
    span ℤ {x, y} ^ (t + 1) ≤ span ℤ (quinticWords x y t) := by
  obtain ⟨r₀, r₁, r₂, r₃, r₄, r₅⟩ := quintic_rewriting_rules hx hy hxy
  -- The same rules at the left end of a word.
  have r₀' := r₀ 1
  have r₁' := r₁ 1
  have r₂' := r₂ 1
  have r₃' := r₃ 1
  have r₄' := r₄ 1
  have r₅' := r₅ 1
  simp only [one_mul] at r₀' r₁' r₂' r₃' r₄' r₅'
  -- Each product of a reduced word with `x` or `y` is rewritten to reduced words of the next
  -- length.
  have hS (t : ℕ) : ∀ b ∈ quinticWords x y t,
      b * x ∈ span ℤ (quinticWords x y (t + 1)) ∧ b * y ∈ span ℤ (quinticWords x y (t + 1)) := by
    rcases Nat.lt_or_ge t 14 with ht | ht
    · interval_cases t
      all_goals
        simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
        repeat' apply And.intro
        all_goals try simp only [r₀, r₁, r₂, r₃, r₄, r₅, r₀', r₁', r₂', r₃', r₄', r₅',
          sub_mul, zero_mul, neg_zero, add_zero, sub_zero]
        all_goals repeat' first
          | exact zero_mem _
          | apply add_mem
          | apply sub_mem
          | apply neg_mem
          | exact subset_span (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 14 := ⟨t - 14, by omega⟩
      simp [quinticWords]
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

/-- **A square-zero and a cube-zero element with a fifth-power-zero sum.** If `x ^ 2 = 0`,
`y ^ 3 = 0` and `(x + y) ^ 5 = 0`, then every product of fifteen factors from `{x, y}`
vanishes. -/
theorem span_pair_pow_fifteen_eq_bot (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 5 = 0) :
    span R {x, y} ^ 15 = ⊥ := by
  -- There are no reduced words of length fifteen.
  have h15 : span ℤ {x, y} ^ 15 = ⊥ :=
    le_bot_iff.1 <| (span_pair_pow_succ_le_span_quinticWords hx hy hxy 14).trans_eq span_empty
  rw [span_pow, span_eq_bot]
  intro w hw
  have hw' : w ∈ span ℤ {x, y} ^ 15 := span_pow (R := ℤ) {x, y} 15 ▸ subset_span hw
  rwa [h15, mem_bot] at hw'

/-- **Words in a square-zero and a cube-zero element with a fifth-power-zero sum are sums of
commutators.** Let `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0`, and suppose that `x`, `y`,
`y ^ 2` and the powers `(x + y) ^ j` for `2 ≤ j < 5` lie in the commutator submodule `[B, B]`. If
`2`, `3` and `5` are units in `k`, then every product of a positive number of factors from
`{x, y}` lies in `[B, B]`. -/
theorem mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_five {B : Type*} [Ring B]
    {k : Type*} [Semiring k] [Module k B] {x y : B} (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    (h5 : IsUnit (5 : k)) (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 5 = 0)
    (hx₀ : x ∈ commutatorSubmodule k B) (hy₀ : y ∈ commutatorSubmodule k B)
    (hy₁ : y ^ 2 ∈ commutatorSubmodule k B) (hs : (x + y) ^ 2 ∈ commutatorSubmodule k B)
    (hc : (x + y) ^ 3 ∈ commutatorSubmodule k B) (hq : (x + y) ^ 4 ∈ commutatorSubmodule k B)
    {t : ℕ} {w : B} (hw : w ∈ span ℤ {x, y} ^ (t + 1)) : w ∈ commutatorSubmodule k B := by
  obtain ⟨r₀, r₁, r₂, r₃, r₄, r₅⟩ := quintic_rewriting_rules hx hy hxy
  have r₀' := r₀ 1
  have r₁' := r₁ 1
  have r₂' := r₂ 1
  have r₃' := r₃ 1
  have r₄' := r₄ 1
  have r₅' := r₅ 1
  simp only [one_mul] at r₀' r₁' r₂' r₃' r₄' r₅'
  -- Work in the quotient of `B` by the commutator submodule, viewed as an additive subgroup.
  let C := commutatorSubmodule k B
  let D : AddSubgroup B := { C.toAddSubmonoid with neg_mem' := neg_mem_commutatorSubmodule }
  have hD {a : B} : a ∈ D ↔ a ∈ C := Iff.rfl
  let f := QuotientAddGroup.mk' D
  have hf {a : B} (h : a ∈ C) : f a = 0 := (QuotientAddGroup.eq_zero_iff a).2 (hD.2 h)
  -- Rotating a product does not change its class.
  have hrot (a b : B) : f (a * b) = f (b * a) := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq, hD,
      neg_add_eq_sub]
    exact mul_sub_mul_mem_commutatorSubmodule k B b a
  -- A class killed by a unit multiple vanishes.
  have hdiv {n : ℕ} (hn : IsUnit (n : k)) {a : B} (h : (n : ℤ) • f a = 0) : f a = 0 := by
    rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, hD, natCast_zsmul,
      ← Nat.cast_smul_eq_nsmul k] at h
    exact hf ((Submodule.smul_mem_iff_of_isUnit _ hn).1 h)
  have u2 : IsUnit ((2 : ℕ) : k) := by exact_mod_cast h2
  have u3 : IsUnit ((3 : ℕ) : k) := by exact_mod_cast h3
  have u5 : IsUnit ((5 : ℕ) : k) := by exact_mod_cast h5
  -- In each length `d`, every `eᵢ` is a relation `f (a * v) = f (v * a)` for a letter `a` and a
  -- reduced word `v` of length `d - 1`, or for `d ≤ 4` a hypothesis, rewritten into reduced words.
  -- Every `wⱼ` solves these relations, and the previous `wᵢ`, for one reduced word of length `d`.
  -- Length 1.
  have l₁ : ∀ b ∈ quinticWords x y 0, f b = 0 := by
    have w₁ : f x = 0 := hf hx₀
    have w₂ : f y = 0 := hf hy₀
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₂⟩
  -- Length 2.
  have l₂ : ∀ b ∈ quinticWords x y 1, f b = 0 := by
    have e₁ := hf hs
    have e₂ := hrot y x
    simp only [pow_succ, pow_zero, one_mul, mul_add, r₀', add_mul, zero_add, map_add] at e₁ e₂
    have w₁ : f (y * y) = 0 := hf (by rwa [← sq])
    have w₂ : f (x * y) = 0 := hdiv u2 <| by linear_combination (norm := module) e₁ - e₂ - w₁
    have w₃ : f (y * x) = 0 := by linear_combination (norm := module) e₂ + w₂
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₂, w₃, w₁⟩
  -- Length 3.
  have l₃ : ∀ b ∈ quinticWords x y 2, f b = 0 := by
    have e₁ := hrot x (x * y)
    have e₂ := hf hc
    have e₃ := hrot y (x * y)
    have e₄ := hrot x (y * y)
    have e₅ := hrot y (y * x)
    simp only [pow_succ, pow_zero, one_mul, mul_add, ← mul_assoc, r₀, r₀', r₁', add_mul, zero_mul,
      add_zero, zero_add, map_add, map_zero] at e₁ e₂ e₃ e₄ e₅
    have w₁ : f (x * y * x) = 0 := by linear_combination (norm := module) -e₁
    have w₂ : f (x * y * y) = 0 := hdiv u3 <| by
      linear_combination (norm := module) e₂ - e₃ + e₄ - w₁
    have w₃ : f (y * x * y) = 0 := by linear_combination (norm := module) e₃ + w₂
    have w₄ : f (y * y * x) = 0 := by linear_combination (norm := module) e₅ + w₃
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₂, w₃, w₄⟩
  -- Length 4.
  have l₄ : ∀ b ∈ quinticWords x y 3, f b = 0 := by
    have e₁ := hrot x (x * y * y)
    have e₂ := hrot y (x * y * y)
    have e₃ := hrot y (y * y * x)
    have e₄ := hf hq
    have e₅ := hrot y (x * y * x)
    simp only [pow_succ, pow_zero, one_mul, mul_add, ← mul_assoc, r₀, r₁, r₀', r₁', add_mul,
      zero_mul, add_zero, zero_add, map_add, map_zero] at e₁ e₂ e₃ e₄ e₅
    have w₁ : f (x * y * y * x) = 0 := by linear_combination (norm := module) -e₁
    have w₂ : f (y * x * y * y) = 0 := by linear_combination (norm := module) e₂
    have w₃ : f (y * y * x * y) = 0 := by linear_combination (norm := module) -e₃
    have w₄ : f (x * y * x * y) = 0 := hdiv u2 <| by
      linear_combination (norm := module) e₄ - e₅ - w₁ - w₂ - w₃
    have w₅ : f (y * x * y * x) = 0 := by linear_combination (norm := module) e₅ + w₄
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₄, w₁, w₅, w₂, w₃⟩
  -- Length 5.
  have l₅ : ∀ b ∈ quinticWords x y 4, f b = 0 := by
    have e₁ := hrot y (y * x * y * y)
    have e₂ := hrot x (x * y * x * y)
    have e₃ := hrot y (x * y * x * y)
    have e₄ := hrot y (x * y * y * x)
    have e₅ := hrot y (y * x * y * x)
    have e₆ := hrot x (y * x * y * y)
    simp only [← mul_assoc, r₁, r₀', r₂', zero_mul, map_add, map_neg, map_zero] at e₁ e₂ e₃ e₄ e₅ e₆
    have w₁ : f (y * y * x * y * y) = 0 := by linear_combination (norm := module) e₁
    have w₂ : f (x * y * x * y * y) = 0 := hdiv u5 <| by
      linear_combination (norm := module) e₂ - 2 • e₃ + e₄ - e₅ + 2 • e₆ - w₁
    have w₃ : f (y * x * y * x * y) = 0 := by linear_combination (norm := module) e₃ + w₂
    have w₄ : f (y * x * y * y * x) = 0 := by linear_combination (norm := module) -e₆ + w₂
    have w₅ : f (x * y * y * x * y) = 0 := by linear_combination (norm := module) -e₄ + w₄
    have w₆ : f (y * y * x * y * x) = 0 := by linear_combination (norm := module) e₅ + w₃
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₂, w₅, w₃, w₄, w₆, w₁⟩
  -- Length 6.
  have l₆ : ∀ b ∈ quinticWords x y 5, f b = 0 := by
    have e₁ := hrot x (x * y * y * x * y)
    have e₂ := hrot y (x * y * x * y * y)
    have e₃ := hrot y (y * y * x * y * x)
    have e₄ := hrot x (x * y * x * y * y)
    have e₅ := hrot y (x * y * y * x * y)
    have e₆ := hrot x (y * x * y * x * y)
    simp only [← mul_assoc, r₁, r₂, r₀', r₁', r₂', r₃', add_mul, neg_mul, zero_mul, add_zero,
      zero_add, map_add, map_neg, map_zero] at e₁ e₂ e₃ e₄ e₅ e₆
    have w₁ : f (x * y * y * x * y * x) = 0 := by linear_combination (norm := module) -e₁
    have w₂ : f (y * x * y * x * y * y) = 0 := by linear_combination (norm := module) e₂
    have w₃ : f (y * y * x * y * x * y) = 0 := by linear_combination (norm := module) -e₃
    have w₄ : f (y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) -e₄ + w₁ - w₂ - w₃
    have w₅ : f (x * y * y * x * y * y) = 0 := by linear_combination (norm := module) -e₅ + w₄
    have w₆ : f (y * y * x * y * y * x) = 0 := by linear_combination (norm := module) e₆ + w₅
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₅, w₂, w₄, w₃, w₆⟩
  -- Length 7.
  have l₇ : ∀ b ∈ quinticWords x y 6, f b = 0 := by
    have e₁ := hrot x (x * y * y * x * y * y)
    have e₂ := hrot y (x * y * y * x * y * y)
    have e₃ := hrot y (y * x * y * x * y * y)
    have e₄ := hrot y (y * y * x * y * y * x)
    have e₅ := hrot x (y * y * x * y * x * y)
    have e₆ := hrot y (x * y * y * x * y * x)
    simp only [← mul_assoc, r₁, r₂, r₀', r₁', zero_mul, add_zero, map_add, map_neg,
      map_zero] at e₁ e₂ e₃ e₄ e₅ e₆
    have w₁ : f (x * y * y * x * y * y * x) = 0 := by linear_combination (norm := module) -e₁
    have w₂ : f (y * x * y * y * x * y * y) = 0 := by linear_combination (norm := module) e₂
    have w₃ : f (y * y * x * y * x * y * y) = 0 := by linear_combination (norm := module) e₃
    have w₄ : f (y * y * x * y * y * x * y) = 0 := by linear_combination (norm := module) -e₄
    have w₅ : f (x * y * y * x * y * x * y) = 0 := by
      linear_combination (norm := module) e₅ - w₃ - w₄
    have w₆ : f (y * x * y * y * x * y * x) = 0 := by linear_combination (norm := module) e₆ + w₅
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₅, w₁, w₆, w₂, w₃, w₄⟩
  -- Length 8.
  have l₈ : ∀ b ∈ quinticWords x y 7, f b = 0 := by
    have e₁ := hrot y (y * x * y * y * x * y * y)
    have e₂ := hrot y (x * y * y * x * y * x * y)
    have e₃ := hrot y (y * x * y * y * x * y * x)
    have e₄ := hrot x (y * y * x * y * x * y * y)
    have e₅ := hrot x (x * y * y * x * y * x * y)
    have e₆ := hrot y (x * y * y * x * y * y * x)
    simp only [← mul_assoc, r₁, r₂, r₃, r₀', r₁', zero_mul, add_zero, map_add, map_neg,
      map_zero] at e₁ e₂ e₃ e₄ e₅ e₆
    have w₁ : f (y * y * x * y * y * x * y * y) = 0 := by linear_combination (norm := module) e₁
    have w₂ : f (x * y * y * x * y * x * y * y) = 0 := hdiv u2 <| by
      linear_combination (norm := module) -e₂ - e₃ + e₄
    have w₃ : f (x * y * y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) e₅ - w₂
    have w₄ : f (y * x * y * y * x * y * x * y) = 0 := by
      linear_combination (norm := module) e₂ + w₂
    have w₅ : f (y * x * y * y * x * y * y * x) = 0 := by
      linear_combination (norm := module) e₆ + w₃
    have w₆ : f (y * y * x * y * y * x * y * x) = 0 := by
      linear_combination (norm := module) e₃ + w₄
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₂, w₃, w₄, w₅, w₆, w₁⟩
  -- Length 9.
  have l₉ : ∀ b ∈ quinticWords x y 8, f b = 0 := by
    have e₁ := hrot x (x * y * y * x * y * x * y * y)
    have e₂ := hrot y (x * y * y * x * y * x * y * y)
    have e₃ := hrot y (y * y * x * y * y * x * y * x)
    have e₄ := hrot y (x * y * y * x * y * y * x * y)
    have e₅ := hrot x (y * x * y * y * x * y * x * y)
    have e₆ := hrot y (y * x * y * y * x * y * x * y)
    have e₇ := hrot y (y * x * y * y * x * y * y * x)
    simp only [← mul_assoc, r₁, r₂, r₃, r₀', r₁', r₃', add_mul, neg_mul, zero_mul, add_zero,
      zero_add, map_add, map_neg, map_zero] at e₁ e₂ e₃ e₄ e₅ e₆ e₇
    have w₁ : f (x * y * y * x * y * y * x * y * x) = 0 := by linear_combination (norm := module) e₁
    have w₂ : f (y * x * y * y * x * y * x * y * y) = 0 := by linear_combination (norm := module) e₂
    have w₃ : f (y * y * x * y * y * x * y * x * y) = 0 := by
      linear_combination (norm := module) -e₃
    have w₄ : f (y * x * y * y * x * y * y * x * y) = 0 := hdiv u3 <| by
      linear_combination (norm := module) e₄ + e₅ + e₆
    have w₅ : f (x * y * y * x * y * y * x * y * y) = 0 := by
      linear_combination (norm := module) -e₄ + w₄
    have w₆ : f (y * y * x * y * y * x * y * y * x) = 0 := by
      linear_combination (norm := module) e₇ + w₄
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₅, w₂, w₄, w₃, w₆⟩
  -- Length 10.
  have l₁₀ : ∀ b ∈ quinticWords x y 9, f b = 0 := by
    have e₁ := hrot x (x * y * y * x * y * y * x * y * y)
    have e₂ := hrot y (x * y * y * x * y * y * x * y * y)
    have e₃ := hrot y (y * x * y * y * x * y * x * y * y)
    have e₄ := hrot y (y * y * x * y * y * x * y * y * x)
    have e₅ := hrot x (y * x * y * y * x * y * x * y * y)
    simp only [← mul_assoc, r₁, r₂, r₃, r₀', r₁', r₃', add_mul, neg_mul, zero_mul, neg_zero,
      add_zero, zero_add, map_add, map_neg, map_zero] at e₁ e₂ e₃ e₄ e₅
    have w₁ : f (x * y * y * x * y * y * x * y * y * x) = 0 := by
      linear_combination (norm := module) -e₁
    have w₂ : f (y * x * y * y * x * y * y * x * y * y) = 0 := by
      linear_combination (norm := module) e₂
    have w₃ : f (y * y * x * y * y * x * y * x * y * y) = 0 := by
      linear_combination (norm := module) e₃
    have w₄ : f (y * y * x * y * y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) -e₄
    have w₅ : f (y * x * y * y * x * y * y * x * y * x) = 0 := by
      linear_combination (norm := module) e₅ - w₂ + w₃
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₅, w₂, w₃, w₄⟩
  -- Length 11.
  have l₁₁ : ∀ b ∈ quinticWords x y 10, f b = 0 := by
    have e₁ := hrot y (y * x * y * y * x * y * y * x * y * y)
    have e₂ := hrot y (x * y * y * x * y * y * x * y * y * x)
    have e₃ := hrot x (y * y * x * y * y * x * y * x * y * y)
    have e₄ := hrot x (y * x * y * y * x * y * y * x * y * y)
    simp only [← mul_assoc, r₁, r₃, r₄, r₁', r₃', r₄', add_mul, neg_mul, zero_mul, add_zero,
      map_add, map_neg, map_zero] at e₁ e₂ e₃ e₄
    have w₁ : f (y * y * x * y * y * x * y * y * x * y * y) = 0 := by
      linear_combination (norm := module) e₁
    have w₂ : f (y * y * x * y * y * x * y * y * x * y * x) = 0 := hdiv u2 <| by
      linear_combination (norm := module) -e₂ + e₃
    have w₃ : f (x * y * y * x * y * y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) -e₄ + w₂
    have w₄ : f (y * x * y * y * x * y * y * x * y * y * x) = 0 := by
      linear_combination (norm := module) e₂ + w₃
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₃, w₄, w₂, w₁⟩
  -- Length 12.
  have l₁₂ : ∀ b ∈ quinticWords x y 11, f b = 0 := by
    have e₁ := hrot x (x * y * y * x * y * y * x * y * y * x * y)
    have e₂ := hrot y (x * y * y * x * y * y * x * y * y * x * y)
    have e₃ := hrot y (y * x * y * y * x * y * y * x * y * y * x)
    simp only [← mul_assoc, r₀', r₅', zero_mul, map_sub, map_zero] at e₁ e₂ e₃
    have w₁ : f (x * y * y * x * y * y * x * y * y * x * y * x) = 0 := by
      linear_combination (norm := module) -e₁
    have w₂ : f (y * y * x * y * y * x * y * y * x * y * y * x) = 0 := by
      linear_combination (norm := module) e₂
    have w₃ : f (y * x * y * y * x * y * y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) -e₃ + w₂
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₃, w₂⟩
  -- Length 13.
  have l₁₃ : ∀ b ∈ quinticWords x y 12, f b = 0 := by
    have e₁ := hrot x (y * y * x * y * y * x * y * y * x * y * y * x)
    have e₂ := hrot y (y * y * x * y * y * x * y * y * x * y * y * x)
    simp only [← mul_assoc, r₀, r₁', r₅', sub_mul, zero_mul, sub_zero, map_zero] at e₁ e₂
    have w₁ : f (y * x * y * y * x * y * y * x * y * y * x * y * x) = 0 := by
      linear_combination (norm := module) e₁
    have w₂ : f (y * y * x * y * y * x * y * y * x * y * y * x * y) = 0 := by
      linear_combination (norm := module) -e₂
    simp only [quinticWords, Set.forall_mem_insert, Set.forall_mem_singleton]
    exact ⟨w₁, w₂⟩
  -- Length 14.
  have l₁₄ : ∀ b ∈ quinticWords x y 13, f b = 0 := by
    have e₁ := hrot y (y * x * y * y * x * y * y * x * y * y * x * y * x)
    simp only [← mul_assoc, r₁, r₄, r₅, r₁', zero_mul, add_zero, sub_zero, map_neg] at e₁
    have w₁ : f (y * y * x * y * y * x * y * y * x * y * y * x * y * x) = 0 := hdiv u2 <| by
      linear_combination (norm := module) e₁
    simp only [quinticWords, Set.forall_mem_singleton]
    exact w₁
  -- Every reduced word of positive length lies in `[B, B]`.
  have hwords : ∀ b ∈ quinticWords x y t, b ∈ C := by
    intro b hb
    refine hD.1 ((QuotientAddGroup.eq_zero_iff b).1 ?_)
    rcases Nat.lt_or_ge t 14 with ht | ht
    · interval_cases t
      exacts [l₁ b hb, l₂ b hb, l₃ b hb, l₄ b hb, l₅ b hb, l₆ b hb, l₇ b hb, l₈ b hb, l₉ b hb,
        l₁₀ b hb, l₁₁ b hb, l₁₂ b hb, l₁₃ b hb, l₁₄ b hb]
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 14 := ⟨t - 14, by omega⟩
      simp [quinticWords] at hb
  have hle := span_pair_pow_succ_le_span_quinticWords hx hy hxy t hw
  clear hw
  induction hle using Submodule.span_induction with
  | mem b hb => exact hwords b hb
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul n a _ ha => exact hD.1 (D.zsmul_mem (hD.2 ha) n)

end TauCeti
