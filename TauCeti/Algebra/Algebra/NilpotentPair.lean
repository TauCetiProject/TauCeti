/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
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

## Main results

* `TauCeti.span_pair_pow_six_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, then the
  sixth power of the span of `{x, y}` is zero.
* `TauCeti.span_pair_pow_fifteen_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 5 = 0`, then
  the fifteenth power of the span of `{x, y}` is zero.
-/

public section

namespace TauCeti

open Submodule
open scoped Pointwise

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {x y : A}

/-- **A square-zero and a cube-zero element with a cube-zero sum.** If `x ^ 2 = 0`, `y ^ 3 = 0`
and `(x + y) ^ 3 = 0`, then every product of six factors from `{x, y}` vanishes. -/
theorem span_pair_pow_six_eq_bot (hx : x ^ 2 = 0) (hy : y ^ 3 = 0) (hxy : (x + y) ^ 3 = 0) :
    span R {x, y} ^ 6 = ⊥ := by
  -- The rewriting rules, applied at the left end of a right-associated word `a`.
  have hxx : x * x = 0 := by rw [← sq, hx]
  have hyyy : y * (y * y) = 0 := by rw [← pow_three, hy]
  have r₁ (a : A) : x * (x * a) = 0 := by rw [← mul_assoc, hxx, zero_mul]
  -- Expanding `(x + y) ^ 3` leaves the four words with no `x x` and no `y y y`.
  have hT : y * (y * x) = -(y * (x * y) + x * (y * y) + x * (y * x)) := by
    have h : (x + y) ^ 3 = x * (x * x) + x * (x * y) + y * (x * x) + y * (y * y) +
        (y * (y * x) + (y * (x * y) + x * (y * y) + x * (y * x))) := by noncomm_ring
    simp only [hxy, r₁, hxx, hyyy, mul_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have r₃ (a : A) :
      y * (y * (x * a)) = -(y * (x * (y * a)) + x * (y * (y * a)) + x * (y * (x * a))) := by
    simp only [← mul_assoc] at hT ⊢
    rw [hT]
    noncomm_ring
  -- Multiplying the cubic relation by `x` on either side gives `y x y x = x y x y`.
  have hR : y * (x * (y * x)) = x * (y * (x * y)) := by
    have hl : x * (y * (y * x)) = -(x * (y * (x * y))) := by
      simp only [hT, mul_neg, mul_add, r₁, add_zero]
    have hr := r₃ x
    simp only [hxx, mul_zero, hl, add_zero] at hr
    rw [eq_comm, neg_eq_zero, ← sub_eq_add_neg] at hr
    exact eq_of_sub_eq_zero hr
  have r₄ (a : A) : y * (x * (y * (x * a))) = x * (y * (x * (y * a))) := by
    simp only [← mul_assoc] at hR ⊢
    rw [hR]
  rw [span_pow, span_eq_bot]
  intro w hw
  rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_succ', pow_succ', pow_zero, mul_one] at hw
  simp only [Set.mem_mul] at hw
  obtain ⟨a₀, ha₀, _, ⟨a₁, ha₁, _, ⟨a₂, ha₂, _, ⟨a₃, ha₃, _, ⟨a₄, ha₄, a₅, ha₅, rfl⟩, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩ := hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha₀ ha₁ ha₂ ha₃ ha₄ ha₅
  rcases ha₀ with rfl | rfl <;> rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;>
    rcases ha₃ with rfl | rfl <;> rcases ha₄ with rfl | rfl <;> rcases ha₅ with rfl | rfl <;>
    simp only [hxx, hyyy, r₁, r₃, r₄, hT, hR, mul_add, mul_neg, mul_zero, neg_zero, add_zero,
      neg_add_rev, neg_neg, zero_add]

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
