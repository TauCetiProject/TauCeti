/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A square-zero and a cube-zero element with a cube-zero sum

Let `x` and `y` be elements of an `R`-algebra with `x ^ 2 = 0`, `y ^ 3 = 0` and
`(x + y) ^ 3 = 0`. Then **every product of six factors from `{x, y}` vanishes**, so the sixth
power of the span of `{x, y}` is zero.

The products of factors from `{x, y}` which survive the relations `x ^ 2 = 0` and `y ^ 3 = 0`
are the words with no factor `x x` and no factor `y y y`. Expanding `(x + y) ^ 3` leaves the
four such words of length three, so

```text
y y x = -(y x y + x y y + x y x).
```

Multiplying this relation by `x` on the left and on the right and comparing gives
`y x y x = x y x y`. These four rewriting rules `x x ↦ 0`, `y y y ↦ 0`,
`y y x ↦ -(y x y + x y y + x y x)` and `y x y x ↦ x y x y` lower words in the degree-lexicographic
order with `x < y`, and every word of length six is rewritten to zero by them.

This is the relation satisfied at the branch node of the `E₆` diagram by the backtracks into its
arms of lengths one and two, in the preprojective algebra of `E₆`: the backtrack into the third
arm, of length two, is `-(x + y)`.

## Main results

* `TauCeti.span_pair_pow_six_eq_bot`: if `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = 0`, then the
  sixth power of the span of `{x, y}` is zero.
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
  rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, pow_succ', pow_succ', pow_succ',
    pow_succ', pow_succ', pow_succ', pow_zero, mul_one] at hw
  simp only [Set.mem_mul] at hw
  obtain ⟨a₀, ha₀, _, ⟨a₁, ha₁, _, ⟨a₂, ha₂, _, ⟨a₃, ha₃, _, ⟨a₄, ha₄, a₅, ha₅, rfl⟩, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩ := hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha₀ ha₁ ha₂ ha₃ ha₄ ha₅
  rcases ha₀ with rfl | rfl <;> rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;>
    rcases ha₃ with rfl | rfl <;> rcases ha₄ with rfl | rfl <;> rcases ha₅ with rfl | rfl <;>
    simp only [hxx, hyyy, r₁, r₃, r₄, hT, hR, mul_add, mul_neg, mul_zero, neg_zero, add_zero,
      neg_add_rev, neg_neg, zero_add]

end TauCeti
