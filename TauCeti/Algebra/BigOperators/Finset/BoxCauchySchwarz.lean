/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Rectangle sums are controlled by the box norm

For a function `g` of two variables and finite sets `s' ⊆ s` and `t' ⊆ t`, two applications of
the Cauchy–Schwarz inequality bound the fourth power of the rectangle sum
`∑ x ∈ s', ∑ y ∈ t', g x y` by `(#s * #t) ^ 2` times
`∑ y ∈ t, ∑ y' ∈ t, (∑ x ∈ s, g x y * g x y') ^ 2`. The last sum is the unnormalized fourth power
of the box norm of `g` on `s ×ˢ t`, a weighted count of the rectangles `{x, x'} × {y, y'}`. The
bound is uniform in the test sets `s'` and `t'`, so a small box norm forces a small discrepancy
on every rectangle. This is the step by which few four-cycles force quasirandomness.

## Main results

* `Finset.sum_sum_pow_four_le`: the fourth power of a rectangle sum is at most
  `(#s * #t) ^ 2` times the box sum.

## References

* F. R. K. Chung, R. L. Graham and R. M. Wilson, *Quasi-random graphs*, Combinatorica 9 (1989).
-/

public section

namespace Finset

variable {α β R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Rectangle sums are controlled by the box norm.** For `s' ⊆ s` and `t' ⊆ t`, the fourth
power of `∑ x ∈ s', ∑ y ∈ t', g x y` is at most `(#s * #t) ^ 2` times the box sum
`∑ y ∈ t, ∑ y' ∈ t, (∑ x ∈ s, g x y * g x y') ^ 2`. -/
theorem sum_sum_pow_four_le {s s' : Finset α} {t t' : Finset β} (hs : s' ⊆ s) (ht : t' ⊆ t)
    (g : α → β → R) :
    (∑ x ∈ s', ∑ y ∈ t', g x y) ^ 4 ≤
      (#s * #t) ^ 2 * ∑ y ∈ t, ∑ y' ∈ t, (∑ x ∈ s, g x y * g x y') ^ 2 := by
  -- Cauchy–Schwarz in the first variable.
  have h₁ : (∑ x ∈ s', ∑ y ∈ t', g x y) ^ 2 ≤
      #s * ∑ y ∈ t', ∑ y' ∈ t', ∑ x ∈ s, g x y * g x y' := by
    calc (∑ x ∈ s', ∑ y ∈ t', g x y) ^ 2 ≤ #s' * ∑ x ∈ s', (∑ y ∈ t', g x y) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ #s * ∑ x ∈ s, (∑ y ∈ t', g x y) ^ 2 := by
          gcongr
      _ = #s * ∑ y ∈ t', ∑ y' ∈ t', ∑ x ∈ s, g x y * g x y' := by
          simp_rw [sq, sum_mul_sum]
          rw [sum_comm]
          exact congrArg _ (sum_congr rfl fun _ _ ↦ sum_comm)
  -- Cauchy–Schwarz in the pair of second variables.
  have h₂ : (∑ y ∈ t', ∑ y' ∈ t', ∑ x ∈ s, g x y * g x y') ^ 2 ≤
      #t ^ 2 * ∑ y ∈ t, ∑ y' ∈ t, (∑ x ∈ s, g x y * g x y') ^ 2 := by
    rw [← sum_product' (f := fun y y' ↦ ∑ x ∈ s, g x y * g x y'),
      ← sum_product' (f := fun y y' ↦ (∑ x ∈ s, g x y * g x y') ^ 2)]
    calc _ ≤ #(t' ×ˢ t') * ∑ p ∈ t' ×ˢ t', (∑ x ∈ s, g x p.1 * g x p.2) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ _ := by
          have hcard : (#(t' ×ˢ t') : R) ≤ #t ^ 2 := by
            rw [card_product, Nat.cast_mul, sq]
            gcongr
          gcongr
  calc (∑ x ∈ s', ∑ y ∈ t', g x y) ^ 4 = ((∑ x ∈ s', ∑ y ∈ t', g x y) ^ 2) ^ 2 := by ring
    _ ≤ (#s * ∑ y ∈ t', ∑ y' ∈ t', ∑ x ∈ s, g x y * g x y') ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = #s ^ 2 * (∑ y ∈ t', ∑ y' ∈ t', ∑ x ∈ s, g x y * g x y') ^ 2 := mul_pow _ _ _
    _ ≤ #s ^ 2 * (#t ^ 2 * ∑ y ∈ t, ∑ y' ∈ t, (∑ x ∈ s, g x y * g x y') ^ 2) := by gcongr
    _ = _ := by ring

end Finset
