/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
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

The same argument one dimension up, with three applications of the Cauchy–Schwarz inequality,
bounds the eighth power of `∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, G x y z * u x y * v x z * w y z`, for
weights `u`, `v` and `w` of absolute value at most one, by `(#s * #t * #r) ^ 6` times the
octahedral sum
`∑ y ∈ t, ∑ y' ∈ t, ∑ z ∈ r, ∑ z' ∈ r, (∑ x ∈ s, G x y z * G x y z' * G x y' z * G x y' z') ^ 2`,
the unnormalized eighth power of the octahedral norm of `G`. The weights may be the indicators
of three arbitrary relations, so a small octahedral norm forces a small discrepancy on every set
of triples cut out by three pair relations.

## Main results

* `Finset.sum_sum_pow_four_le`: the fourth power of a rectangle sum is at most
  `(#s * #t) ^ 2` times the box sum.
* `Finset.sq_sum_sum_mul_le`: Cauchy–Schwarz on a double sum with weights of square at most one.
* `Finset.sum_sum_sum_mul_pow_eight_le`: the eighth power of a weighted box sum of three
  variables is at most `(#s * #t * #r) ^ 6` times the octahedral sum.

## References

* F. R. K. Chung, R. L. Graham and R. M. Wilson, *Quasi-random graphs*, Combinatorica 9 (1989).
* W. T. Gowers, *Quasirandomness, counting and regularity for 3-uniform hypergraphs*,
  Combin. Probab. Comput. 15 (2006), the octahedral norm.
-/

public section

namespace Finset

variable {α β γ R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

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

/-- **Cauchy–Schwarz with bounded weights.** For weights `a` of square at most one on `s ×ˢ t`,
the square of `∑ x ∈ s, ∑ y ∈ t, a x y * g x y` is at most `#s * #t` times the sum of the
squares of `g`. -/
theorem sq_sum_sum_mul_le {s : Finset α} {t : Finset β} (a g : α → β → R)
    (ha : ∀ x ∈ s, ∀ y ∈ t, a x y ^ 2 ≤ 1) :
    (∑ x ∈ s, ∑ y ∈ t, a x y * g x y) ^ 2 ≤ #s * #t * ∑ x ∈ s, ∑ y ∈ t, g x y ^ 2 := by
  rw [← sum_product' (f := fun x y ↦ a x y * g x y), ← sum_product' (f := fun x y ↦ g x y ^ 2)]
  calc _ ≤ (∑ p ∈ s ×ˢ t, a p.1 p.2 ^ 2) * ∑ p ∈ s ×ˢ t, g p.1 p.2 ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ _p ∈ s ×ˢ t, (1 : R)) * ∑ p ∈ s ×ˢ t, g p.1 p.2 ^ 2 := by
        gcongr with p hp
        exact ha _ (mem_product.1 hp).1 _ (mem_product.1 hp).2
    _ = _ := by simp [card_product]

private theorem sq_mul_le_one {a b : R} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : (a * b) ^ 2 ≤ 1 := by
  rw [sq_le_one_iff_abs_le_one, abs_mul]
  calc |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- First step of `Finset.sum_sum_sum_mul_pow_eight_le`: Cauchy–Schwarz in `(x, y)` removes
the weight `u`. -/
private theorem sq_sum_sum_sum_mul_le {s : Finset α} {t : Finset β} {r : Finset γ}
    (G : α → β → γ → R) {u : α → β → R} (v : α → γ → R) (w : β → γ → R)
    (hu : ∀ x ∈ s, ∀ y ∈ t, |u x y| ≤ 1) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, G x y z * u x y * v x z * w y z) ^ 2 ≤
      #s * #t * ∑ x ∈ s, ∑ y ∈ t, (∑ z ∈ r, G x y z * v x z * w y z) ^ 2 := by
  calc _ = (∑ x ∈ s, ∑ y ∈ t, u x y * ∑ z ∈ r, G x y z * v x z * w y z) ^ 2 := by
        simp_rw [mul_sum]
        congr 1
        refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
        ring
    _ ≤ _ := sq_sum_sum_mul_le _ _ fun x hx y hy ↦ sq_le_one_iff_abs_le_one _ |>.2 (hu x hx y hy)

/-- Second step of `Finset.sum_sum_sum_mul_pow_eight_le`: Cauchy–Schwarz in `(x, (z, z'))`
removes the weight `v`. -/
private theorem sq_sum_sum_sq_le {s : Finset α} {t : Finset β} {r : Finset γ}
    (G : α → β → γ → R) {v : α → γ → R} (w : β → γ → R) (hv : ∀ x ∈ s, ∀ z ∈ r, |v x z| ≤ 1) :
    (∑ x ∈ s, ∑ y ∈ t, (∑ z ∈ r, G x y z * v x z * w y z) ^ 2) ^ 2 ≤
      #s * #(r ×ˢ r) * ∑ x ∈ s, ∑ p ∈ r ×ˢ r,
        (∑ y ∈ t, w y p.1 * w y p.2 * (G x y p.1 * G x y p.2)) ^ 2 := by
  calc _ = (∑ x ∈ s, ∑ p ∈ r ×ˢ r, v x p.1 * v x p.2 *
        ∑ y ∈ t, w y p.1 * w y p.2 * (G x y p.1 * G x y p.2)) ^ 2 := by
        congr 1
        refine sum_congr rfl fun x _ ↦ ?_
        simp_rw [sq, sum_mul_sum, mul_sum]
        rw [sum_product, sum_comm]
        refine sum_congr rfl fun z _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun z' _ ↦ sum_congr rfl fun y _ ↦ ?_
        ring
    _ ≤ _ := sq_sum_sum_mul_le _ _ fun x hx p hp ↦
        sq_mul_le_one (hv x hx _ (mem_product.1 hp).1) (hv x hx _ (mem_product.1 hp).2)

/-- Third step of `Finset.sum_sum_sum_mul_pow_eight_le`: Cauchy–Schwarz in
`((y, y'), (z, z'))` removes the weight `w`. -/
private theorem sq_sum_sum_sq_le_octahedral {s : Finset α} {t : Finset β} {r : Finset γ}
    (G : α → β → γ → R) {w : β → γ → R} (hw : ∀ y ∈ t, ∀ z ∈ r, |w y z| ≤ 1) :
    (∑ x ∈ s, ∑ p ∈ r ×ˢ r, (∑ y ∈ t, w y p.1 * w y p.2 * (G x y p.1 * G x y p.2)) ^ 2) ^ 2 ≤
      #(t ×ˢ t) * #(r ×ˢ r) * ∑ y ∈ t, ∑ y' ∈ t, ∑ z ∈ r, ∑ z' ∈ r,
        (∑ x ∈ s, G x y z * G x y z' * G x y' z * G x y' z') ^ 2 := by
  calc _ = (∑ q ∈ t ×ˢ t, ∑ p ∈ r ×ˢ r, w q.1 p.1 * w q.1 p.2 * (w q.2 p.1 * w q.2 p.2) *
        ∑ x ∈ s, G x q.1 p.1 * G x q.1 p.2 * G x q.2 p.1 * G x q.2 p.2) ^ 2 := by
        congr 1
        simp_rw [sq, sum_mul_sum, mul_sum]
        rw [sum_product]
        -- Bring both sides to the summation order `p, y, y', x`: the left side from
        -- `x, p, y, y'` via `p, x, y, y'` and `p, y, x, y'`, the right side from `y, y', p, x`
        -- via `y, p, y', x`.
        conv_lhs => rw [sum_comm]; enter [2, p]; rw [sum_comm]; enter [2, y]; rw [sum_comm]
        conv_rhs => enter [2, y]; rw [sum_comm]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun p _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun y' _ ↦
          sum_congr rfl fun x _ ↦ ?_
        ring
    _ ≤ #(t ×ˢ t) * #(r ×ˢ r) * ∑ q ∈ t ×ˢ t, ∑ p ∈ r ×ˢ r,
        (∑ x ∈ s, G x q.1 p.1 * G x q.1 p.2 * G x q.2 p.1 * G x q.2 p.2) ^ 2 := by
        refine sq_sum_sum_mul_le _ _ fun q hq p hp ↦ ?_
        rw [mem_product] at hq hp
        rw [mul_pow]
        calc _ ≤ (1 : R) * 1 := mul_le_mul (sq_mul_le_one (hw _ hq.1 _ hp.1) (hw _ hq.1 _ hp.2))
              (sq_mul_le_one (hw _ hq.2 _ hp.1) (hw _ hq.2 _ hp.2)) (sq_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = _ := by
        rw [sum_product]
        exact congrArg _ (sum_congr rfl fun y _ ↦ sum_congr rfl fun y' _ ↦ sum_product ..)

/-- **Box sums are controlled by the octahedral norm.** For weights `u`, `v` and `w` of absolute
value at most one on the three coordinate pairs, the eighth power of the weighted box sum
`∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, G x y z * u x y * v x z * w y z` is at most `(#s * #t * #r) ^ 6`
times the octahedral sum of `G`, a weighted count of the octahedra
`{x, x'} × {y, y'} × {z, z'}`. -/
theorem sum_sum_sum_mul_pow_eight_le {s : Finset α} {t : Finset β} {r : Finset γ}
    (G : α → β → γ → R) {u : α → β → R} {v : α → γ → R} {w : β → γ → R}
    (hu : ∀ x ∈ s, ∀ y ∈ t, |u x y| ≤ 1) (hv : ∀ x ∈ s, ∀ z ∈ r, |v x z| ≤ 1)
    (hw : ∀ y ∈ t, ∀ z ∈ r, |w y z| ≤ 1) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, G x y z * u x y * v x z * w y z) ^ 8 ≤
      (#s * #t * #r) ^ 6 * ∑ y ∈ t, ∑ y' ∈ t, ∑ z ∈ r, ∑ z' ∈ r,
        (∑ x ∈ s, G x y z * G x y z' * G x y' z * G x y' z') ^ 2 := by
  set X := ∑ x ∈ s, ∑ y ∈ t, (∑ z ∈ r, G x y z * v x z * w y z) ^ 2
  set Y := ∑ x ∈ s, ∑ p ∈ r ×ˢ r, (∑ y ∈ t, w y p.1 * w y p.2 * (G x y p.1 * G x y p.2)) ^ 2
  have h₁ : _ ≤ #s * #t * X := sq_sum_sum_sum_mul_le G v w hu
  have h₂ : X ^ 2 ≤ #s * #(r ×ˢ r) * Y := sq_sum_sum_sq_le G w hv
  have h₃ := sq_sum_sum_sq_le_octahedral (s := s) G hw
  have hX₀ : 0 ≤ X := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  have hY₀ : 0 ≤ Y := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only [card_product, Nat.cast_mul] at h₂ h₃
  calc _ = ((∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, G x y z * u x y * v x z * w y z) ^ 2) ^ 4 := by ring
    _ ≤ (#s * #t * X) ^ 4 := pow_le_pow_left₀ (sq_nonneg _) h₁ 4
    _ = (#s * #t) ^ 4 * (X ^ 2) ^ 2 := by ring
    _ ≤ (#s * #t) ^ 4 * (#s * (#r * #r) * Y) ^ 2 := by gcongr
    _ = (#s * #t) ^ 4 * (#s * (#r * #r)) ^ 2 * Y ^ 2 := by ring
    _ ≤ (#s * #t) ^ 4 * (#s * (#r * #r)) ^ 2 * (#t * #t * (#r * #r) *
        ∑ y ∈ t, ∑ y' ∈ t, ∑ z ∈ r, ∑ z' ∈ r,
          (∑ x ∈ s, G x y z * G x y z' * G x y' z * G x y' z') ^ 2) := by gcongr
    _ = _ := by ring

end Finset
