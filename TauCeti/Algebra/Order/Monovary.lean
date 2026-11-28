/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Order.Monotone.Monovary

/-!
# Rearrangement inequalities for ordered semirings

Similarly ordered functions satisfy the binary rearrangement inequality on any set.
Oppositely ordered functions satisfy its reverse. These subtraction-free forms extend
Mathlib's ordered-ring statements to ordered semirings and supply the pairwise comparisons
used in weighted Chebyshev inequalities.

## Main results

* `TauCeti.MonovaryOn.mul_add_mul_le_mul_add_mul`: the cross sum is bounded by the diagonal sum.
* `TauCeti.AntivaryOn.mul_add_mul_le_mul_add_mul`: the diagonal sum is bounded by the cross sum.
-/

public section

namespace TauCeti

variable {ι R : Type*} [Semiring R] [LinearOrder R] [ExistsAddOfLE R]
  [MulPosMono R] [AddLeftMono R]

/-- Binary rearrangement for similarly ordered functions on a set, over an ordered semiring. -/
theorem MonovaryOn.mul_add_mul_le_mul_add_mul {s : Set ι} {a b : ι → R}
    (hab : MonovaryOn a b s) ⦃i : ι⦄ (hi : i ∈ s) ⦃j : ι⦄ (hj : j ∈ s) :
    a i * b j + a j * b i ≤ a i * b i + a j * b j := by
  have hpair ⦃i j : ι⦄ (hi : i ∈ s) (hj : j ∈ s) (hb : b i ≤ b j) :
      a i * b j + a j * b i ≤ a i * b i + a j * b j := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hb]
    have ha := hab hi hj hb
    obtain ⟨c, hc⟩ := exists_add_of_le hb.le
    have hc0 : 0 ≤ c := by
      by_contra hn
      have hle := add_le_add (le_refl (b i)) (le_of_not_ge hn)
      rw [← hc, add_zero] at hle
      exact hb.not_ge hle
    have h := add_le_add (le_refl (a i * b i + a j * b i))
      (mul_le_mul_of_nonneg_right ha hc0)
    simpa only [hc, mul_add, add_assoc, add_left_comm, add_comm] using h
  rcases le_total (b i) (b j) with h | h
  · exact hpair hi hj h
  · simpa only [add_comm] using hpair hj hi h

/-- Binary rearrangement for oppositely ordered functions on a set, over an ordered semiring. -/
theorem AntivaryOn.mul_add_mul_le_mul_add_mul {s : Set ι} {a b : ι → R}
    (hab : AntivaryOn a b s) ⦃i : ι⦄ (hi : i ∈ s) ⦃j : ι⦄ (hj : j ∈ s) :
    a i * b i + a j * b j ≤ a i * b j + a j * b i := by
  have hpair ⦃i j : ι⦄ (hi : i ∈ s) (hj : j ∈ s) (hb : b i ≤ b j) :
      a i * b i + a j * b j ≤ a i * b j + a j * b i := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hb]
    have ha := hab hi hj hb
    obtain ⟨c, hc⟩ := exists_add_of_le hb.le
    have hc0 : 0 ≤ c := by
      by_contra hn
      have hle := add_le_add (le_refl (b i)) (le_of_not_ge hn)
      rw [← hc, add_zero] at hle
      exact hb.not_ge hle
    have h := add_le_add (le_refl (a i * b i + a j * b i))
      (mul_le_mul_of_nonneg_right ha hc0)
    simpa only [hc, mul_add, add_assoc, add_left_comm, add_comm] using h
  rcases le_total (b i) (b j) with h | h
  · exact hpair hi hj h
  · simpa only [add_comm] using hpair hj hi h

end TauCeti
