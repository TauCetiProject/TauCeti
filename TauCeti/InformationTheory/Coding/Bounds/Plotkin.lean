/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.InformationTheory.Hamming

/-!
# The Plotkin bound

Let `C` be a code of length `n` over an alphabet of `q` letters whose distinct words are at
Hamming distance at least `d`. If `(q - 1) n < q d`, then `|C| ≤ q d / (q d - (q - 1) n)`.

The proof sums the distance over the ordered pairs of words of `C`: the total `T` is at least
`|C| (|C| - 1) d`, because each pair of distinct words contributes at least `d`. In a coordinate
where the letter `a` occurs `m_a` times, the pairs that agree number `∑_a m_a²`, and
`|C|² ≤ q ∑_a m_a²` by the Cauchy–Schwarz inequality. With the counting identity
`Finset.sum_sum_hammingDist_add_sum_sum_sq`, summed over the `n` coordinates this gives
`q T ≤ (q - 1) n |C|²`.

## Main results

* `Finset.card_le_plotkin`: **the Plotkin bound**.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, Theorem 4.4.1, part 2, and
  Exercise 4.17.
-/

public section

namespace Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

/-- **The Plotkin bound.** If the distinct words of a code `C` of length `n` over an alphabet of
`q` letters are at Hamming distance at least `d`, and `(q - 1) n < q d`, then
`|C| ≤ q d / (q d - (q - 1) n)`. -/
theorem card_le_plotkin (C : Finset (ι → α)) {d : ℕ}
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y)
    (h : ((Fintype.card α : ℝ) - 1) * Fintype.card ι < Fintype.card α * d) :
    (#C : ℝ) ≤
      Fintype.card α * d / (Fintype.card α * d - (Fintype.card α - 1) * Fintype.card ι) := by
  set q : ℝ := (Fintype.card α : ℝ)
  set n : ℝ := (Fintype.card ι : ℝ)
  set c : ℝ := (#C : ℝ)
  have hq : 0 ≤ q := Nat.cast_nonneg _
  -- The total distance `T` satisfies `c (c - 1) d ≤ T` and `q T ≤ (q - 1) n c²`.
  set T : ℕ := ∑ x ∈ C, ∑ y ∈ C, hammingDist x y with hT
  have hlow : c * (c - 1) * d ≤ T := by
    have hrow (x) (hx : x ∈ C) : (#C - 1) * d ≤ ∑ y ∈ C, hammingDist x y :=
      calc (#C - 1) * d = #(C.erase x) • d := by rw [card_erase_of_mem hx, smul_eq_mul]
        _ ≤ ∑ y ∈ C.erase x, hammingDist x y := card_nsmul_le_sum _ _ _ fun y hy ↦
          hd x hx y (mem_of_mem_erase hy) (ne_of_mem_erase hy).symm
        _ = ∑ y ∈ C, hammingDist x y := sum_erase C (hammingDist_self x)
    have hT := card_nsmul_le_sum C _ _ hrow
    rw [smul_eq_mul] at hT
    rcases C.eq_empty_or_nonempty with hC | hC
    · simp [c, hC]
    · have h1 : 1 ≤ #C := hC.card_pos
      calc c * (c - 1) * d = ((#C * ((#C - 1) * d) : ℕ) : ℝ) := by
            push_cast [Nat.cast_sub h1]
            ring
        _ ≤ T := by exact_mod_cast hT
  have hcs (i : ι) : c ^ 2 ≤ q * ∑ a, (#{x ∈ C | x i = a} : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α))
      (f := fun a ↦ (#{x ∈ C | x i = a} : ℝ))
    rwa [card_univ, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _] at this
  have hsum := sum_sum_hammingDist_add_sum_sum_sq C fun _ _ _ ↦ mem_univ _
  rw [← hT] at hsum
  have hsum' : (T : ℝ) + ∑ i, ∑ a, (#{x ∈ C | x i = a} : ℝ) ^ 2 = n * c ^ 2 := by
    simp only [n, c]
    exact_mod_cast hsum
  have hup : q * T ≤ (q - 1) * n * c ^ 2 := by
    have := sum_le_sum fun i (_ : i ∈ univ) ↦ hcs i
    rw [sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at this
    nlinarith
  have hden : 0 < q * d - (q - 1) * n := by linarith
  rw [le_div_iff₀ hden]
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  rcases hc0.eq_or_lt with hc | hc
  · rw [← hc, zero_mul]
    exact mul_nonneg hq (Nat.cast_nonneg _)
  · nlinarith [mul_le_mul_of_nonneg_left hlow hq]

end Finset
