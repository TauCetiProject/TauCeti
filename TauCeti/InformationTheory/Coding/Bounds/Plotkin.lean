/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Plotkin bound

Let `C` be a code of length `n` over an alphabet of `q` letters whose distinct words are at
Hamming distance at least `d`. If `(q - 1) n < q d`, then `|C| ≤ q d / (q d - (q - 1) n)`.

The proof sums the distance over the ordered pairs of words of `C`. Each pair of distinct words
contributes at least `d`. In a coordinate where the letter `a` occurs `m_a` times, the pairs
that agree number `∑_a m_a²`, which is at least `|C|² / q` by the Cauchy–Schwarz inequality,
so the pairs that differ there number at most `(1 - 1/q) |C|²`.

## Main results

* `TauCeti.sum_sum_hammingDist_add_sum_sum_sq`: `∑_{x, y ∈ C} d(x, y) + ∑_i ∑_a m_{i,a}² = n |C|²`.
* `TauCeti.card_le_plotkin`: **the Plotkin bound**.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, Theorem 4.4.1, part 2, and
  Exercise 4.17.
-/

public section

open Finset

namespace TauCeti

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

omit [Fintype ι] in
/-- In the coordinate `i`, the ordered pairs of words of `C` that agree there number
`∑_a m_a²`, where `m_a` is the number of words with letter `a` at `i`. -/
private theorem sum_sum_ite_eq_sum_sq (C : Finset (ι → α)) (i : ι) :
    ∑ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) = ∑ a, #{x ∈ C | x i = a} ^ 2 := by
  rw [← sum_fiberwise C (fun x ↦ x i)]
  refine sum_congr rfl fun a _ ↦ ?_
  have hx : ∀ x ∈ {x ∈ C | x i = a},
      ∑ y ∈ C, (if x i = y i then 1 else 0) = #{x ∈ C | x i = a} := by
    intro x hx
    rw [(mem_filter.1 hx).2, sum_boole, Nat.cast_id]
    exact congr_arg card (filter_congr fun _ _ ↦ eq_comm)
  rw [sum_congr rfl hx, sum_const, smul_eq_mul, sq]

/-- The sum of the distances over the ordered pairs of words of `C`, plus the number of pairs
that agree in each coordinate, summed over the coordinates, is `n |C|²`. -/
theorem sum_sum_hammingDist_add_sum_sum_sq (C : Finset (ι → α)) :
    ∑ x ∈ C, ∑ y ∈ C, hammingDist x y + ∑ i, ∑ a, #{x ∈ C | x i = a} ^ 2 =
      Fintype.card ι * #C ^ 2 := by
  have hpair (x y : ι → α) :
      hammingDist x y + ∑ i, (if x i = y i then 1 else 0) = Fintype.card ι := by
    rw [sum_boole, Nat.cast_id, hammingDist, add_comm, ← card_univ]
    exact card_filter_add_card_filter_not _
  have hswap : ∑ i, ∑ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) =
      ∑ x ∈ C, ∑ y ∈ C, ∑ i, (if x i = y i then 1 else 0 : ℕ) :=
    sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm)
  simp_rw [← sum_sum_ite_eq_sum_sq C]
  rw [hswap, ← sum_add_distrib]
  simp_rw [← sum_add_distrib, hpair, sum_const, smul_eq_mul]
  ring

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
  -- The total distance `T` is at least `c (c - 1) d` and at most `(1 - 1/q) n c²`.
  set T : ℕ := ∑ x ∈ C, ∑ y ∈ C, hammingDist x y with hT
  have hlow : c * (c - 1) * d ≤ T := by
    have : ∀ x ∈ C, (#C - 1) * d ≤ ∑ y ∈ C, hammingDist x y := by
      intro x hx
      rw [← add_sum_erase _ _ hx, hammingDist_self, zero_add, ← card_erase_of_mem hx,
        ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun y hy ↦ hd x hx y (mem_of_mem_erase hy) (ne_of_mem_erase hy).symm
    have hT := sum_le_sum this
    rw [sum_const, smul_eq_mul] at hT
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
  have hsum := sum_sum_hammingDist_add_sum_sum_sq C
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
  rcases eq_or_lt_of_le (Nat.cast_nonneg (#C) : (0 : ℝ) ≤ c) with hc | hc
  · rw [show c = 0 from hc.symm, zero_mul]
    exact mul_nonneg hq (Nat.cast_nonneg _)
  · nlinarith [mul_le_mul_of_nonneg_left hlow hq]

end TauCeti
