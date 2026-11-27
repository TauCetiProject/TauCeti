/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# The smooth-number counting function

For real numbers `x` and `y`, the smooth-number counting function `Ψ(x, y)` is the number of
positive integers `n ≤ x` all of whose prime factors are at most `y`. It is the function whose
size, for `y = x ^ (1 / u)`, is described by the Dickman function.

Mathlib's `Nat.smoothNumbersUpTo N k` is the finite set of positive integers `n ≤ N` all of whose
prime factors are *strictly* less than `k`. The inclusive condition `p ≤ y` on a prime `p` is
`p < ⌊y⌋₊ + 1`, so `Ψ(x, y)` is defined as the cardinality of
`Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1)`. For instance `Ψ(5, 5) = 5`, while
`Nat.smoothNumbersUpTo 5 5` has only the four elements `1, 2, 3, 4`.

## Main definitions

* `TauCeti.smoothCount x y`: the smooth-number counting function `Ψ(x, y)`.

## Main results

* `TauCeti.smoothCount_eq_card_filter`: `Ψ(x, y)` counts the `n` in `[1, ⌊x⌋₊]` all of whose prime
  factors `p` satisfy `(p : ℝ) ≤ y`.
* `TauCeti.smoothCount_mono`: `Ψ` is nondecreasing in each of its two arguments.
* `TauCeti.smoothCount_le_natFloor`: `Ψ(x, y) ≤ ⌊x⌋₊`.
* `TauCeti.smoothCount_eq_natFloor`: `Ψ(x, y) = ⌊x⌋₊` when `x ≤ y`.
* `TauCeti.smoothCount_pos`: `0 < Ψ(x, y)` exactly when `1 ≤ x`, since `1` is always counted.

## References

* A. Hildebrand, G. Tenenbaum, *Integers without large prime factors*, J. Théor. Nombres
  Bordeaux 5 (1993), 411–484.
-/

public section

open Finset

namespace TauCeti

/-- The smooth-number counting function `Ψ(x, y)`: the number of positive integers `n ≤ x` all of
whose prime factors are at most `y`. The cutoff passed to `Nat.smoothNumbersUpTo` is `⌊y⌋₊ + 1`
because that set requires the prime factors to be strictly less than its cutoff. -/
noncomputable def smoothCount (x y : ℝ) : ℕ :=
  #(Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1))

/-- The defining formula: `Ψ(x, y)` is the cardinality of
`Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1)`. -/
theorem smoothCount_def (x y : ℝ) :
    smoothCount x y = #(Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1)) :=
  (rfl)

/-- A natural number lies in `Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1)` exactly when it lies in
`[1, ⌊x⌋₊]` and each of its prime factors `p` satisfies `(p : ℝ) ≤ y`. -/
theorem mem_smoothNumbersUpTo_natFloor_iff {x y : ℝ} {n : ℕ} :
    n ∈ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊y⌋₊ + 1) ↔
      n ∈ Icc 1 ⌊x⌋₊ ∧ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y := by
  rw [Nat.mem_smoothNumbersUpTo, mem_Icc]
  refine ⟨fun ⟨hn, hmem⟩ ↦ ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.ne_zero_of_mem_smoothNumbers hmem), hn⟩,
    fun p hp ↦ ?_⟩, fun ⟨⟨hn₁, hn⟩, hp⟩ ↦ ⟨hn, Nat.mem_smoothNumbers'.2 fun p hp' hpn ↦ ?_⟩⟩
  · obtain ⟨hp', hpn, -⟩ := Nat.mem_primeFactors.1 hp
    exact (Nat.le_floor_iff' hp'.ne_zero).1
      (Nat.lt_succ_iff.1 (Nat.mem_smoothNumbers'.1 hmem p hp' hpn))
  · exact Nat.lt_succ_iff.2 ((Nat.le_floor_iff' hp'.ne_zero).2
      (hp p (Nat.mem_primeFactors.2 ⟨hp', hpn, Nat.one_le_iff_ne_zero.1 hn₁⟩)))

/-- `Ψ(x, y)` is the number of `n` in `[1, ⌊x⌋₊]` all of whose prime factors `p` satisfy
`(p : ℝ) ≤ y`. -/
theorem smoothCount_eq_card_filter (x y : ℝ) :
    smoothCount x y = #{n ∈ Icc 1 ⌊x⌋₊ | ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) ≤ y} := by
  rw [smoothCount_def]
  congr 1
  ext n
  rw [mem_smoothNumbersUpTo_natFloor_iff, mem_filter]

/-- Only the integer part of the first argument of `Ψ` matters. -/
@[simp]
theorem smoothCount_natFloor_left (x y : ℝ) : smoothCount (⌊x⌋₊ : ℝ) y = smoothCount x y := by
  rw [smoothCount_def, smoothCount_def, Nat.floor_natCast]

/-- Only the integer part of the second argument of `Ψ` matters. -/
@[simp]
theorem smoothCount_natFloor_right (x y : ℝ) : smoothCount x (⌊y⌋₊ : ℝ) = smoothCount x y := by
  rw [smoothCount_def, smoothCount_def, Nat.floor_natCast]

/-- At natural-number arguments, `Ψ(N, k)` is the cardinality of
`Nat.smoothNumbersUpTo N (k + 1)`. -/
theorem smoothCount_natCast (N k : ℕ) :
    smoothCount (N : ℝ) (k : ℝ) = #(Nat.smoothNumbersUpTo N (k + 1)) := by
  rw [smoothCount_def, Nat.floor_natCast, Nat.floor_natCast]

/-- `Ψ` is nondecreasing in each of its two arguments. -/
@[gcongr]
theorem smoothCount_mono {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    smoothCount x₁ y₁ ≤ smoothCount x₂ y₂ := by
  rw [smoothCount_def, smoothCount_def]
  refine card_le_card fun n hn ↦ ?_
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans (Nat.floor_mono hx),
    Nat.smoothNumbers_mono (Nat.succ_le_succ (Nat.floor_mono hy)) hn.2⟩

/-- At most `⌊x⌋₊` positive integers are counted by `Ψ(x, y)`. -/
theorem smoothCount_le_natFloor (x y : ℝ) : smoothCount x y ≤ ⌊x⌋₊ := by
  rw [smoothCount_def]
  have := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card ⌊x⌋₊ (⌊y⌋₊ + 1)
  omega

/-- If `x ≤ y`, every positive integer `n ≤ x` is counted: `Ψ(x, y) = ⌊x⌋₊`. -/
theorem smoothCount_eq_natFloor {x y : ℝ} (h : x ≤ y) : smoothCount x y = ⌊x⌋₊ := by
  rw [smoothCount_eq_card_filter, filter_true_of_mem, Nat.card_Icc, Nat.add_sub_cancel]
  intro n hn p hp
  obtain ⟨hn₁, hn⟩ := mem_Icc.1 hn
  calc (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactors hp
    _ ≤ x := (Nat.le_floor_iff' (Nat.one_le_iff_ne_zero.1 hn₁)).1 hn
    _ ≤ y := h

/-- `Ψ(x, y)` is positive exactly when `1 ≤ x`: the integer `1` has no prime factors, so it is
counted for every `y`. -/
@[simp]
theorem smoothCount_pos {x y : ℝ} : 0 < smoothCount x y ↔ 1 ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hx
    have := smoothCount_le_natFloor x y
    rw [Nat.floor_eq_zero.2 (not_le.1 hx)] at this
    omega
  · rw [smoothCount_def]
    exact card_pos.2 ⟨1, Nat.mem_smoothNumbersUpTo.2
      ⟨Nat.le_floor (by simpa using h), Nat.mem_smoothNumbers.2 ⟨one_ne_zero, by simp⟩⟩⟩

/-- `Ψ(x, y)` vanishes exactly when `x < 1`. -/
@[simp]
theorem smoothCount_eq_zero_iff {x y : ℝ} : smoothCount x y = 0 ↔ x < 1 := by
  rw [← not_le, ← smoothCount_pos (y := y), Nat.pos_iff_ne_zero, not_not]

/-! ### Examples -/

example : smoothCount 0 2 = 0 := smoothCount_eq_zero_iff.2 one_pos

example : smoothCount 10 2 = 4 := by
  rw [show (10 : ℝ) = (10 : ℕ) by norm_num, show (2 : ℝ) = (2 : ℕ) by norm_num, smoothCount_natCast]
  decide +kernel

example : smoothCount 10 3 = 7 := by
  rw [show (10 : ℝ) = (10 : ℕ) by norm_num, show (3 : ℝ) = (3 : ℕ) by norm_num, smoothCount_natCast]
  decide +kernel

example : smoothCount 5 5 = 5 := by simpa using smoothCount_eq_natFloor (le_refl (5 : ℝ))

example : #(Nat.smoothNumbersUpTo 5 5) = 4 := by decide +kernel

end TauCeti
