/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Sum of squares of parity-constrained symmetric integer families

For any `d : ℕ` and `c : ℤ`, we prove the closed form
`3 * ∑ k ∈ Finset.range d, (2 * (k : ℤ) - c) ^ 2`
`= 2 * d * (d - 1) * (2 * d - 1) - 6 * c * d * (d - 1) + 3 * d * c ^ 2`
(`Int.three_mul_sum_range_two_mul_sub_sq`). As a consequence, any injective integer family
`f : α → ℤ` on a finite set `s` whose values have the parity of `#s - 1` and satisfy `|f i| < #s`
has image `{1 - #s, 3 - #s, …, #s - 1}` (`Finset.image_eq_range_two_mul_sub_of_injOn`) and
satisfies `3 * ∑ i ∈ s, f i ^ 2 = #s * (#s ^ 2 - 1)` (`Finset.three_mul_sum_sq_of_injOn`).
In particular, this gives the `|2ρ|² = n(n² - 1)/3` norm identity for the half-sum of positive
roots in `GL_n`.

## Main results

* `Int.three_mul_sum_range_two_mul_sub_sq`: closed form for `3 * ∑ k < d, (2k - c)²`.
* `Finset.image_eq_range_two_mul_sub_of_injOn`: characterization of the image of an injective
  integer family with parity `#s - 1` and modulus `< #s`.
* `Finset.three_mul_sum_sq_of_injOn`: `3 * ∑ i ∈ s, f i ^ 2 = #s * (#s ^ 2 - 1)`.

## Provenance

Adapted from `New.three_mul_sum_range_two_mul_sub_sq` and `New.three_mul_sum_sq_of_injOn` in
`grh-lean` (https://github.com/lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/DiscreteSeries/Theta/CasimirComparison.lean`).
-/

public section

open Finset

/-- Closed form for `3 * ∑ k ∈ range d, (2k - c)²` over `ℤ`. -/
theorem Int.three_mul_sum_range_two_mul_sub_sq (c : ℤ) (d : ℕ) :
    3 * ∑ k ∈ range d, (2 * (k : ℤ) - c) ^ 2 =
      2 * (d : ℤ) * (d - 1) * (2 * d - 1) - 6 * c * d * (d - 1) + 3 * d * c ^ 2 := by
  have hexp : ∑ k ∈ range d, (2 * (k : ℤ) - c) ^ 2 =
      4 * ∑ k ∈ range d, (k : ℤ) ^ 2 - 4 * c * ∑ k ∈ range d, (k : ℤ) + d * c ^ 2 := by
    have hterm : ∀ k ∈ range d,
        (2 * (k : ℤ) - c) ^ 2 = 4 * (k : ℤ) ^ 2 - 4 * c * (k : ℤ) + c ^ 2 := fun _ _ ↦ by ring
    rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
      sum_const, card_range, nsmul_eq_mul]
  have hsq := Finset.sum_range_natCast_sq_mul_six (R := ℤ) d
  have hlin := Finset.sum_range_natCast_mul_two (R := ℤ) d
  linear_combination 3 * hexp + 2 * hsq - 6 * c * hlin

namespace Finset

/-- An injective integer family `f` on `s : Finset α` whose values have the parity of `#s - 1`
and satisfy `|f i| < #s` has image `(range #s).image (fun k ↦ 2 * (k : ℤ) - (#s - 1))`. -/
theorem image_eq_range_two_mul_sub_of_injOn {α : Type*} (s : Finset α) (f : α → ℤ)
    (hinj : Set.InjOn f s) (hparity : ∀ i ∈ s, Even (f i + #s - 1))
    (hbound : ∀ i ∈ s, |f i| < #s) :
    s.image f = (range #s).image (fun k : ℕ ↦ 2 * (k : ℤ) - (#s - 1)) := by
  let g (k : ℕ) : ℤ := 2 * (k : ℤ) - (#s - 1)
  have hginj : Function.Injective g := fun j k hjk ↦ by
    have h : 2 * (j : ℤ) - (#s - 1) = 2 * k - (#s - 1) := hjk
    omega
  have hsub : s.image f ⊆ (range #s).image g := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    obtain ⟨k, hk⟩ := hparity i hi
    have hlt := abs_lt.mp (hbound i hi)
    refine mem_image.mpr ⟨k.toNat, mem_range.mpr ?_, ?_⟩
    · omega
    · simp only [g]
      omega
  exact eq_of_subset_of_card_le hsub <| by
    rw [card_image_of_injective _ hginj, card_range, card_image_of_injOn hinj]

/-- A set of `#s` distinct integers of the parity of `#s - 1` and of modulus below `#s` satisfies
`3 * ∑ i ∈ s, f i ^ 2 = #s * (#s ^ 2 - 1)`. -/
theorem three_mul_sum_sq_of_injOn {α : Type*} (s : Finset α) (f : α → ℤ)
    (hinj : Set.InjOn f s) (hparity : ∀ i ∈ s, Even (f i + #s - 1))
    (hbound : ∀ i ∈ s, |f i| < #s) :
    3 * ∑ i ∈ s, f i ^ 2 = (#s : ℤ) * ((#s : ℤ) ^ 2 - 1) := by
  let g (k : ℕ) : ℤ := 2 * (k : ℤ) - (#s - 1)
  have hginj : Function.Injective g := fun j k hjk ↦ by
    have h : 2 * (j : ℤ) - (#s - 1) = 2 * k - (#s - 1) := hjk
    omega
  have himg := image_eq_range_two_mul_sub_of_injOn s f hinj hparity hbound
  calc 3 * ∑ i ∈ s, f i ^ 2 = 3 * ∑ z ∈ s.image f, z ^ 2 := by rw [sum_image hinj]
    _ = 3 * ∑ k ∈ range #s, g k ^ 2 := by rw [himg, sum_image hginj.injOn]
    _ = (#s : ℤ) * ((#s : ℤ) ^ 2 - 1) := by
      dsimp [g]
      rw [Int.three_mul_sum_range_two_mul_sub_sq]
      ring

end Finset
