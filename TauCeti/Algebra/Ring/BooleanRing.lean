/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Partition of unity in a Boolean ring

For any finite subset `X` of a Boolean ring `S`, the indicator products
`e T = (∏ x ∈ T, x) * ∏ x ∈ X \ T, (1 - x)` indexed by subsets `T ⊆ X` sum to `1` and satisfy
`e T * x = (if x ∈ T then 1 else 0) * e T` for every `x ∈ X`.

## Main results

* `TauCeti.booleanRing_partition_unity`: the indicator products over `X.powerset` form a partition
  of unity that diagonalizes multiplication by elements of `X`.
-/

public section

namespace TauCeti

/-- For a finite subset `X` of a Boolean ring `S`, the indicator products
`e T = (∏ x ∈ T, x) * ∏ x ∈ X \ T, (1 - x)` form a partition of unity that diagonalizes
multiplication by elements of `X`. -/
theorem booleanRing_partition_unity {S : Type*} [BooleanRing S] [DecidableEq S]
    (X : Finset S) :
    let e : Finset S → S := fun T ↦ (∏ x ∈ T, x) * ∏ x ∈ X \ T, (1 - x)
    (∑ T ∈ X.powerset, e T = 1) ∧
      ∀ (T : Finset S) {x : S}, x ∈ X →
        e T * x = (if x ∈ T then (1 : S) else 0) * e T := by
  intro e
  refine ⟨?_, fun T x hx ↦ ?_⟩
  · simpa [e, add_sub_cancel] using
      (Finset.prod_add (fun x : S ↦ x) (fun x : S ↦ 1 - x) X).symm
  · by_cases hxT : x ∈ T
    · simp only [hxT, ↓reduceIte, one_mul, e]
      rw [← Finset.mul_prod_erase T (fun y ↦ y) hxT]
      linear_combination
        (∏ y ∈ T.erase x, y) * (∏ y ∈ X \ T, (1 - y)) * BooleanRing.mul_self x
    · have hx_sdiff : x ∈ X \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
      simp only [hxT, ↓reduceIte, zero_mul, e]
      rw [← Finset.mul_prod_erase (X \ T) (fun y ↦ 1 - y) hx_sdiff]
      have h1x : (1 - x) * x = 0 := by rw [sub_mul, one_mul, BooleanRing.mul_self x, sub_self]
      linear_combination (∏ y ∈ T, y) * (∏ y ∈ (X \ T).erase x, (1 - y)) * h1x

end TauCeti
