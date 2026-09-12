/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Majorization

import Mathlib.Tactic

/-!
# Uniqueness of the CAR staircase occupation weight

The half-integral weights arising from the CAR model have the form `a i + 1 / 2`, where `a` is a
tuple of natural-number occupation counts. This file specializes the integer staircase criterion
from `TauCeti.Combinatorics.Majorization` to the finite natural-number tuples produced by that
model.

## Main results

* `TauCeti.eq_finRev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq`: a natural occupation
  tuple dominated by `Fin.rev`, with the same total and quadratic sum, is `Fin.rev`.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transform. Groups 6
  (2001), 371–396, Proposition 2.4 and Example 2.5(1), for the CAR staircase-weight application.
-/

public section

namespace TauCeti

open scoped BigOperators

/-- **A majorized occupation weight with the staircase quadratic value is the staircase.**

Let `a : Fin N → ℕ` be weakly decreasing. Suppose every proper initial sum of `a` is at most
the corresponding initial sum of the reverse-index tuple `i ↦ N - 1 - i`, and suppose the total
sums are equal. If the two tuples also have the same value under

`a ↦ ∑ i, a i * (a i + N - 2i)`,

then `a` is the reverse-index tuple. For CAR highest weights this is the integral form of the
trace-form `gl_N` Casimir polynomial after a common half-unit shift. -/
theorem eq_finRev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    {N : ℕ} (a : Fin N → ℕ) (ha : Antitone a)
    (hmajor : ∀ (k : ℕ) (hk : k < N),
      (∑ i : Fin k, (a (Fin.castLE hk.le i) : ℤ)) ≤
        ∑ i : Fin k, ((Fin.rev (Fin.castLE hk.le i) : ℕ) : ℤ))
    (hsum : (∑ i : Fin N, (a i : ℤ)) =
      ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ))
    (hcasimir :
      (∑ i : Fin N, (a i : ℤ) * ((a i : ℤ) + (N : ℤ) - 2 * (i : ℕ))) =
        ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ) *
          (((Fin.rev i : ℕ) : ℤ) + (N : ℤ) - 2 * (i : ℕ))) :
    a = fun i => (Fin.rev i : ℕ) := by
  let aZ : ℕ → ℤ := fun i => if hi : i < N then a ⟨i, hi⟩ else 0
  have haZ : ∀ i, i + 1 < N → aZ (i + 1) ≤ aZ i := by
    intro i hi
    have hi' : i < N := by omega
    simpa only [aZ, dite_eq_left hi, dite_eq_left hi'] using
      mod_cast ha (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, hi'⟩ : Fin N) ≤ ⟨i + 1, hi⟩)
  have hmajorZ : ∀ (k : ℕ), k < N →
      (∑ i ∈ Finset.range k, aZ i) ≤
        ∑ i ∈ Finset.range k, ((N - (i + 1) : ℕ) : ℤ) := by
    intro k hk
    rw [← Fin.sum_univ_eq_sum_range aZ k,
      ← Fin.sum_univ_eq_sum_range (fun i => ((N - (i + 1) : ℕ) : ℤ)) k]
    convert hmajor k hk using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · have hiN : i < N := lt_trans i.isLt hk
      simp only [aZ, dite_eq_left hiN]
      congr 1
    · rfl
  have hsumZ : (∑ i ∈ Finset.range N, aZ i) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range aZ N,
      ← Fin.sum_univ_eq_sum_range (fun i => ((N - (i + 1) : ℕ) : ℤ)) N]
    convert hsum using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · simp [aZ, i.isLt]
    · rfl
  have hcasimirZ :
      (∑ i ∈ Finset.range N, aZ i * (aZ i + (N : ℤ) - 2 * i)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) *
        (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i) := by
    rw [← Fin.sum_univ_eq_sum_range
        (fun i => aZ i * (aZ i + (N : ℤ) - 2 * i)) N,
      ← Fin.sum_univ_eq_sum_range
        (fun i => ((N - (i + 1) : ℕ) : ℤ) *
          (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i)) N]
    convert hcasimir using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · simp [aZ, i.isLt]
    · rfl
  funext i
  have h := eq_staircase_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    aZ haZ hmajorZ hsumZ hcasimirZ i i.isLt
  have hcast : ((a i : ℕ) : ℤ) = ((Fin.rev i : ℕ) : ℤ) := by
    simpa [aZ, i.isLt, Fin.rev] using h
  exact_mod_cast hcast

end TauCeti
