/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Support, disjointness and size of function antidiagonals

`Finset.piAntidiag s n` is the finset of functions with support contained in `s` whose values sum
to `n` over `s`. Such a function therefore vanishes at every point outside `s`, and for a fixed `s`
the finsets `Finset.piAntidiag s n` are pairwise disjoint across sums `n`. For `s = univ` in a
finite type `ι` and `μ = ℕ`, the members of the antidiagonals of sums `< T` have every entry `< T`,
so there are at most `T ^ card ι` of them; this counts the Taylor coefficients of degree `< T` of a
function of `card ι` variables.

## Main results

* `Finset.piAntidiag_singleton_eq`: the compositions of `n` supported on a singleton `{i}` are
  the single function with value `n` at `i`.
* `Finset.eq_zero_of_notMem_of_mem_piAntidiag`: a member of `Finset.piAntidiag s n` vanishes off
  `s`.
* `Finset.pairwiseDisjoint_piAntidiag`, `Finset.sum_biUnion_piAntidiag`: the function antidiagonals
  over `s` are pairwise disjoint across target sums, so a sum over a union of antidiagonals is taken
  value by value.
* `Finset.card_biUnion_range_piAntidiag_le`: there are at most `T ^ card ι` multi-indices
  `α : ι → ℕ` of total degree `< T`.
-/

public section

namespace Finset

variable {ι μ : Type*} [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]
  {s : Finset ι} {n : μ} {f : ι → μ} {i : ι}

/-- A function in `Finset.piAntidiag s n` has support contained in `s`, so it takes the value `0`
at every point outside `s`. -/
theorem eq_zero_of_notMem_of_mem_piAntidiag (hi : i ∉ s) (hf : f ∈ piAntidiag s n) : f i = 0 :=
  not_not.1 fun h ↦ hi ((mem_piAntidiag.1 hf).2 i h)

/-- The compositions of `N` supported on a singleton `{i}` are the single vector with value `N`
at `i`. -/
@[simp]
theorem piAntidiag_singleton_eq (i : ι) (N : μ) :
    piAntidiag {i} N = {Function.update (0 : ι → μ) i N} := by
  ext f
  simp only [mem_piAntidiag, sum_singleton, mem_singleton]
  constructor
  · rintro ⟨hf, hs⟩
    ext j
    by_cases hji : j = i
    · subst j; simpa using hf
    · simp only [Function.update_of_ne hji]
      exact not_ne_iff.mp (fun h ↦ hji (hs j h))
  · rintro rfl
    refine ⟨by simp, fun j hj ↦ ?_⟩
    by_contra hji
    simp [Function.update_of_ne hji] at hj

/-- The function antidiagonals `Finset.piAntidiag s n` are pairwise disjoint across sums `n`. -/
theorem pairwiseDisjoint_piAntidiag (s : Finset ι) (t : Set μ) :
    t.PairwiseDisjoint (piAntidiag s) :=
  fun _ _ _ _ hmn ↦ disjoint_left.2 fun _ hm hn ↦
    hmn ((mem_piAntidiag.1 hm).1.symm.trans (mem_piAntidiag.1 hn).1)

/-- A product over a union of function antidiagonals is taken antidiagonal by antidiagonal. -/
@[to_additive /-- A sum over a union of function antidiagonals is taken antidiagonal by
antidiagonal. -/]
theorem prod_biUnion_piAntidiag {M : Type*} [CommMonoid M] [DecidableEq (ι → μ)] (s : Finset ι)
    (t : Finset μ) (g : (ι → μ) → M) :
    ∏ f ∈ t.biUnion (piAntidiag s), g f = ∏ k ∈ t, ∏ f ∈ piAntidiag s k, g f :=
  prod_biUnion (pairwiseDisjoint_piAntidiag s (t : Set μ))

/-- There are at most `T ^ card ι` multi-indices `α : ι → ℕ` of total degree `< T`: each of their
entries is `< T`. -/
theorem card_biUnion_range_piAntidiag_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℕ) :
    #((range T).biUnion (piAntidiag (univ : Finset ι))) ≤ T ^ Fintype.card ι := by
  calc #((range T).biUnion (piAntidiag (univ : Finset ι)))
      ≤ #(Fintype.piFinset fun _ : ι ↦ range T) := by
        refine card_le_card fun α hα ↦ ?_
        obtain ⟨k, hk, hαk⟩ := mem_biUnion.1 hα
        rw [mem_range] at hk
        rw [mem_piAntidiag] at hαk
        exact Fintype.mem_piFinset.2 fun i ↦ mem_range.2 <|
          (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i)).trans_lt (hαk.1 ▸ hk)
    _ = T ^ Fintype.card ι := by simp

end Finset
