/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Fin

/-!
# Function antidiagonals: vanishing off the index set, and coordinate counts

`Finset.piAntidiag s n` is the finset of functions with support contained in `s` whose values sum
to `n` over `s`.  Such a function therefore vanishes at every point outside `s`.  Over a finite
type, the members of `Finset.univ.piAntidiag k` are exactly the coordinate counts of the tuples
`Fin k → ι`, the multi-indices of total degree `k`.

## Main results

* `Finset.piAntidiag_singleton_eq`: the compositions of `n` supported on a singleton `{i}` are
  the single function with value `n` at `i`.
* `Finset.eq_zero_of_notMem_of_mem_piAntidiag`: a member of `Finset.piAntidiag s n` vanishes off
  `s`.
* `Finset.exists_card_fiber_eq_of_mem_piAntidiag`: every member `α` of `Finset.univ.piAntidiag k`
  is the coordinate count of some tuple `a : Fin k → ι`, in which each `i` occurs `α i` times.
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

/-- Every multi-index `α` of total degree `k` is the coordinate count of a tuple: there is
`a : Fin k → ι` in which each `i` occurs exactly `α i` times. -/
theorem exists_card_fiber_eq_of_mem_piAntidiag [Fintype ι] {k : ℕ} {α : ι → ℕ}
    (hα : α ∈ univ.piAntidiag k) : ∃ a : Fin k → ι, ∀ i, Fintype.card {j // a j = i} = α i := by
  -- List the multiset in which each `i` occurs `α i` times, and read off its entries.
  set l := (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm α)).toList
  have hl : l.length = k := by
    simp [l, Finsupp.card_toMultiset, Finsupp.sum_fintype, (mem_piAntidiag.1 hα).1]
  refine ⟨fun j ↦ l.get (Fin.cast hl.symm j), fun i ↦ ?_⟩
  rw [Fintype.card_subtype, ← List.count_ofFn, ← List.ofFn_congr hl l.get, List.ofFn_get]
  simp [l, ← Multiset.coe_count, Finsupp.count_toMultiset]

end Finset
