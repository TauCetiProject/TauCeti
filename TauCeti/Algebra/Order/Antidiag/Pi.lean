/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Vanishing off the index set of a function antidiagonal

`Finset.piAntidiag s n` is the finset of functions with support contained in `s` whose values sum
to `n` over `s`.  Such a function therefore vanishes at every point outside `s`.

## Main results

* `Finset.piAntidiag_singleton_eq`: the compositions of `n` supported on a singleton `{i}` are
  the single function with value `n` at `i`.
* `Finset.eq_zero_of_notMem_of_mem_piAntidiag`: a member of `Finset.piAntidiag s n` vanishes off
  `s`.
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

end Finset
