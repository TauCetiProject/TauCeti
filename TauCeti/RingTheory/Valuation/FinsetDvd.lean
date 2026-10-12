/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# A finite family in a ring with total divisibility has a member dividing all others

In a monoid with total divisibility, for instance a valuation ring or the `p`-adic integers, any
two elements are comparable for divisibility. Consequently a finite nonempty family of elements
has a member that divides every member of the family: the divisibility preorder restricted to the
family is total, and a finite nonempty totally preordered set has a least element.

This is what picks, in a vector with entries in a discrete valuation ring, a coordinate of
minimal valuation, which then divides all the other coordinates.

## Main results

* `TauCeti.PreValuationRing.exists_mem_forall_dvd`: a finite nonempty family in a monoid with
  total divisibility has a member dividing every member.
* `TauCeti.PreValuationRing.exists_forall_dvd`: the same for a family indexed by a finite nonempty
  type.
-/

public section

namespace TauCeti

namespace PreValuationRing

variable {R : Type*} [Monoid R] [PreValuationRing R] {ι : Type*}

/-- In a monoid with total divisibility, a finite nonempty family has a member dividing every
member of the family. -/
theorem exists_mem_forall_dvd {s : Finset ι} (hs : s.Nonempty) (f : ι → R) :
    ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, Finset.mem_singleton_self a, fun j hj ↦ by rw [Finset.mem_singleton.mp hj]⟩
  | cons a s ha _ ih =>
    obtain ⟨i, hi, hfi⟩ := ih
    rcases ValuationRing.dvd_total (f a) (f i) with h | h
    · refine ⟨a, Finset.mem_cons_self a s, fun j hj ↦ ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact dvd_rfl
      · exact h.trans (hfi j hj)
    · refine ⟨i, Finset.mem_cons_of_mem hi, fun j hj ↦ ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact h
      · exact hfi j hj

/-- In a monoid with total divisibility, a family indexed by a finite nonempty type has a member
dividing every member of the family. -/
theorem exists_forall_dvd [Finite ι] [Nonempty ι] (f : ι → R) : ∃ i, ∀ j, f i ∣ f j := by
  cases nonempty_fintype ι
  obtain ⟨i, -, h⟩ := exists_mem_forall_dvd Finset.univ_nonempty f
  exact ⟨i, fun j ↦ h j (Finset.mem_univ j)⟩

end PreValuationRing

end TauCeti
