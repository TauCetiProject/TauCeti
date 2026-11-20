/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Card
import Mathlib.Order.Interval.Set.Infinite

/-!
# Antitone finitely supported sequences

An antitone finitely supported function on an order with no maximal element, such as a sequence
`f : ℕ →₀ α`, takes only nonnegative values. An antitone finitely supported sequence is moreover
determined by how many times it takes each positive value: it lists
its nonzero values in nonincreasing order, followed by zeros. Sorted, zero-padded sequences of this
kind are how Mathlib records singular values (`LinearMap.singularValues`), so this is the uniqueness
principle used to identify two such sequences from their multiplicities.
Nonnegativity holds in any preorder, and uniqueness requires only a partial order on the values.

## Main declarations

* `Finsupp.nonneg_of_antitone`: an antitone finitely supported function on an order with no
  maximal element is nonnegative.
* `Finsupp.eq_of_antitone_of_ncard_eq`: two antitone finitely supported sequences that take
  every positive value equally often are equal.
-/

public section

namespace Finsupp

variable {α : Type*} [Zero α]

/-- An antitone finitely supported function on an order with no maximal element takes only
nonnegative values. -/
theorem nonneg_of_antitone {ι : Type*} [Preorder ι] [NoMaxOrder ι] [Preorder α] {f : ι →₀ α}
    (hf : Antitone f) (i : ι) : 0 ≤ f i := by
  obtain ⟨j, hij, hj⟩ := (Set.Ici_infinite i).exists_notMem_finset f.support
  exact notMem_support_iff.mp hj ▸ hf hij

/-- If two sequences agree below `i` and take each value equally often, the `i`-th entry of the
first lies below that of the second whenever the second is antitone. -/
private theorem le_of_antitone_of_ncard_eq [Preorder α] {f g : ℕ →₀ α} (hg : Antitone g)
    {i : ℕ} (hfg : ∀ j < i, f j = g j)
    (h : ∀ a, {i | f i = a}.ncard = {i | g i = a}.ncard) : f i ≤ g i := by
  by_contra hi
  have hfi : f i ≠ 0 := fun hfi ↦ hi (hfi ▸ nonneg_of_antitone hg i)
  refine (Set.ncard_lt_ncard ⟨fun j hj ↦ ?_, fun h ↦ ?_⟩ <|
    f.support.finite_toSet.subset (t := {j | f j = f i}) fun j (hj : f j = f i) ↦
      mem_support_iff.mpr (hj ▸ hfi)).ne
      (h _).symm
  · have hji : j < i := lt_of_not_ge fun hij ↦ hi (hj ▸ hg hij)
    exact (hfg j hji).trans hj
  · exact hi (h (rfl : f i = f i)).ge

/-- An antitone finitely supported sequence is determined by how many times it takes each positive
value. -/
theorem eq_of_antitone_of_ncard_eq [PartialOrder α] {f g : ℕ →₀ α}
    (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a > 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f = g := by
  have h' (a : α) : {i | f i = a}.ncard = {i | g i = a}.ncard := by
    by_cases ha : 0 < a
    · exact h a ha
    · rw [ncard_ofPred_eq_zero_of_nonneg_of_not_pos (nonneg_of_antitone hf) ha,
        ncard_ofPred_eq_zero_of_nonneg_of_not_pos (nonneg_of_antitone hg) ha]
  ext i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    exact le_antisymm (le_of_antitone_of_ncard_eq hg ih h')
      (le_of_antitone_of_ncard_eq hf (fun j hj ↦ (ih j hj).symm) fun a ↦ (h' a).symm)

end Finsupp
