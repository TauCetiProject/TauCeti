/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Card

/-!
# Antitone finitely supported sequences

A finitely supported sequence `f : ℕ →₀ α` that is antitone takes only nonnegative values, and
it is determined by how many times it takes each nonzero value: it lists its nonzero values in
nonincreasing order, followed by zeros. Sorted, zero-padded sequences of this kind are how
Mathlib records singular values (`LinearMap.singularValues`), so this is the uniqueness
principle used to identify two such sequences from their multiplicities.

## Main declarations

* `Finsupp.nonneg_of_antitone`: an antitone finitely supported sequence is nonnegative.
* `Finsupp.eq_of_antitone_of_ncard_eq`: two antitone finitely supported sequences that take
  every nonzero value equally often are equal.
-/

public section

namespace Finsupp

variable {α : Type*} [LinearOrder α] [Zero α]

/-- An antitone finitely supported sequence takes only nonnegative values. -/
theorem nonneg_of_antitone {f : ℕ →₀ α} (hf : Antitone f) (i : ℕ) : 0 ≤ f i := by
  obtain ⟨n, hn⟩ := f.support.exists_nat_subset_range
  have hfn : f (max i n) = 0 :=
    notMem_support_iff.mp fun h ↦ (Finset.mem_range.mp (hn h)).not_ge (le_max_right i n)
  exact hfn ▸ hf (le_max_left i n)

/-- Two sequences that agree below `i`, with `g` antitone and `g i < f i`, cannot take every
nonzero value equally often: `g` takes the value `f i` fewer times than `f` does. -/
private theorem false_of_lt_of_ncard_eq {f g : ℕ →₀ α} (hg : Antitone g) {i : ℕ}
    (hfg : ∀ j < i, f j = g j) (hi : g i < f i)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : False := by
  have hfi : f i ≠ 0 := ((nonneg_of_antitone hg i).trans_lt hi).ne'
  refine (Set.ncard_lt_ncard ⟨fun j hj ↦ ?_, fun h ↦ ?_⟩ <|
    f.support.finite_toSet.subset fun j (hj : f j = f i) ↦ mem_support_iff.mpr (hj ▸ hfi)).ne
      (h _ hfi).symm
  · have hji : j < i := lt_of_not_ge fun hij ↦ (hg hij).not_gt (hj ▸ hi)
    exact (hfg j hji).trans hj
  · exact hi.ne (h (rfl : f i = f i))

/-- An antitone finitely supported sequence is determined by how many times it takes each nonzero
value. -/
theorem eq_of_antitone_of_ncard_eq {f g : ℕ →₀ α} (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f = g := by
  by_contra hne
  have hex : ∃ i, f i ≠ g i := by simpa [Finsupp.ext_iff] using hne
  classical
  have hfg : ∀ j < Nat.find hex, f j = g j := fun j hj ↦ not_not.mp (Nat.find_min hex hj)
  rcases (Nat.find_spec hex).lt_or_gt with hlt | hlt
  · exact false_of_lt_of_ncard_eq hf (fun j hj ↦ (hfg j hj).symm) hlt fun a ha ↦ (h a ha).symm
  · exact false_of_lt_of_ncard_eq hg hfg hlt h

end Finsupp
