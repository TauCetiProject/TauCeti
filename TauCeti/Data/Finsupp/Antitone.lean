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
Nonnegativity holds in any preorder, and uniqueness requires only a partial order on the values.

## Main declarations

* `Finsupp.nonneg_of_antitone`: an antitone finitely supported sequence is nonnegative.
* `Finsupp.eq_of_antitone_of_ncard_eq`: two antitone finitely supported sequences that take
  every nonzero value equally often are equal.
-/

public section

namespace Finsupp

variable {α : Type*} [Zero α]

/-- An antitone finitely supported sequence takes only nonnegative values. -/
theorem nonneg_of_antitone [Preorder α] {f : ℕ →₀ α} (hf : Antitone f) (i : ℕ) :
    0 ≤ f i := by
  obtain ⟨n, hn⟩ := f.support.exists_nat_subset_range
  have hfn : f (max i n) = 0 :=
    notMem_support_iff.mp fun h ↦ (Finset.mem_range.mp (hn h)).not_ge (le_max_right i n)
  exact hfn ▸ hf (le_max_left i n)

/-- If two sequences agree below `i` and take each nonzero value equally often, the `i`-th
entry of the first lies below that of the second whenever the second is antitone. -/
private theorem le_of_antitone_of_ncard_eq [Preorder α] {f g : ℕ →₀ α} (hg : Antitone g)
    {i : ℕ} (hfg : ∀ j < i, f j = g j)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f i ≤ g i := by
  by_contra hi
  have hfi : f i ≠ 0 := fun hfi ↦ hi (hfi ▸ nonneg_of_antitone hg i)
  refine (Set.ncard_lt_ncard ⟨fun j hj ↦ ?_, fun h ↦ ?_⟩ <|
    f.support.finite_toSet.subset (t := {j | f j = f i}) fun j (hj : f j = f i) ↦
      mem_support_iff.mpr (hj ▸ hfi)).ne
      (h _ hfi).symm
  · have hji : j < i := lt_of_not_ge fun hij ↦ hi (hj ▸ hg hij)
    exact (hfg j hji).trans hj
  · exact hi (h (rfl : f i = f i)).ge

/-- An antitone finitely supported sequence is determined by how many times it takes each nonzero
value. -/
theorem eq_of_antitone_of_ncard_eq [PartialOrder α] {f g : ℕ →₀ α}
    (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f = g := by
  ext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    exact le_antisymm (le_of_antitone_of_ncard_eq hg ih h)
      (le_of_antitone_of_ncard_eq hf (fun j hj ↦ (ih j hj).symm) fun a ha ↦ (h a ha).symm)

end Finsupp
