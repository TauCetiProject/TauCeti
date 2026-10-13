/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card

/-!
# A subgroup with three cosets

Let `H` be a subgroup of a group `G` and `g` an element with `g² ∉ H`. Then `H`, `g H` and
`g⁻¹ H` are three distinct left cosets: `g ∉ H` and `g⁻¹ ∉ H` because `g² ∉ H`, and
`g H = g⁻¹ H` would put `g² = (g⁻¹)⁻¹ g` in `H`. If every element of `G` lies in one of them,
then `H` has index three.

This is the shape in which index three arises from a classification of the elements outside `H`
into two classes exchanged by inversion: for instance the points of an elliptic curve with
singular reduction at Tate's reduction symbol `IV*`, sorted by the root of a residue quadratic
that the residue of `y / ϖ²` is.

## Main results

* `Subgroup.index_eq_three_of_sq_notMem` and `AddSubgroup.index_eq_three_of_two_nsmul_notMem`: if
  `g² ∉ H` and every element lies in `H`, `g H` or `g⁻¹ H`, then `H.index = 3`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **A subgroup covered by three cosets `H`, `g H`, `g⁻¹ H` with `g² ∉ H` has index three.**
The condition `g² ∉ H` makes the three cosets distinct, and the covering hypothesis says that
every element `a` lies in `H`, in `g H` (that is `g⁻¹ a ∈ H`) or in `g⁻¹ H` (that is
`g a ∈ H`). -/
@[to_additive index_eq_three_of_two_nsmul_notMem /-- **An additive subgroup covered by three
cosets `H`, `g + H`, `-g + H` with `2 • g ∉ H` has index three.** The condition `2 • g ∉ H` makes
the three cosets distinct, and the covering hypothesis says that every element `a` lies in `H`, in
`g + H` (that is `-g + a ∈ H`) or in `-g + H` (that is `g + a ∈ H`). -/]
theorem index_eq_three_of_sq_notMem {g : G} (hg : g ^ 2 ∉ H)
    (h : ∀ a, a ∈ H ∨ g⁻¹ * a ∈ H ∨ g * a ∈ H) : H.index = 3 := by
  have hg₁ : g ∉ H := fun hg₁ ↦ hg (H.pow_mem hg₁ 2)
  rw [index_eq_card, ← Set.ncard_univ, Set.ncard_eq_three]
  refine ⟨((1 : G) : G ⧸ H), (g : G ⧸ H), ((g⁻¹ : G) : G ⧸ H), ?_, ?_, ?_, ?_⟩
  · rw [Ne, QuotientGroup.eq]
    simpa using hg₁
  · rw [Ne, QuotientGroup.eq]
    simpa using hg₁
  · rw [Ne, QuotientGroup.eq]
    intro h'
    exact hg (by simpa [pow_two] using H.inv_mem h')
  · refine Set.eq_of_subset_of_subset (fun q _ ↦ ?_) (Set.subset_univ _)
    induction q using QuotientGroup.induction_on with | H a => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, QuotientGroup.eq]
    rcases h a with ha | ha | ha
    · exact Or.inl (by simpa using ha)
    · exact Or.inr (Or.inl (by simpa using H.inv_mem ha))
    · exact Or.inr (Or.inr (by simpa using H.inv_mem ha))

end Subgroup
