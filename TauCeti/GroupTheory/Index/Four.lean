/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# Index four from four covering cosets

Let `H` be a normal subgroup of a group `G`, and suppose that every element of `G` lies in one of
the left cosets `H`, `s H`, `d H` and `g H`. Then `H` has index at most four. If moreover
`s ∉ H` while `s² ∈ H`, and `d ∉ H` lies outside `s H`, then the index is exactly four: the index
is not one since `s ∉ H`; it is not three, since then `s³ ∈ H` and so `s ∈ H`; and it is not two,
since in a group of order two the cosets of `s` and `d`, both nontrivial, would agree. Unlike for
the corresponding statement with three cosets, the cosets `g H` and `d H` need not be shown
distinct.

For example, at Tate's reduction symbol `Iₙ*` the points of an elliptic curve with singular
reduction fall into classes: those reducing near the simple root of a residue cubic, whose
classes are of order two, and one class for each root of a residue quadratic. When the quadratic
has a root, the subgroup of points with nonsingular reduction has index four.

## Main results

* `Subgroup.index_eq_four_of_sq_mem` and `AddSubgroup.index_eq_four_of_two_nsmul_mem`: if `G` is
  covered by the cosets `H`, `s H`, `d H` and `g H`, with `s ∉ H`, `s² ∈ H`, `d ∉ H` and
  `s⁻¹ d ∉ H`, then `H.index = 4`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal]

/-- **Four covering cosets and an element of order two give index four.** If every `a` satisfies
`a ∈ H`, `s⁻¹ a ∈ H`, `d⁻¹ a ∈ H` or `g⁻¹ a ∈ H` (that is, `a` lies in `H`, `s H`, `d H` or `g H`),
and `s ∉ H`, `s² ∈ H`, `d ∉ H` and `s⁻¹ d ∉ H`, then `H.index = 4`. -/
@[to_additive index_eq_four_of_two_nsmul_mem /-- **Four covering cosets and an element of order
two give index four.** If every `a` satisfies `a ∈ H`, `-s + a ∈ H`, `-d + a ∈ H` or `-g + a ∈ H`
(that is, `a` lies in `H`, `s + H`, `d + H` or `g + H`), and `s ∉ H`, `2 • s ∈ H`, `d ∉ H` and
`-s + d ∉ H`, then `H.index = 4`. -/]
theorem index_eq_four_of_sq_mem {s d g : G}
    (h : ∀ a, a ∈ H ∨ s⁻¹ * a ∈ H ∨ d⁻¹ * a ∈ H ∨ g⁻¹ * a ∈ H) (hs : s ∉ H) (hs₂ : s ^ 2 ∈ H)
    (hd : d ∉ H) (hsd : s⁻¹ * d ∉ H) : H.index = 4 := by
  -- `1`, `s`, `d` and `g` represent every class of `G ⧸ H`
  have hf : Function.Surjective ![((1 : G) : G ⧸ H), (s : G ⧸ H), (d : G ⧸ H), (g : G ⧸ H)] := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rcases h a with ha | ha | ha | ha
    · exact ⟨0, QuotientGroup.eq.2 (by rwa [inv_one, one_mul])⟩
    · exact ⟨1, QuotientGroup.eq.2 ha⟩
    · exact ⟨2, QuotientGroup.eq.2 ha⟩
    · exact ⟨3, QuotientGroup.eq.2 ha⟩
  have : Finite (G ⧸ H) := Finite.of_surjective _ hf
  have hle : H.index ≤ 4 := by
    rw [index_eq_card]
    exact (Nat.card_le_card_of_surjective _ hf).trans_eq (by simp)
  have h0 : H.index ≠ 0 := index_ne_zero_of_finite
  have h1 : H.index ≠ 1 := fun h1 ↦ hs (index_eq_one.1 h1 ▸ mem_top s)
  have h2 : H.index ≠ 2 := fun h2 ↦ hsd <| by
    rw [mul_mem_iff_of_index_two h2, inv_mem_iff]
    exact iff_of_false hs hd
  have h3 : H.index ≠ 3 := fun h3 ↦ hs <| by
    have h3s := H.pow_index_mem s
    rw [h3] at h3s
    rw [show s = (s ^ 2)⁻¹ * s ^ 3 by group]
    exact H.mul_mem (H.inv_mem hs₂) h3s
  omega

end Subgroup
