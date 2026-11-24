/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Separating subgroups of a linearly ordered group

A subgroup not contained in another is separated from it by an element of prescribed sign:
`¬Γ' ≤ Δ` holds exactly when some member of `Γ'` outside `Δ` exceeds `1`, and dually exactly when
one lies below `1`. In particular this applies to a strictly larger subgroup, `Δ < Γ'`. Nothing
beyond a group, a linear order and strictly monotone left multiplication is assumed.

That the witness has a *strict* sign is what these are for. A monotone map out of `Γ` carries a
bound only to `≤`; a witness of this shape is what upgrades such a bound to the strict inequality
a cofinality argument needs.

## Main results

* `Subgroup.not_le_iff_exists_one_lt` and `Subgroup.not_le_iff_exists_lt_one` : the two
  orientations of the separation statement.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §1.4 — the convex-subgroup and cofinality
  material these lemmas serve, in particular Definition 1.16 and Corollary 1.21.

Adapted from the AINTLIB development (Apache 2.0), file
`projects/AdicSpaces/Adic spaces/OrderedGroupConvex.lean`.
-/

public section

variable {Γ : Type*} [Group Γ] [LinearOrder Γ] [MulLeftStrictMono Γ] {Γ' Δ : Subgroup Γ}

/-- **A subgroup not contained in another is separated from it by an element above `1`**:
`Γ'` fails to lie in `Δ` exactly when some member of `Γ'` outside `Δ` exceeds `1`. This is the
signed refinement of `IsConcreteLE.not_le_iff_exists`. -/
theorem Subgroup.not_le_iff_exists_one_lt : ¬Γ' ≤ Δ ↔ ∃ z ∈ Γ', z ∉ Δ ∧ 1 < z := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hzΓ', hzΔ, _⟩ ↦ IsConcreteLE.not_le_iff_exists.mpr ⟨z, hzΓ', hzΔ⟩⟩
  obtain ⟨x, hxΓ', hxΔ⟩ := IsConcreteLE.not_le_iff_exists.mp h
  rcases lt_trichotomy x 1 with hl | rfl | hg
  · exact ⟨x⁻¹, inv_mem hxΓ', by simpa, one_lt_inv'.mpr hl⟩
  · exact absurd (one_mem Δ) hxΔ
  · exact ⟨x, hxΓ', hxΔ, hg⟩

/-- **A subgroup not contained in another is separated from it by an element below `1`**, the
order dual of `Subgroup.not_le_iff_exists_one_lt`. -/
theorem Subgroup.not_le_iff_exists_lt_one : ¬Γ' ≤ Δ ↔ ∃ z ∈ Γ', z ∉ Δ ∧ z < 1 := by
  rw [Subgroup.not_le_iff_exists_one_lt, inv_surjective.exists]
  simp

end
