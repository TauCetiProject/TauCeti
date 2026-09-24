/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Subword

/-!
# The identity and simple Bruhat cells are disjoint

The nondegeneracy axiom of a Tits system says that a simple reflection does not
normalize the Borel subgroup.  In particular, its double coset cannot meet the
identity double coset.  This file records that first separation result for the
Bruhat cells of a Tits system.

It is the length-zero/one base case for the injectivity part of Bruhat
decomposition: the Weyl-indexed cell at a simple reflection is genuinely a new
cell, rather than another presentation of `B`.

## Main declarations

* `TauCeti.TitsSystem.exists_mem_bruhatCell` gives a representative in every
  Weyl-indexed Bruhat cell.
* `TauCeti.TitsSystem.bruhatCell_one_disjoint_bruhatCell_of_mem_simple` proves
  that the identity cell and a simple cell are disjoint.
* `TauCeti.TitsSystem.bruhatCell_ne_one_of_mem_simple` is the corresponding
  non-equality of cells.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1--29.2.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- Every Weyl-indexed Bruhat cell contains a representative from the normalizer subgroup. -/
theorem exists_mem_bruhatCell (w : T.WeylGroup) :
    ∃ n : T.subgroupN, QuotientGroup.mk n = w ∧ (n : G) ∈ T.bruhatCell w := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective T.intersection w
  refine ⟨n, hn, ?_⟩
  rw [← hn, QuotientGroup.mk'_apply, T.bruhatCell_mk]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- The identity Bruhat cell is disjoint from every simple Bruhat cell.

Indeed, an intersection would identify the double coset of a simple representative with `B`.
The representative would then belong to `B ∩ N`, so its Weyl-group class would be the identity,
contradicting `TitsSystem.simple_ne_one`. -/
theorem bruhatCell_one_disjoint_bruhatCell_of_mem_simple {s : T.WeylGroup}
    (hs : s ∈ T.simple) : Disjoint (T.bruhatCell 1) (T.bruhatCell s) := by
  obtain ⟨r, hr, _⟩ := T.exists_mem_bruhatCell s
  rw [Set.disjoint_left]
  intro x hxone hxs
  rw [T.bruhatCell_one] at hxone
  rw [← hr, T.bruhatCell_mk] at hxs
  obtain ⟨b₁, hb₁, b₂, hb₂, hxs⟩ := DoubleCoset.mem_doubleCoset.mp hxs
  have hrB : (r : G) ∈ T.subgroupB := by
    have hr_eq : (r : G) = (b₁ : G)⁻¹ * x * (b₂ : G)⁻¹ := by
      rw [hxs]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
    rw [hr_eq]
    exact T.subgroupB.mul_mem
      (T.subgroupB.mul_mem (T.subgroupB.inv_mem hb₁) hxone)
      (T.subgroupB.inv_mem hb₂)
  have hrinter : r ∈ T.intersection := T.mem_intersection r |>.mpr hrB
  have hsone : s = 1 := by
    rw [← hr]
    exact (QuotientGroup.eq_one_iff r).mpr hrinter
  exact (T.simple_ne_one hs) hsone

/-- A simple Bruhat cell is not the identity Bruhat cell. -/
theorem bruhatCell_ne_one_of_mem_simple {s : T.WeylGroup} (hs : s ∈ T.simple) :
    T.bruhatCell s ≠ T.bruhatCell 1 := by
  intro h
  have hdisjoint := T.bruhatCell_one_disjoint_bruhatCell_of_mem_simple hs
  obtain ⟨r, _, hrmem⟩ := T.exists_mem_bruhatCell s
  have hrone : (r : G) ∈ T.bruhatCell 1 := h ▸ hrmem
  exact (Set.disjoint_left.mp hdisjoint) hrone hrmem

end TauCeti.TitsSystem
