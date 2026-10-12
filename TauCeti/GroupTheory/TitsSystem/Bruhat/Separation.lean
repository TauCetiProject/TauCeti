/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Basic

/-!
# The identity Bruhat cell is disjoint from the other cells

The Weyl group of a Tits system is `N / (B ∩ N)`, so a representative in `N` lying in `B`
represents the identity.  Consequently the identity double coset `B` cannot meet the Bruhat cell
of any nonidentity Weyl element.  This file records that first separation result for the
Bruhat cells of a Tits system.

In particular, by `TauCeti.TitsSystem.simple_ne_one`, it is the length-zero/one base case for the
injectivity part of Bruhat decomposition: the Weyl-indexed cell at a simple reflection is
genuinely a new cell, rather than another presentation of `B`.

## Main declarations

* `TauCeti.TitsSystem.bruhatCell_one_disjoint_bruhatCell` proves that the identity cell and the
  cell of a nonidentity Weyl element are disjoint.
* `TauCeti.TitsSystem.bruhatCell_ne_bruhatCell_one` is the corresponding non-equality of cells.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1--29.2.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The identity Bruhat cell is disjoint from the Bruhat cell of every nonidentity Weyl
element. -/
theorem bruhatCell_one_disjoint_bruhatCell {w : T.WeylGroup} (hw : w ≠ 1) :
    Disjoint (T.bruhatCell 1) (T.bruhatCell w) := by
  obtain ⟨r, hr, _⟩ := T.exists_mem_bruhatCell w
  rw [Set.disjoint_left]
  intro x hxone hxw
  rw [T.bruhatCell_one] at hxone
  rw [← hr, T.bruhatCell_mk] at hxw
  have hnot : ¬ Disjoint
      (DoubleCoset.doubleCoset (1 : G) T.subgroupB T.subgroupB)
      (DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB) := by
    rw [Set.not_disjoint_iff]
    exact ⟨x, by simpa only [doubleCoset_one_self] using hxone, hxw⟩
  have hrB : (r : G) ∈ T.subgroupB := by
    simpa only [doubleCoset_one_self, SetLike.mem_coe] using
      (DoubleCoset.mem_doubleCoset_of_not_disjoint hnot)
  have hrinter : r ∈ T.intersection := T.mem_intersection r |>.mpr hrB
  apply hw
  rw [← hr]
  exact (QuotientGroup.eq_one_iff r).mpr hrinter

/-- The Bruhat cell of a nonidentity Weyl element is not the identity Bruhat cell. -/
theorem bruhatCell_ne_bruhatCell_one {w : T.WeylGroup} (hw : w ≠ 1) :
    T.bruhatCell w ≠ T.bruhatCell 1 := by
  intro h
  have hdisjoint := T.bruhatCell_one_disjoint_bruhatCell hw
  obtain ⟨r, _, hrmem⟩ := T.exists_mem_bruhatCell w
  have hrone : (r : G) ∈ T.bruhatCell 1 := h ▸ hrmem
  exact (Set.disjoint_left.mp hdisjoint) hrone hrmem

end TauCeti.TitsSystem
