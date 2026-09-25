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
  obtain ⟨b₁, hb₁, b₂, hb₂, hxw⟩ := DoubleCoset.mem_doubleCoset.mp hxw
  have hrB : (r : G) ∈ T.subgroupB := by
    have hr_eq : (r : G) = (b₁ : G)⁻¹ * x * (b₂ : G)⁻¹ := by
      rw [hxw]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
    rw [hr_eq]
    exact T.subgroupB.mul_mem
      (T.subgroupB.mul_mem (T.subgroupB.inv_mem hb₁) hxone)
      (T.subgroupB.inv_mem hb₂)
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
