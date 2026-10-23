/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Separation

/-!
# Uniqueness in Bruhat decomposition

The Bruhat cells of a Tits system are indexed injectively by its Weyl group. Together with
the covering theorem, this gives the disjoint decomposition `G = ⨆ w ∈ W, B w B`: every
element belongs to exactly one Weyl-indexed cell. Consequently containment of cells is equality
of their indices, and a cell contained in a union of two cells is one of the two.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1--29.2.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- Distinct Weyl elements index distinct Bruhat cells. -/
theorem bruhatCell_injective : Function.Injective T.bruhatCell := by
  have step {s w : T.WeylGroup} (hs : s ∈ T.simple)
      (ih : ∀ v, T.bruhatCell w = T.bruhatCell v → w = v) :
      ∀ v, T.bruhatCell (s * w) = T.bruhatCell v → s * w = v := by
    intro v h
    obtain ⟨n, _, hn⟩ := T.exists_mem_bruhatCell w
    have hnprod : (n : G) ∈ T.bruhatCell s * T.bruhatCell (s * w) := by
      rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs (s * w) with hmul | hmul
      · simpa only [hmul, ← mul_assoc, T.simple_sq_eq_one hs, one_mul] using hn
      · rw [hmul, ← mul_assoc, T.simple_sq_eq_one hs, one_mul]
        exact Or.inl hn
    rw [h] at hnprod
    have hnunion : (n : G) ∈ T.bruhatCell (s * v) ∪ T.bruhatCell v := by
      rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs v with hmul | hmul
      · exact Or.inl (hmul ▸ hnprod)
      · exact hmul ▸ hnprod
    rcases hnunion with hnv | hnv
    · have hw : w = s * v := ih _
        ((T.bruhatCell_eq_doubleCoset hn).trans (T.bruhatCell_eq_doubleCoset hnv).symm)
      rw [hw, ← mul_assoc, T.simple_sq_eq_one hs, one_mul]
    · have hw : w = v := ih _
        ((T.bruhatCell_eq_doubleCoset hn).trans (T.bruhatCell_eq_doubleCoset hnv).symm)
      have hsw : w = s * w := ih _ (h.trans (congrArg T.bruhatCell hw.symm)).symm
      exact (T.simple_ne_one hs (mul_right_cancel (hsw.symm.trans (one_mul w).symm))).elim
  intro w
  have hw : w ∈ Subgroup.closure T.simple := by simp [T.closure_simple]
  induction hw using Subgroup.closure_induction_left with
  | one =>
      intro v h
      by_contra hv
      exact T.bruhatCell_ne_bruhatCell_one (Ne.symm hv) h.symm
  | mul_left s hs w _ ih => exact step hs ih
  | inv_mul_cancel s hs w _ ih =>
      rw [T.inv_simple hs]
      exact step hs ih

/-- Equality of Bruhat cells is equality of their Weyl indices. -/
@[simp]
theorem bruhatCell_inj {w v : T.WeylGroup} :
    T.bruhatCell w = T.bruhatCell v ↔ w = v :=
  T.bruhatCell_injective.eq_iff

/-- Two cells sharing an element have the same Weyl index. -/
theorem eq_of_mem_bruhatCell_of_mem {g : G} {w v : T.WeylGroup} (hw : g ∈ T.bruhatCell w)
    (hv : g ∈ T.bruhatCell v) : w = v :=
  T.bruhatCell_injective
    ((T.bruhatCell_eq_doubleCoset hw).trans (T.bruhatCell_eq_doubleCoset hv).symm)

/-- Containment of Bruhat cells is equality of their Weyl indices. -/
@[simp]
theorem bruhatCell_subset_iff {w v : T.WeylGroup} :
    T.bruhatCell w ⊆ T.bruhatCell v ↔ w = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ subset_rfl⟩
  obtain ⟨n, _, hn⟩ := T.exists_mem_bruhatCell w
  exact T.eq_of_mem_bruhatCell_of_mem hn (h hn)

/-- A Bruhat cell contained in the union of two cells is one of them. -/
theorem eq_or_eq_of_bruhatCell_subset_union {w u v : T.WeylGroup}
    (h : T.bruhatCell w ⊆ T.bruhatCell u ∪ T.bruhatCell v) : w = u ∨ w = v := by
  obtain ⟨n, _, hn⟩ := T.exists_mem_bruhatCell w
  exact (h hn).imp (T.eq_of_mem_bruhatCell_of_mem hn) (T.eq_of_mem_bruhatCell_of_mem hn)

/-- Two Bruhat cells are disjoint exactly when their Weyl indices differ. -/
@[simp]
theorem disjoint_bruhatCell_iff {w v : T.WeylGroup} :
    Disjoint (T.bruhatCell w) (T.bruhatCell v) ↔ w ≠ v := by
  constructor
  · rintro h rfl
    obtain ⟨n, _, hn⟩ := T.exists_mem_bruhatCell w
    exact Set.disjoint_left.mp h hn hn
  · intro h
    rw [Set.disjoint_left]
    intro g hw hv
    exact h (T.eq_of_mem_bruhatCell_of_mem hw hv)

/-- **Bruhat decomposition:** every group element belongs to a unique Weyl-indexed cell. -/
theorem existsUnique_mem_bruhatCell (g : G) :
    ∃! w : T.WeylGroup, g ∈ T.bruhatCell w := by
  obtain ⟨n, hn⟩ := T.exists_mem_doubleCoset g
  have hn' : g ∈ T.bruhatCell (QuotientGroup.mk n) := by
    simpa only [T.bruhatCell_mk] using hn
  exact ⟨QuotientGroup.mk n, hn', fun w hw ↦ T.eq_of_mem_bruhatCell_of_mem hw hn'⟩

end TauCeti.TitsSystem
