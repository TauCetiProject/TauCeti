/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.GroupTheory.Submonoid.Centralizer

/-!
# Units in submonoids of groups

An element of a submonoid of a group is a unit in that submonoid exactly when its inverse
also lies in the submonoid. The additive version characterizes additive units by negation.
In any monoid, a unit lies in the units of a centralizer exactly when it lies in the centralizer.
-/

public section

namespace Submonoid

/-- An element of a submonoid of a group is a unit precisely when its inverse belongs to it. -/
@[to_additive
/-- An element of an additive submonoid of a group is an additive unit precisely when its
negative belongs to it. -/]
theorem isUnit_iff_inv_mem {G : Type*} [Group G] {S : Submonoid G} (a : S) :
    IsUnit a ↔ (a : G)⁻¹ ∈ S := by
  rw [isUnit_iff_exists]
  constructor
  · rintro ⟨b, hab, -⟩
    have hab' : (a : G) * (b : G) = 1 := congrArg Subtype.val hab
    exact (eq_inv_of_mul_eq_one_right hab') ▸ b.property
  · intro ha
    exact ⟨⟨(a : G)⁻¹, ha⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩

section Centralizer

variable {M : Type*} [Monoid M]

/-- A unit lies in the units of the centralizer of a set exactly when it lies in the centralizer:
its inverse then commutes with the set too. -/
@[to_additive
/-- An additive unit lies in the additive units of the centralizer of a set exactly when it lies
in the centralizer: its negative then commutes with the set too. -/]
theorem mem_units_centralizer_iff {S : Set M} {g : Mˣ} :
    g ∈ (centralizer S).units ↔ (g : M) ∈ centralizer S := by
  rw [mem_units_iff, and_iff_left_iff_imp]
  exact fun h s hs ↦ Commute.units_inv_right (h s hs)

/-- A unit lies in the units of the centralizer of `{z}` exactly when it commutes with `z`. -/
@[to_additive
/-- An additive unit lies in the additive units of the centralizer of `{z}` exactly when it
commutes with `z`. -/]
theorem mem_units_centralizer_singleton_iff {z : M} {g : Mˣ} :
    g ∈ (centralizer {z}).units ↔ Commute (g : M) z := by
  simp only [mem_units_centralizer_iff, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact ⟨Eq.symm, Eq.symm⟩

end Centralizer

end Submonoid
