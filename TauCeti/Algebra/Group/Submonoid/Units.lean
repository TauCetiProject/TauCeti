/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units

/-!
# Units in submonoids of groups

An element of a submonoid of a group is a unit in that submonoid exactly when its inverse
also lies in the submonoid. The additive version characterizes additive units by negation.
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

end Submonoid
