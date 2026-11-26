/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Group.Action.Basic

/-!
# `Ring.inverse` and actions of groups with zero

When a group with zero `G₀` acts on a monoid with zero `M₀` compatibly with left and right
multiplication, scaling an element by `c : G₀` scales its totalized inverse `Ring.inverse` by `c⁻¹`
(`TauCeti.ringInverse_smul`), including at `c = 0` and at nonunits where both sides vanish.
-/

public section

namespace TauCeti

/-- Scaling an element of a monoid with zero by a scalar from a group with zero scales its
`Ring.inverse` by the inverse scalar. Both sides vanish when `c = 0` or `a` is not a unit. -/
@[simp, grind =]
theorem ringInverse_smul {G₀ M₀ : Type*} [GroupWithZero G₀] [MonoidWithZero M₀]
    [MulActionWithZero G₀ M₀] [IsScalarTower G₀ M₀ M₀] [SMulCommClass G₀ M₀ M₀]
    (c : G₀) (a : M₀) : Ring.inverse (c • a) = c⁻¹ • Ring.inverse a := by
  rcases GroupWithZero.eq_zero_or_unit c with rfl | ⟨c, rfl⟩
  · simp
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simpa [Units.smul_def, Units.smul_inv, Ring.inverse_unit] using Ring.inverse_unit (c • u)
  · have hca : ¬IsUnit ((c : G₀) • a) := by rwa [← Units.smul_def, isUnit_smul_iff]
    simp [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ hca]

end TauCeti
