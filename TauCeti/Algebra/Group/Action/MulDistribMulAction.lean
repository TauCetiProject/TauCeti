/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Multiplicative distributive actions on monoids

A multiplicative distributive action of `G` on a monoid `A`, such as a `MulSemiringAction`, has
`g • (a * b) = g • a * g • b`. Read with `A` acting on itself by left multiplication, this is
`SMulDistribClass G A A`, the form taken by statements about semilinear actions on `A`-modules
when the module is `A` itself. Moreover, because two-sided inverses in a monoid are unique, any
`g : G` fixing a unit also fixes its inverse, so inclusion `FixedPoints.submonoid G B →* B`
reflects and preserves units.

## Main results

* `TauCeti.smulDistribClass_self`: `SMulDistribClass G A A` for a `MulDistribMulAction G A`.
* `TauCeti.smul_val_inv_eq_of_smul_eq`: if `g` fixes a unit `u`, then `g` fixes `u⁻¹`.
* `TauCeti.isUnit_coe_fixedPoints_submonoid_iff`: inclusion `FixedPoints.submonoid G B →* B`
  reflects and preserves units.
-/

public section

namespace TauCeti

/-- A multiplicative distributive action of `G` on a monoid `A` distributes over the action of `A`
on itself by left multiplication. -/
instance smulDistribClass_self (G A : Type*) [Monoid G] [Monoid A] [MulDistribMulAction G A] :
    SMulDistribClass G A A :=
  ⟨smul_mul'⟩

/-- If `g` fixes a unit `u : Bˣ` under a multiplicative action, `g` also fixes `u⁻¹`. -/
theorem smul_val_inv_eq_of_smul_eq {B G : Type*} [Monoid B] [Monoid G] [MulDistribMulAction G B]
    {u : Bˣ} {g : G} (hu : g • (u : B) = u) : g • (↑u⁻¹ : B) = ↑u⁻¹ :=
  Units.mul_eq_one_iff_eq_inv.mp <| by rw [← hu, ← smul_mul', Units.inv_mul, smul_one]

/-- Inclusion `FixedPoints.submonoid G B →* B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_submonoid_iff {B G : Type*} [Monoid B] [Monoid G]
    [MulDistribMulAction G B] {x : FixedPoints.submonoid G B} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun ⟨u, hu⟩ ↦ ⟨⟨x, ⟨↑u⁻¹, fun g ↦ smul_val_inv_eq_of_smul_eq (hu ▸ x.property g)⟩,
    Subtype.ext (by simp [← hu]), Subtype.ext (by simp [← hu])⟩, rfl⟩,
   fun ⟨u, hu⟩ ↦ ⟨⟨u.val, u.inv, congrArg Subtype.val u.val_inv, congrArg Subtype.val u.inv_val⟩,
    hu ▸ rfl⟩⟩

end TauCeti
