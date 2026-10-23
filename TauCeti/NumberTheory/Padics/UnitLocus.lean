/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Division
public import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The clopen unit locus of the p-adic integers

The group `ℤ_pˣ` is homeomorphic, by its value map, to the clopen subset of units in `ℤ_p`.
This identifies intrinsic test functions on the unit group with test functions on that clopen
subset, so they can be extended by zero to `ℤ_p`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3,
  Remark 3.31 and Corollary 3.32.
-/

public noncomputable section

open TopologicalSpace

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The clopen subset of invertible p-adic integers. -/
def unitsClopen : Clopens ℤ_[p] where
  carrier := {x | IsUnit x}
  isClopen' := by
    have h : {x : ℤ_[p] | IsUnit x} = (multiplesClopen p : Set ℤ_[p])ᶜ := by
      ext x
      simp only [Set.mem_ofPred, Set.mem_compl_iff, SetLike.mem_coe, mem_multiplesClopen_iff,
        ← not_isUnit_iff_dvd, not_not]
    rw [h]
    exact (multiplesClopen p).isClopen.compl

/-- Membership in the unit locus is invertibility. -/
@[simp]
theorem mem_unitsClopen {x : ℤ_[p]} : x ∈ unitsClopen p ↔ IsUnit x := Iff.rfl

/-- The value map identifies the p-adic unit group with the clopen unit locus. -/
def unitsHomeomorphIsUnit : ℤ_[p]ˣ ≃ₜ unitsClopen p := by
  let e : ℤ_[p]ˣ ≃ unitsClopen p :=
    { toFun := fun u ↦ ⟨u, u.isUnit⟩
      invFun := fun x ↦ x.property.unit
      left_inv := fun u ↦ Units.val_injective (IsUnit.unit_spec u.isUnit)
      right_inv := fun x ↦ Subtype.ext (IsUnit.unit_spec x.property) }
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (Units.continuous_val.subtype_mk _)

/-- The homeomorphism to the unit locus preserves underlying p-adic values. -/
@[simp]
theorem unitsHomeomorphIsUnit_apply (u : ℤ_[p]ˣ) :
    unitsHomeomorphIsUnit p u = ⟨u, (mem_unitsClopen p).mpr u.isUnit⟩ := (rfl)

/-- The inverse homeomorphism preserves underlying p-adic values. -/
@[simp]
theorem unitsHomeomorphIsUnit_symm_apply (x : unitsClopen p) :
    ((unitsHomeomorphIsUnit p).symm x : ℤ_[p]) = x :=
  IsUnit.unit_spec x.property

end PadicInt
