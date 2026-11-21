/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Basic identities for special unitary matrices

For a unitary matrix the conjugate transpose is a right inverse, so the adjugate is the
determinant times the conjugate transpose (`Matrix.adjugate_eq_det_smul_of_mul_eq_one`). For a
special unitary matrix the two agree. This turns `star` on `Matrix.specialUnitaryGroup n α` into a
polynomial expression in the entries, which is what makes the small special unitary groups
computable by hand.

We also record the equivalence between the group commutator equation `⁅A, B⁆ = c • 1` in `SU(n, α)`
and the Weyl commutation relation `A * B = c • (B * A)`.

## Main results

* `Matrix.specialUnitaryGroup.star_eq_adjugate`: the conjugate transpose of a special
  unitary matrix is its adjugate.
* `Matrix.specialUnitaryGroup.commutatorElement_eq_smul_one_iff`: in `SU(n, α)`, the group
  commutator relation `⁅A, B⁆ = c • 1` is equivalent to the Weyl relation `A * B = c • (B * A)`.
-/

public section

open scoped commutatorElement

namespace Matrix.specialUnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

/-- The conjugate transpose of a special unitary matrix is its adjugate: it is the inverse, and
for determinant one the inverse is the adjugate. -/
theorem star_eq_adjugate (g : specialUnitaryGroup n α) :
    star (g : Matrix n n α) = (g : Matrix n n α).adjugate := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.property
  rw [adjugate_eq_det_smul_of_mul_eq_one (mem_unitaryGroup_iff.mp hU), hdet, one_smul]

/-- In `SU(n, α)`, the group-commutator equation `⁅A, B⁆ = c • 1` is equivalent to the Weyl
commutation relation `A * B = c • (B * A)`. -/
theorem commutatorElement_eq_smul_one_iff {A B : specialUnitaryGroup n α} {c : α} :
    ((⁅A, B⁆ : specialUnitaryGroup n α) : Matrix n n α) = c • (1 : Matrix n n α) ↔
      (A : Matrix n n α) * (B : Matrix n n α) =
        c • ((B : Matrix n n α) * (A : Matrix n n α)) := by
  constructor
  · intro h
    have hmul : ⁅A, B⁆ * (B * A) = A * B := by
      rw [commutatorElement_def, mul_assoc (A * B * A⁻¹), inv_mul_cancel_left, inv_mul_cancel_right]
    have hcoe := congrArg Subtype.val hmul
    simpa [Submonoid.coe_mul, h, Matrix.smul_mul] using hcoe.symm
  · intro h
    have hmul : ⁅A, B⁆ = (A * B) * (A⁻¹ * B⁻¹) := by
      rw [commutatorElement_def, mul_assoc (A * B)]
    have hcancel : (B * A) * (A⁻¹ * B⁻¹) = 1 := by
      rw [mul_assoc B A, mul_inv_cancel_left, mul_inv_cancel]
    have hcoe := congrArg Subtype.val hmul
    have hcancel_coe : (((B * A) * (A⁻¹ * B⁻¹) : specialUnitaryGroup n α) : Matrix n n α) = 1 :=
      congrArg Subtype.val hcancel
    rw [hcoe, Submonoid.coe_mul, Submonoid.coe_mul, h, Matrix.smul_mul, ← Submonoid.coe_mul,
      ← Submonoid.coe_mul, hcancel_coe]

end Matrix.specialUnitaryGroup
