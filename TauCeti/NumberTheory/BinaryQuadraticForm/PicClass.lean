/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change
public import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Positive definite form classes and the Picard group

Primitive positive definite forms of discriminant `-D` inherit the existing left action
on `posDef D`. Their invertible form ideals define classes through the order's native
`mkPic`. The ideal comparison under a proper change of variables proves invariance and
descends the construction to proper classes. This is the negative-discriminant map in
the form-ideal correspondence; its bijectivity is a separate theorem.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section
noncomputable section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- Primitive forms in the existing positive definite sub-action. -/
def primitivePosDef (D : ℕ) [NeZero D] :
    SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f ∈ posDef D ∧ f.IsPrimitive}
  smul_mem' γ f hf :=
    ⟨(posDef D).smul_mem γ hf.1, (isPrimitive_smul_iff f γ).mpr hf.2⟩

/-- Membership records positive definiteness and primitivity. -/
@[simp] theorem mem_primitivePosDef (D : ℕ) [NeZero D] (f : BinaryQuadraticForm ℤ) :
    f ∈ primitivePosDef D ↔ f ∈ posDef D ∧ f.IsPrimitive := Iff.rfl

/-- A negative nonzero natural discriminant is nonsquare. -/
instance instFactNotIsSquareNegNatCast (D : ℕ) [NeZero D] : Fact (¬ IsSquare (-(D : ℤ))) :=
  ⟨not_isSquare_of_neg (neg_neg_of_pos (by exact_mod_cast NeZero.pos D))⟩

/-- The native Picard class of a primitive positive definite form's ideal. -/
def posDefToPic (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) (f : primitivePosDef D) :
    GlobalNumberFields.Pic (QuadraticOrder.numberFieldOrder (-(D : ℤ)) hD) :=
  (QuadraticOrder.numberFieldOrder (-(D : ℤ)) hD).mkPic
    (f.val.invertibleFractionalIdeal (-(D : ℤ))
      ((mem_posDef.mp ((mem_primitivePosDef D f.val).mp f.property).1).1)
      ((mem_primitivePosDef D f.val).mp f.property).2)

/-- The positive definite map uses the supplier's class of the uncorrected form ideal. -/
theorem posDefToPic_def (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) (f : primitivePosDef D) :
    posDefToPic D hD f = (QuadraticOrder.numberFieldOrder (-(D : ℤ)) hD).mkPic
      (f.val.invertibleFractionalIdeal (-(D : ℤ))
        ((mem_posDef.mp ((mem_primitivePosDef D f.val).mp f.property).1).1)
        ((mem_primitivePosDef D f.val).mp f.property).2) := by
  rfl

/-- A proper change of variables preserves the native Picard class. -/
@[simp] theorem posDefToPic_smul (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) (f : primitivePosDef D)
    (γ : SL(2, ℤ)) : posDefToPic D hD (γ • f) = posDefToPic D hD f := by
  have h := congrArg (QuadraticOrder.numberFieldOrder (-(D : ℤ)) hD).mkPic
    (invertibleFractionalIdeal_smul f.val (-(D : ℤ))
      ((mem_posDef.mp ((mem_primitivePosDef D f.val).mp f.property).1).1)
      ((mem_primitivePosDef D f.val).mp f.property).2 γ)
  simpa only [posDefToPic_def, SubMulAction.val_smul, map_mul,
    ClassGroup.mk_toPrincipalIdeal, one_mul] using h

/-- A positive definite form with leading coefficient one has the principal Picard class. -/
theorem posDefToPic_eq_one_of_a_eq_one (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) (f : primitivePosDef D)
    (ha : f.val.a = 1) : posDefToPic D hD f = 1 := by
  have hf := (mem_posDef.mp ((mem_primitivePosDef D f.val).mp f.property).1).1
  have hp := ((mem_primitivePosDef D f.val).mp f.property).2
  have hI : f.val.invertibleFractionalIdeal (-(D : ℤ)) hf hp = 1 := by
    apply Units.ext
    rw [coe_invertibleFractionalIdeal, Units.val_one]
    apply le_antisymm (fractionalIdeal_le_one f.val (-(D : ℤ)) hf)
    apply FractionalIdeal.one_le.mpr
    simpa only [ha, Int.cast_one] using a_mem_fractionalIdeal f.val (-(D : ℤ)) hf
  rw [posDefToPic_def, hI, map_one]

/-- Proper classes of primitive positive definite forms map to the consumed Picard group. -/
def properClassToPic (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) :
    MulAction.orbitRel.Quotient SL(2, ℤ) (primitivePosDef D) →
      GlobalNumberFields.Pic (QuadraticOrder.numberFieldOrder (-(D : ℤ)) hD) :=
  Quotient.lift (posDefToPic D hD) (by
    intro f g h
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact posDefToPic_smul D hD g γ)

/-- On a proper-class representative, the map is the native class of its form ideal. -/
@[simp] theorem properClassToPic_mk (D : ℕ) [NeZero D]
    (hD : -(D : ℤ) % 4 = 0 ∨ -(D : ℤ) % 4 = 1) (f : primitivePosDef D) :
    properClassToPic D hD (Quotient.mk _ f) = posDefToPic D hD f := by
  rfl

end TauCeti.BinaryQuadraticForm
