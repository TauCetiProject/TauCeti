/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

/-!
# Proper fractional ideals of a number-field order

The multiplier ring of a fractional ideal consists of the field elements preserving that ideal
under multiplication. A fractional ideal is proper when its multiplier ring is exactly the order.
An invertible fractional ideal is proper; the converse can fail for non-Gorenstein orders.

This distinction is needed when forming the Picard group from invertible ideals while keeping
noninvertible proper ideals in the ideal class monoid.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- The subring of `K` consisting of elements that preserve a fractional `O`-ideal under
multiplication. -/
def multiplierRing (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Subring K where
  carrier := {x | ∀ y ∈ I, x * y ∈ I}
  zero_mem' := by intro y hy; simpa using I.zero_mem
  one_mem' := by intro y hy; simpa using hy
  add_mem' := by
    intro x z hx hz y hy
    simpa [add_mul] using
      (I : Submodule O.toSubalgebra K).add_mem (hx y hy) (hz y hy)
  mul_mem' := by
    intro x z hx hz y hy
    simpa [mul_assoc] using hx (z * y) (hz y hy)
  neg_mem' := by
    intro x hx y hy
    rw [neg_mul]
    exact (I : Submodule O.toSubalgebra K).neg_mem (hx y hy)

/-- Membership in the multiplier ring means preservation of every element of the ideal. -/
@[simp]
theorem mem_multiplierRing_iff (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (x : K) :
    x ∈ O.multiplierRing I ↔ ∀ y ∈ I, x * y ∈ I := Iff.rfl

/-- The order acts on each of its fractional ideals, so it lies in the multiplier ring. -/
theorem order_le_multiplierRing (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    O.toSubalgebra.toSubring ≤ O.multiplierRing I := by
  intro x hx y hy
  let a : O.toSubalgebra := ⟨x, hx⟩
  have h := (I : Submodule O.toSubalgebra K).smul_mem a hy
  simpa [a, Algebra.smul_def] using h

/-- An element preserving `I` also preserves every product `I * J`. -/
theorem multiplierRing_le_multiplierRing_mul
    (I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    O.multiplierRing I ≤ O.multiplierRing (I * J) := by
  intro x hx
  rw [O.mem_multiplierRing_iff] at hx ⊢
  intro z hz
  refine FractionalIdeal.mul_induction_on (C := fun z => x * z ∈ I * J) hz ?_ ?_
  · intro i hi j hj
    simpa [mul_assoc] using FractionalIdeal.mul_mem_mul (hx i hi) hj
  · intro a b ha hb
    rw [mul_add]
    exact (I * J : FractionalIdeal _ K).val.add_mem ha hb

/-- A fractional ideal is proper when its multiplier ring equals the order. -/
def IsProperFractionalIdeal (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Prop :=
  O.multiplierRing I = O.toSubalgebra.toSubring

/-- Properness says exactly that any field element stabilizing the ideal belongs to the order. -/
theorem isProperFractionalIdeal_iff (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    O.IsProperFractionalIdeal I ↔
      ∀ x : K, (∀ y ∈ I, x * y ∈ I) → x ∈ O.toSubalgebra := by
  unfold IsProperFractionalIdeal
  constructor
  · intro h x hx
    have hx' : x ∈ O.multiplierRing I := (O.mem_multiplierRing_iff I x).mpr hx
    rwa [h] at hx'
  · intro h
    exact le_antisymm (fun x hx => h x hx) (O.order_le_multiplierRing I)

/-- The unit fractional ideal has precisely the order as its multiplier ring. -/
@[simp]
theorem isProperFractionalIdeal_one :
    O.IsProperFractionalIdeal (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
  rw [O.isProperFractionalIdeal_iff]
  intro x hx
  have h := hx 1 (FractionalIdeal.one_mem_one (nonZeroDivisors O.toSubalgebra))
  have hx1 : x ∈ (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
    simpa using h
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors O.toSubalgebra)).mp
    hx1
  -- The algebra map from the order to its fraction field is its subtype inclusion.
  change (a : K) = x at ha
  exact ha ▸ a.property

/-- Every invertible fractional ideal is proper. -/
theorem isProperFractionalIdeal_of_mul_eq_one
    {I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hIJ : I * J = 1) :
    O.IsProperFractionalIdeal I := by
  apply le_antisymm ?_ (O.order_le_multiplierRing I)
  calc
    O.multiplierRing I ≤ O.multiplierRing (I * J) := O.multiplierRing_le_multiplierRing_mul I J
    _ = O.multiplierRing 1 := by rw [hIJ]
    _ = O.toSubalgebra.toSubring := O.isProperFractionalIdeal_one

/-- Units of the fractional-ideal monoid, namely invertible fractional ideals, are proper. -/
theorem isProperFractionalIdeal_of_isUnit
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : IsUnit I) :
    O.IsProperFractionalIdeal I := by
  obtain ⟨J, hIJ⟩ := isUnit_iff_exists_inv.mp hI
  exact O.isProperFractionalIdeal_of_mul_eq_one hIJ

end NumberFieldOrder

end TauCeti.GlobalNumberFields
