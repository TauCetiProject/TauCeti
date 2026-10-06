/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
import TauCeti.RingTheory.FractionalIdeal.Operations

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
  carrier := (I : Submodule O.toSubalgebra K) / (I : Submodule O.toSubalgebra K)
  zero_mem' := Submodule.zero_mem _
  one_mem' := by intro y hy; simpa using hy
  add_mem' := Submodule.add_mem _
  mul_mem' := by
    intro x z hx hz y hy
    simpa [mul_assoc] using hx (z * y) (hz y hy)
  neg_mem' := Submodule.neg_mem _

/-- Membership in the multiplier ring means preservation of every element of the ideal. -/
@[simp]
theorem mem_multiplierRing_iff (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (x : K) :
    x ∈ O.multiplierRing I ↔ ∀ y ∈ I, x * y ∈ I :=
  Submodule.mem_div_iff_forall_mul_mem

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

/-- Multiplication by an invertible fractional ideal preserves the multiplier ring. -/
@[simp]
theorem multiplierRing_mul_isUnit
    (I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hJ : IsUnit J) :
    O.multiplierRing (I * J) = O.multiplierRing I := by
  obtain ⟨J', hJJ'⟩ := isUnit_iff_exists_inv.mp hJ
  apply le_antisymm ?_ (O.multiplierRing_le_multiplierRing_mul I J)
  have h := O.multiplierRing_le_multiplierRing_mul (I * J) J'
  simpa [mul_assoc, hJJ'] using h

/-- Scaling a fractional ideal by a nonzero field element preserves its multiplier ring. -/
@[simp]
theorem multiplierRing_mul_spanSingleton
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) {x : K} (hx : x ≠ 0) :
    O.multiplierRing (I * FractionalIdeal.spanSingleton _ x) = O.multiplierRing I := by
  exact O.multiplierRing_mul_isUnit I _
    (FractionalIdeal.isUnit_spanSingleton (isUnit_iff_ne_zero.mpr hx))

/-- A fractional ideal is proper when its multiplier ring equals the order. -/
def IsProperFractionalIdeal (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Prop :=
  O.multiplierRing I = O.toSubalgebra.toSubring

/-- Properness is equality of the multiplier ring with the order. -/
theorem isProperFractionalIdeal_def (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    O.IsProperFractionalIdeal I ↔ O.multiplierRing I = O.toSubalgebra.toSubring :=
  Iff.rfl

/-- Every field element preserves the zero ideal, so its multiplier ring is the whole field. -/
@[simp]
theorem multiplierRing_zero : O.multiplierRing 0 = ⊤ := by
  ext x
  simp

section

variable {O}

/-- A proper fractional ideal is nonzero, so proper ideals enter the monoid of nonzero fractional
ideals without a separate nonvanishing hypothesis. -/
theorem IsProperFractionalIdeal.ne_zero {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (hI : O.IsProperFractionalIdeal I) : I ≠ 0 := by
  rintro rfl
  rw [O.isProperFractionalIdeal_def, multiplierRing_zero] at hI
  exact O.toSubalgebra_ne_top (Algebra.toSubring_eq_top.mp hI.symm)

end

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

/-- Properness is unchanged by multiplication by an invertible fractional ideal. -/
@[simp]
theorem isProperFractionalIdeal_mul_isUnit
    (I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hJ : IsUnit J) :
    O.IsProperFractionalIdeal (I * J) ↔ O.IsProperFractionalIdeal I := by
  simp only [IsProperFractionalIdeal, O.multiplierRing_mul_isUnit I J hJ]

/-- Properness is unchanged by nonzero principal scaling. -/
@[simp]
theorem isProperFractionalIdeal_mul_spanSingleton
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) {x : K} (hx : x ≠ 0) :
    O.IsProperFractionalIdeal (I * FractionalIdeal.spanSingleton _ x) ↔
      O.IsProperFractionalIdeal I := by
  simp only [IsProperFractionalIdeal, O.multiplierRing_mul_spanSingleton I hx]

/-- The unit fractional ideal has precisely the order as its multiplier ring. -/
@[simp]
theorem multiplierRing_one :
    O.multiplierRing (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) =
      O.toSubalgebra.toSubring := by
  apply le_antisymm ?_ (O.order_le_multiplierRing 1)
  intro x hx
  rw [O.mem_multiplierRing_iff] at hx
  have h := hx 1 (FractionalIdeal.one_mem_one (nonZeroDivisors O.toSubalgebra))
  have hx1 : x ∈ (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
    simpa using h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors O.toSubalgebra)).mp hx1
  exact a.property

/-- The unit fractional ideal is proper. -/
@[simp]
theorem isProperFractionalIdeal_one :
    O.IsProperFractionalIdeal (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :=
  O.multiplierRing_one

/-- Units of the fractional-ideal monoid, namely invertible fractional ideals, are proper. -/
theorem isProperFractionalIdeal_of_isUnit
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : IsUnit I) :
    O.IsProperFractionalIdeal I := by
  simpa only [one_mul] using
    (O.isProperFractionalIdeal_mul_isUnit 1 I hI).mpr O.isProperFractionalIdeal_one

/-- The group of invertible fractional ideals of an order. Its elements are proper fractional
ideals, by `NumberFieldOrder.isProperFractionalIdeal_of_isUnit`. -/
abbrev invertibleProperFractionalIdeals (O : NumberFieldOrder K) :=
  (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ

/-- The proper fractional ideals of an order. Every invertible fractional ideal is proper, but for
a non-Gorenstein order some proper fractional ideals are not invertible, so this carrier is larger
than `NumberFieldOrder.invertibleProperFractionalIdeals`. -/
abbrev properFractionalIdeals (O : NumberFieldOrder K) :=
  {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K // O.IsProperFractionalIdeal I}

/-- Every invertible fractional ideal of an order is proper. -/
theorem invertible_isProper (I : O.invertibleProperFractionalIdeals) :
    O.IsProperFractionalIdeal I :=
  O.isProperFractionalIdeal_of_isUnit I.isUnit

/-- A fractional ideal with a multiplicative inverse is proper. -/
theorem isProperFractionalIdeal_of_mul_eq_one
    {I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hIJ : I * J = 1) :
    O.IsProperFractionalIdeal I :=
  O.isProperFractionalIdeal_of_isUnit (IsUnit.of_mul_eq_one J hIJ)

end NumberFieldOrder

end TauCeti.GlobalNumberFields
