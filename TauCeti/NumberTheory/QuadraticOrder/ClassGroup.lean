/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticOrder.Field
public import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
public import TauCeti.NumberTheory.ClassGroup.Equiv

/-!
# The Picard group of a fundamental quadratic order

For a fundamental discriminant `D`, the quadratic order `ℤ[(D + √D)/2]` of the model `ℚ(√D)` is
its ring of integers (`TauCeti.QuadraticOrder.toSubalgebra_eq_integralClosure_iff`). This file
turns that equality of subrings into a ring equivalence with `𝓞 ℚ(√D)` and, through Mathlib's
`ClassGroup.mulEquiv`, identifies the Picard group of the order with the ideal class group of
`ℚ(√D)`. This is the conductor-one case of the comparison between Picard groups of quadratic
orders and class groups, through which counts of forms of fundamental discriminant become class
numbers.

## Main definitions and results

* `TauCeti.QuadraticOrder.ringEquivRingOfIntegers`: for fundamental `D`, the order of
  discriminant `D` is the ring of integers of `ℚ(√D)`.
* `TauCeti.QuadraticOrder.picEquivClassGroup`: for fundamental `D`, the Picard group of the order
  of discriminant `D` is the class group of `𝓞 ℚ(√D)`, and `picEquivClassGroup_mkPic` computes it
  on Picard classes of invertible fractional ideals.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open scoped NumberField

namespace TauCeti.QuadraticOrder

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)]

/-- **At a fundamental discriminant the quadratic order is the ring of integers.** For a
fundamental discriminant `D`, the order `ℤ[(D + √D)/2]` of `ℚ(√D)` and `𝓞 ℚ(√D)` are the same
subring of `ℚ(√D)`. -/
noncomputable def ringEquivRingOfIntegers (hfund : Int.IsFundamentalDiscr D) :
    (numberFieldOrder D hD).toSubalgebra ≃+* 𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0) :=
  (Subalgebra.equivOfEq _ _ <| (numberFieldOrder_toSubalgebra D hD).trans <|
    (toSubalgebra_eq_integralClosure_iff D hD).mpr hfund).toRingEquiv

/-- The identification of the order with the ring of integers is compatible with the inclusions
into `ℚ(√D)`. -/
@[simp] theorem algebraMap_ringEquivRingOfIntegers (hfund : Int.IsFundamentalDiscr D)
    (x : (numberFieldOrder D hD).toSubalgebra) :
    algebraMap (𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0)) (QuadraticAlgebra ℚ (D : ℚ) 0)
      (ringEquivRingOfIntegers D hD hfund x) = algebraMap _ _ x := (rfl)

/-- **At a fundamental discriminant the Picard group is the class group.** For a fundamental
discriminant `D`, the Picard group of the order of discriminant `D` is the ideal class group of
`𝓞 ℚ(√D)`, via Mathlib's `ClassGroup.mulEquiv` for `ringEquivRingOfIntegers`. -/
noncomputable def picEquivClassGroup (hfund : Int.IsFundamentalDiscr D) :
    GlobalNumberFields.Pic (numberFieldOrder D hD) ≃*
      ClassGroup (𝓞 (QuadraticAlgebra ℚ (D : ℚ) 0)) :=
  ClassGroup.mulEquiv (ringEquivRingOfIntegers D hD hfund)

/-- `picEquivClassGroup` sends the Picard class of an invertible fractional ideal of the order to
the ideal class of its transport along `ringEquivRingOfIntegers`. -/
@[simp] theorem picEquivClassGroup_mkPic (hfund : Int.IsFundamentalDiscr D)
    (I : (numberFieldOrder D hD).invertibleProperFractionalIdeals) :
    picEquivClassGroup D hD hfund ((numberFieldOrder D hD).mkPic I) =
      ClassGroup.mk (QuadraticAlgebra ℚ (D : ℚ) 0)
        (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv _ _
          (ringEquivRingOfIntegers D hD hfund)).toMulEquiv I) :=
  ClassGroup.mulEquiv_mk _ _ I

end TauCeti.QuadraticOrder
