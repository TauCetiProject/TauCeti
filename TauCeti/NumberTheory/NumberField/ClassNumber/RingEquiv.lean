/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# The class group and class number are isomorphism invariants of number fields

A ring isomorphism `e : K ≃+* L` between two fields identifies their rings of integers,
and a ring isomorphism of Dedekind domains identifies their class groups. This file combines those
two existing isomorphisms — `NumberField.RingOfIntegers.mapRingEquiv` and `ClassGroup.mulEquiv` —
to produce the isomorphism of the class groups, from which the equality of the class numbers of
number fields follows.

## Main results

* `RingEquiv.classGroupEquiv`: a ring isomorphism `e : K ≃+* L` induces an isomorphism of the
  class groups of the rings of integers of `K` and `L`.
* `RingEquiv.classNumber_eq`: as a consequence, `NumberField.classNumber K =
  NumberField.classNumber L`.
-/

public section

open NumberField
open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [Field L]

/-- A ring isomorphism `e : K ≃+* L` between fields induces an isomorphism between the class
groups of their rings of integers. -/
noncomputable def RingEquiv.classGroupEquiv (e : K ≃+* L) :
    ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L) :=
  ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv e)

/-- The class-group isomorphism is the one induced by the ring isomorphism of the rings of
integers. -/
theorem RingEquiv.classGroupEquiv_eq (e : K ≃+* L) :
    e.classGroupEquiv = ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv e) := (rfl)

/-- The class-group isomorphism sends the class of a non-zero ideal to the class of its image
under the induced ring isomorphism. -/
@[simp]
theorem RingEquiv.classGroupEquiv_mk0 [IsDedekindDomain (𝓞 K)] [IsDedekindDomain (𝓞 L)]
    (e : K ≃+* L) (I : (Ideal (𝓞 K))⁰) :
    e.classGroupEquiv (ClassGroup.mk0 I) =
      ClassGroup.mk0
        ⟨I.1.map (NumberField.RingOfIntegers.mapRingEquiv e),
          mem_nonZeroDivisors_iff_ne_zero.mpr <|
            (Ideal.map_eq_bot_iff_of_injective
              (NumberField.RingOfIntegers.mapRingEquiv e).injective).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ :=
  ClassGroup.mulEquiv_mk0 (NumberField.RingOfIntegers.mapRingEquiv e) I

/-- Isomorphic number fields have the same class number: if `e : K ≃+* L`, then
`classNumber K = classNumber L`. -/
theorem RingEquiv.classNumber_eq (e : K ≃+* L) [NumberField K] [NumberField L] :
    classNumber K = classNumber L := by
  rw [classNumber, classNumber]
  exact Fintype.card_congr (RingEquiv.classGroupEquiv e).toEquiv
