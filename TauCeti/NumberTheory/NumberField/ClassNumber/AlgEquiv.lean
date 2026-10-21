/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# The class number is an isomorphism invariant of number fields

A field isomorphism over `ℚ` between two number fields identifies their rings of integers, and
a ring isomorphism of Dedekind domains identifies their class groups. This file uses those two
existing isomorphisms — `NumberField.RingOfIntegers.mapRingEquiv` and `ClassGroup.mulEquiv` — to
show that the class number, the cardinality of the class group, is preserved by
`K ≃ₐ[ℚ] L`. The transport therefore arises from the actual maps on rings of integers and ideal
classes, not from any abstract argument about cardinalities.

## Main results

* `AlgEquiv.classNumber_eq`: a field isomorphism `e : K ≃ₐ[ℚ] L` induces an isomorphism of the
  class groups of `K` and `L`, so `NumberField.classNumber K = NumberField.classNumber L`.
-/

public section

open NumberField

/-! Isomorphic number fields have the same class number: the isomorphism of rings of integers
induces an isomorphism of class groups, and isomorphic finite groups have the same cardinality. -/
theorem AlgEquiv.classNumber_eq {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) : NumberField.classNumber K = NumberField.classNumber L := by
  rw [NumberField.classNumber, NumberField.classNumber]
  exact Fintype.card_congr
    (ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)).toEquiv
