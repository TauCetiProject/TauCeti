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
# The class group and class number are isomorphism invariants of number fields

A ring isomorphism `e : K ≃+* L` between two number fields identifies their rings of integers,
and a ring isomorphism of Dedekind domains identifies their class groups. This file combines those
two existing isomorphisms — `NumberField.RingOfIntegers.mapRingEquiv` and `ClassGroup.mulEquiv` —
to produce the isomorphism of the class groups, from which the equality of the class numbers
follows.

## Main results

* `RingEquiv.classGroupEquiv`: a ring isomorphism `e : K ≃+* L` induces an isomorphism of the
  class groups of the rings of integers of `K` and `L`.
* `RingEquiv.classNumber_eq`: as a consequence, `NumberField.classNumber K =
  NumberField.classNumber L`.
-/

public section

open NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- A ring isomorphism `e : K ≃+* L` between number fields induces an isomorphism between the
class groups of their rings of integers. -/
noncomputable def RingEquiv.classGroupEquiv (e : K ≃+* L) :
    ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L) :=
  ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv e)

/-- Isomorphic number fields have the same class number: if `e : K ≃+* L`, then
`classNumber K = classNumber L`. -/
theorem RingEquiv.classNumber_eq (e : K ≃+* L) : classNumber K = classNumber L := by
  rw [classNumber, classNumber]
  exact Fintype.card_congr (RingEquiv.classGroupEquiv e).toEquiv
