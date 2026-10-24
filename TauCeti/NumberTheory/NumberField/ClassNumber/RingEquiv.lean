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
* `RingEquiv.classGroupEquiv_refl`, `RingEquiv.classGroupEquiv_symm`,
  `RingEquiv.classGroupEquiv_trans`: the induced isomorphism respects the identity, inverses and
  compositions of ring isomorphisms.
* `NumberField.RingOfIntegers.mapRingEquiv_refl`, `NumberField.RingOfIntegers.mapRingEquiv_symm`,
  `NumberField.RingOfIntegers.mapRingEquiv_trans`: restricting a ring isomorphism of fields to
  the rings of integers respects the identity, inverses and compositions.
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

/-- The restriction of the identity ring isomorphism of a field to the rings of integers is the
identity ring isomorphism of the ring of integers. -/
theorem NumberField.RingOfIntegers.mapRingEquiv_refl :
    NumberField.RingOfIntegers.mapRingEquiv (RingEquiv.refl K) = RingEquiv.refl (𝓞 K) := by
  ext z
  simp [NumberField.RingOfIntegers.mapRingEquiv_apply]

/-- The restriction of a ring isomorphism of fields to the rings of integers respects
inverses: the inverse of the restriction is the restriction of the inverse. -/
theorem NumberField.RingOfIntegers.mapRingEquiv_symm (e : K ≃+* L) :
    (NumberField.RingOfIntegers.mapRingEquiv e).symm =
      NumberField.RingOfIntegers.mapRingEquiv e.symm := by
  ext x
  simp only [NumberField.RingOfIntegers.mapRingEquiv_apply,
    NumberField.RingOfIntegers.mapRingEquiv_symm_apply]

/-- The restriction of a ring isomorphism of fields to the rings of integers respects
composition: the restriction of a composition is the composition of the restrictions. -/
theorem NumberField.RingOfIntegers.mapRingEquiv_trans {M : Type*} [Field M] (e : K ≃+* L)
    (f : L ≃+* M) :
    NumberField.RingOfIntegers.mapRingEquiv (e.trans f) =
      (NumberField.RingOfIntegers.mapRingEquiv e).trans
        (NumberField.RingOfIntegers.mapRingEquiv f) := by
  ext x
  simp only [NumberField.RingOfIntegers.mapRingEquiv_apply, RingEquiv.trans_apply]

/-- The identity ring isomorphism induces the identity isomorphism on class groups. -/
@[simp]
theorem RingEquiv.classGroupEquiv_refl :
    (RingEquiv.refl K).classGroupEquiv = MulEquiv.refl _ := by
  rw [RingEquiv.classGroupEquiv_eq,
    congrArg ClassGroup.mulEquiv NumberField.RingOfIntegers.mapRingEquiv_refl]
  ext x
  dsimp only [ClassGroup.mulEquiv]
  simp [ClassGroup.map_id]

/-- The inverse of the class-group isomorphism is the class-group isomorphism of the inverse
ring isomorphism. -/
@[simp]
theorem RingEquiv.classGroupEquiv_symm (e : K ≃+* L) :
    e.classGroupEquiv.symm = e.symm.classGroupEquiv := by
  have h : (ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv e)).symm =
      ClassGroup.mulEquiv ((NumberField.RingOfIntegers.mapRingEquiv e).symm) := by
    ext x
    dsimp only [ClassGroup.mulEquiv]
    simp
  rw [RingEquiv.classGroupEquiv_eq, h, RingEquiv.classGroupEquiv_eq]
  exact congrArg ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv_symm e)

/-- The class-group isomorphism of a composition of ring isomorphisms is the composition of the
respective class-group isomorphisms. -/
@[simp]
theorem RingEquiv.classGroupEquiv_trans {M : Type*} [Field M] (e : K ≃+* L) (f : L ≃+* M) :
    (e.trans f).classGroupEquiv = e.classGroupEquiv.trans f.classGroupEquiv := by
  rw [RingEquiv.classGroupEquiv_eq, RingEquiv.classGroupEquiv_eq, RingEquiv.classGroupEquiv_eq,
    congrArg ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv_trans e f)]
  ext x
  dsimp only [ClassGroup.mulEquiv]
  simp [ClassGroup.map_map]

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
