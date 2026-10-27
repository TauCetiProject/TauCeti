/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

import TauCeti.NumberTheory.ClassGroup.Equiv
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# Transport of class groups and class numbers along isomorphisms

An isomorphism of fields `e : K ≃+* L` restricts to an isomorphism
`NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K ≃+* 𝓞 L` of the rings of integers, and a ring
isomorphism of domains induces an isomorphism of ideal class groups, `ClassGroup.mulEquiv`. This
file composes the two into the class-group isomorphism `RingEquiv.classGroupEquiv e` attached to an
isomorphism of fields, and records that the construction is functorial and acts on ideal classes
by pushing ideals forward. A `ℚ`-algebra isomorphism `e : K ≃ₐ[ℚ] L` is used through its
underlying ring isomorphism `e.toRingEquiv`.

Consequently the class number of a number field is an isomorphism invariant, and it can be
computed from any ring isomorphic to the ring of integers, such as an explicit integral model:
`Nat.card (ClassGroup R) = classNumber K` for every ring isomorphism `R ≃+* 𝓞 K`.

## Main definitions and results

* `RingEquiv.classGroupEquiv`: the isomorphism `ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L)` induced by
  an isomorphism of fields `K ≃+* L`.
* `RingEquiv.classGroupEquiv_mk0`: it sends the class of a nonzero ideal `I` to the class of
  `I.map (mapRingEquiv e)`.
* `RingEquiv.classGroupEquiv_refl`, `RingEquiv.classGroupEquiv_symm`,
  `RingEquiv.classGroupEquiv_trans`: functoriality, including inverses.
* `RingEquiv.classNumber_eq`: isomorphic number fields have equal class numbers.
* `RingEquiv.natCard_classGroup_eq_classNumber`: a ring isomorphic to `𝓞 K` has `classNumber K`
  ideal classes.

## Source note

The construction of `RingEquiv.classGroupEquiv` as `ClassGroup.mulEquiv` of
`NumberField.RingOfIntegers.mapRingEquiv e`, and the deduction of `RingEquiv.classNumber_eq` from
it, follow the earlier Tau Ceti formalization in
[TauCeti PR #19781](https://github.com/TauCetiProject/TauCeti/pull/19781) by @aisathome-agent
(feat: isomorphic number fields have the same class number).
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace RingEquiv

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The isomorphism of ideal class groups of the rings of integers induced by an isomorphism of
fields `e : K ≃+* L`. -/
noncomputable def classGroupEquiv (e : K ≃+* L) : ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L) :=
  ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)

/-- The class-group isomorphism of `e` is the one induced by the restriction of `e` to the rings
of integers. This gives access to the general `ClassGroup.mulEquiv` API. -/
theorem classGroupEquiv_def (e : K ≃+* L) :
    e.classGroupEquiv = ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e) := by
  unfold classGroupEquiv
  rfl

/-- The class-group isomorphism of `e` sends the class of a nonzero ideal `I` of `𝓞 K` to the
class of its image `I.map (mapRingEquiv e)` in `𝓞 L`. -/
@[simp]
theorem classGroupEquiv_mk0 [IsDedekindDomain (𝓞 K)] [IsDedekindDomain (𝓞 L)] (e : K ≃+* L)
    (I : (Ideal (𝓞 K))⁰) :
    e.classGroupEquiv (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map (RingOfIntegers.mapRingEquiv e),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  rw [classGroupEquiv_def]
  exact ClassGroup.mulEquiv_mk0 _ I

/-- The identity isomorphism of a field induces the identity of its class group. -/
@[simp]
theorem classGroupEquiv_refl : (RingEquiv.refl K).classGroupEquiv = MulEquiv.refl _ := by
  rw [classGroupEquiv_def, RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl]

/-- The inverse of the class-group isomorphism of `e` is the class-group isomorphism of
`e.symm`. -/
@[simp]
theorem classGroupEquiv_symm (e : K ≃+* L) : e.classGroupEquiv.symm = e.symm.classGroupEquiv := by
  rw [classGroupEquiv_def, classGroupEquiv_def, ClassGroup.mulEquiv_symm,
    RingOfIntegers.mapRingEquiv_symm]

/-- The class-group isomorphism of a composite of isomorphisms of fields is the composite of
their class-group isomorphisms. -/
@[simp]
theorem classGroupEquiv_trans (e : K ≃+* L) (e' : L ≃+* M) :
    (e.trans e').classGroupEquiv = e.classGroupEquiv.trans e'.classGroupEquiv := by
  rw [classGroupEquiv_def, classGroupEquiv_def, classGroupEquiv_def,
    RingOfIntegers.mapRingEquiv_trans, ClassGroup.mulEquiv_trans]

/-- **The class number is an isomorphism invariant.** Isomorphic number fields have equal class
numbers. -/
theorem classNumber_eq [NumberField K] [NumberField L] (e : K ≃+* L) :
    classNumber K = classNumber L :=
  Fintype.card_congr e.classGroupEquiv.toEquiv

/-- A ring `R` isomorphic to the ring of integers of a number field `K` has exactly
`classNumber K` ideal classes. This identifies the class number of `K` with that of an explicit
model of `𝓞 K`. -/
theorem natCard_classGroup_eq_classNumber {R : Type*} [CommRing R] [IsDomain R] [NumberField K]
    (f : R ≃+* 𝓞 K) : Nat.card (ClassGroup R) = classNumber K :=
  (Nat.card_congr (ClassGroup.mulEquiv f).toEquiv).trans Nat.card_eq_fintype_card

end RingEquiv
