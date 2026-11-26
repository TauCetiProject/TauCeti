/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.DedekindDomain.PID
public import TauCeti.RingTheory.ClassGroup.RelNorm

import TauCeti.NumberTheory.ClassGroup.Equiv
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.ClassGroup.Galois

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
`Nat.card (ClassGroup R) = classNumber K` for every ring isomorphism `R ≃+* 𝓞 K`. In the same way
the native Dedekind equivalences *class number one ⇔ principal ideal domain ⇔ unique factorization
domain* hold for every such model `R`, not only for `𝓞 K` itself.

## Main definitions and results

* `RingEquiv.classGroupEquiv`: the isomorphism `ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L)` induced by
  an isomorphism of fields `K ≃+* L`.
* `RingEquiv.classGroupEquiv_mk0`: it sends the class of a nonzero ideal `I` to the class of
  `I.map (mapRingEquiv e)`.
* `RingEquiv.classGroupEquiv_refl`, `RingEquiv.classGroupEquiv_symm`,
  `RingEquiv.classGroupEquiv_trans`: functoriality, including inverses.
* `TauCeti.classGroupAction G K`: for a group `G` acting on `K` by ring automorphisms, such as a
  Galois group `K ≃ₐ[F] K`, the induced action `G →* MulAut (ClassGroup (𝓞 K))`, with
  `TauCeti.classGroupAction_mk0`: `g` sends the class of `I` to the class of its image under `g`.
* `ClassGroup.extendedHom_relNorm_ringOfIntegers`, `ClassGroup.relNorm_mulEquiv_ringOfIntegers`,
  and `ClassGroup.extendedHom_mulEquiv_ringOfIntegers`: Galois orbit-product and tower
  equivariance of `ClassGroup.relNorm` and `ClassGroup.extendedHom` on rings of integers.
* `RingEquiv.classNumber_eq`: isomorphic number fields have equal class numbers.
* `RingEquiv.natCard_classGroup_eq_classNumber`: a ring isomorphic to `𝓞 K` has `classNumber K`
  ideal classes.
* `NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid`: `classNumber K = 1` exactly when
  `𝓞 K` is a unique factorization domain.
* `RingEquiv.classNumber_eq_one_iff_isPrincipalIdealRing`,
  `RingEquiv.classNumber_eq_one_iff_uniqueFactorizationMonoid`: for a ring `R ≃+* 𝓞 K`,
  `classNumber K = 1` exactly when `R` is a principal ideal domain, respectively a unique
  factorization domain.

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
      ClassGroup.mk0 ⟨I.val.map (RingOfIntegers.mapRingEquiv e),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ := by
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

end RingEquiv

namespace TauCeti

variable (G : Type*) [Group G] (K : Type*) [Field K] [MulSemiringAction G K]

/-- The action on the ideal class group of `𝓞 K` of a group `G` acting on the field `K` by ring
automorphisms: `g` acts by the class-group automorphism induced by the restriction of `g` to
`𝓞 K`, so that `g [I] = [g I]`. For a Galois group `G = K ≃ₐ[F] K` this is the Galois action on
ideal classes. -/
noncomputable def classGroupAction : G →* MulAut (ClassGroup (𝓞 K)) :=
  ClassGroup.mulEquivHom.comp (MulSemiringAction.toRingAut G (𝓞 K))

variable {G K} in
/-- The element `g` acts on ideal classes through the class-group isomorphism of the ring
automorphism of `K` by which it acts. -/
theorem classGroupAction_apply (g : G) :
    classGroupAction G K g = (MulSemiringAction.toRingEquiv G K g).classGroupEquiv := by
  rw [RingEquiv.classGroupEquiv_def, classGroupAction, MonoidHom.comp_apply,
    ClassGroup.mulEquivHom_apply]
  exact congrArg _ <| RingEquiv.ext fun _ ↦ RingOfIntegers.ext rfl

variable {G K} in
/-- The element `g` sends the class of a nonzero ideal `I` of `𝓞 K` to the class of its image
under `g`. -/
@[simp]
theorem classGroupAction_mk0 [NumberField K] (g : G) (I : (Ideal (𝓞 K))⁰) :
    classGroupAction G K g (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.val.map (RingOfIntegers.mapRingEquiv (MulSemiringAction.toRingEquiv G K g)),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingEquiv.injective _)).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ := by
  rw [classGroupAction_apply, RingEquiv.classGroupEquiv_mk0]

end TauCeti

namespace RingEquiv

variable {K L M : Type*} [Field K] [Field L] [Field M]

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

/-- **Class number one for a model of the ring of integers.** For a ring `R` isomorphic to the ring
of integers of `K`, the class number of `K` is `1` exactly when `R` is a principal ideal ring. -/
theorem classNumber_eq_one_iff_isPrincipalIdealRing {R : Type*} [CommRing R] [NumberField K]
    (f : R ≃+* 𝓞 K) : classNumber K = 1 ↔ IsPrincipalIdealRing R :=
  classNumber_eq_one_iff.trans
    ⟨fun _ ↦ .of_surjective f.symm.toRingHom f.symm.surjective,
      fun _ ↦ .of_surjective f.toRingHom f.surjective⟩

end RingEquiv

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Class number one is unique factorization.** The class number of a number field `K` is `1`
exactly when `𝓞 K` is a unique factorization domain: a principal ideal domain has unique
factorization, and a Dedekind domain with unique factorization is a principal ideal domain. -/
theorem classNumber_eq_one_iff_uniqueFactorizationMonoid :
    classNumber K = 1 ↔ UniqueFactorizationMonoid (𝓞 K) :=
  classNumber_eq_one_iff.trans
    ⟨fun _ ↦ inferInstance,
      fun _ ↦ IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid (𝓞 K)⟩

end NumberField

namespace RingEquiv

variable {K : Type*} [Field K] [NumberField K]

/-- **Unique factorization in a model of the ring of integers.** For a ring `R` isomorphic to
the ring of integers of `K`, the class number of `K` is `1` exactly when `R` is a unique
factorization domain. -/
theorem classNumber_eq_one_iff_uniqueFactorizationMonoid {R : Type*} [CommRing R]
    (f : R ≃+* 𝓞 K) : classNumber K = 1 ↔ UniqueFactorizationMonoid R :=
  NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid.trans
    (f.toMulEquiv.uniqueFactorizationMonoid_iff).symm

end RingEquiv

namespace ClassGroup

open scoped NumberField

/-- **Class-group Galois orbit product for number fields**, expressed in terms of
`NumberField.RingOfIntegers.mapRingEquiv`. -/
theorem extendedHom_relNorm_ringOfIntegers (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L] (c : ClassGroup (𝓞 L)) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) (ClassGroup.relNorm (𝓞 K) c) =
      ∏ σ : L ≃ₐ[K] L,
        ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) c := by
  rw [extendedHom_relNorm (𝓞 K) K L (𝓞 L) c]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  have hEq : (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv =
      RingOfIntegers.mapRingEquiv σ.toRingEquiv :=
    RingEquiv.ext fun z ↦ RingOfIntegers.ext (algebraMap_galRestrict_apply (𝓞 K) σ z)
  rw [hEq]

/-- Restriction of a field automorphism `τ : L ≃ₐ[F] L` to a normal subextension `K / F` commutes
with the inclusion `algebraMap (𝓞 K) (𝓞 L)` on rings of integers. -/
theorem _root_.NumberField.RingOfIntegers.mapRingEquiv_algebraMap_restrictNormal
    {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F K] (τ : L ≃ₐ[F] L) (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv τ.toRingEquiv (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K) (𝓞 L)
        (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv x) :=
  RingOfIntegers.ext <| by
    simp only [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
      RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (τ.restrictNormal_commutes K _).symm

/-- **Galois equivariance of `ClassGroup.relNorm` on rings of integers** for a normal subextension
`K / F` inside `L / F`. -/
theorem relNorm_mulEquiv_ringOfIntegers {F K L : Type*} [Field F] [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F K] (τ : L ≃ₐ[F] L) (c : ClassGroup (𝓞 L)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv)
        (ClassGroup.relNorm (𝓞 K) c) =
      ClassGroup.relNorm (𝓞 K)
        (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv τ.toRingEquiv) c) :=
  relNorm_mulEquiv _ _ (RingOfIntegers.mapRingEquiv_algebraMap_restrictNormal τ) c

/-- **Galois equivariance of `ClassGroup.extendedHom` on rings of integers** for a normal
subextension `K / F` inside `L / F`. -/
theorem extendedHom_mulEquiv_ringOfIntegers {F K L : Type*} [Field F] [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F K] (τ : L ≃ₐ[F] L) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv τ.toRingEquiv)
        (ClassGroup.extendedHom (𝓞 K) (𝓞 L) c) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv) c) :=
  extendedHom_mulEquiv _ _ (RingOfIntegers.mapRingEquiv_algebraMap_restrictNormal τ) c

end ClassGroup
