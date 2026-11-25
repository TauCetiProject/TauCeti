/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.LocalRing.ResidueField.Separable
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Separability and separable-closedness instances on residue fields

This file provides `IsSepClosed` and `Algebra.HasSeparableResidueFieldsAt` results for residue
fields of local rings and fields, complementing
`Mathlib.RingTheory.LocalRing.ResidueField.Instances`:

* `TauCeti.IsLocalRing.isSepClosed_maximalIdeal_residueField`: if `IsLocalRing.ResidueField S` is
  separably closed, so is the prime residue field `(IsLocalRing.maximalIdeal S).ResidueField`.
* `TauCeti.Field.isSepClosed_residueField`: the residue field `IsLocalRing.ResidueField K` of a
  separably closed field `K` is separably closed.
* `TauCeti.IsLocalRing.hasSeparableResidueFieldsAt_maximalIdeal` and
  `TauCeti.IsLocalRing.hasSeparableResidueFieldsAt_under_maximalIdeal`: for an integral local
  homomorphism `R → S` of local rings with separable residue extension,
  `Algebra.HasSeparableResidueFieldsAt` holds at the maximal ideal of `R`.
-/

public section

namespace TauCeti

/-- Over a local ring `S` whose residue field `IsLocalRing.ResidueField S` is separably closed, the
prime residue field `(IsLocalRing.maximalIdeal S).ResidueField` at the maximal ideal is separably
closed. -/
instance IsLocalRing.isSepClosed_maximalIdeal_residueField (S : Type*) [CommRing S]
    [_root_.IsLocalRing S] [IsSepClosed (_root_.IsLocalRing.ResidueField S)] :
    IsSepClosed (_root_.IsLocalRing.maximalIdeal S).ResidueField :=
  .of_ringEquiv (IsLocalRing.maximalIdealResidueFieldAlgEquiv S).symm.toRingEquiv

/-- The residue field of a separably closed field is separably closed; together with
`Field.henselian` and `TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed`, this makes every
separably closed field strictly henselian. -/
instance Field.isSepClosed_residueField (K : Type*) [Field K] [IsSepClosed K] :
    IsSepClosed (_root_.IsLocalRing.ResidueField K) :=
  .of_ringEquiv (RingEquiv.ofBijective (_root_.IsLocalRing.residue K)
    ⟨(_root_.IsLocalRing.residue K).injective, _root_.IsLocalRing.residue_surjective⟩)

/-- For an integral local homomorphism `R → S` of local rings with separable residue-field
extension and a prime `p = IsLocalRing.maximalIdeal R`, `Algebra.HasSeparableResidueFieldsAt R S p`
holds: every prime of `S` over `maximalIdeal R` is maximal by Going-Up, hence equals
`maximalIdeal S`. -/
theorem IsLocalRing.hasSeparableResidueFieldsAt_of_eq_maximalIdeal {R S : Type*}
    [CommRing R] [_root_.IsLocalRing R] [CommRing S] [_root_.IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField R)
      (_root_.IsLocalRing.ResidueField S)]
    {p : Ideal R} [p.IsPrime] (hp : p = _root_.IsLocalRing.maximalIdeal R) :
    Algebra.HasSeparableResidueFieldsAt R S p := by
  subst hp
  refine ⟨fun q _ hq_over ↦ ?_⟩
  have hq_max : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under q
    (hq_over.over ▸ _root_.IsLocalRing.maximalIdeal.isMaximal R)
  obtain rfl : q = _root_.IsLocalRing.maximalIdeal S := _root_.IsLocalRing.eq_maximalIdeal hq_max
  let := Localization.AtPrime.algebraOfLiesOver (_root_.IsLocalRing.maximalIdeal R)
    (_root_.IsLocalRing.maximalIdeal S)
  refine Algebra.IsSeparable.of_equiv_equiv
    (IsLocalRing.maximalIdealResidueFieldAlgEquiv R).symm.toRingEquiv
    (IsLocalRing.maximalIdealResidueFieldAlgEquiv S).symm.toRingEquiv ?_
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨r, rfl⟩ := _root_.IsLocalRing.residue_surjective x
  simp [← IsScalarTower.algebraMap_apply]

/-- For an integral local homomorphism `R → S` of local rings with separable residue-field
extension, `Algebra.HasSeparableResidueFieldsAt` holds at `IsLocalRing.maximalIdeal R`. -/
theorem IsLocalRing.hasSeparableResidueFieldsAt_maximalIdeal (R S : Type*)
    [CommRing R] [_root_.IsLocalRing R] [CommRing S] [_root_.IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField R)
      (_root_.IsLocalRing.ResidueField S)] :
    Algebra.HasSeparableResidueFieldsAt R S (_root_.IsLocalRing.maximalIdeal R) :=
  IsLocalRing.hasSeparableResidueFieldsAt_of_eq_maximalIdeal rfl

/-- Variant of `IsLocalRing.hasSeparableResidueFieldsAt_maximalIdeal` stated at
`(IsLocalRing.maximalIdeal S).under R`. -/
theorem IsLocalRing.hasSeparableResidueFieldsAt_under_maximalIdeal (R S : Type*)
    [CommRing R] [_root_.IsLocalRing R] [CommRing S] [_root_.IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField R)
      (_root_.IsLocalRing.ResidueField S)] :
    Algebra.HasSeparableResidueFieldsAt R S ((_root_.IsLocalRing.maximalIdeal S).under R) :=
  IsLocalRing.hasSeparableResidueFieldsAt_of_eq_maximalIdeal
    (_root_.IsLocalRing.maximalIdeal_comap (algebraMap R S))

end TauCeti
