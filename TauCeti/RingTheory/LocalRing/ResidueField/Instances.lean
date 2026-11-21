/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Separability and separable-closedness instances on residue fields

This file provides `IsSepClosed` instances for residue fields of local rings and fields,
complementing `Mathlib.RingTheory.LocalRing.ResidueField.Instances`, as well as residue
separability agreement between `ResidueField` and maximal-ideal quotients:

* `TauCeti.IsLocalRing.isSeparable_residueField_iff`: for a local algebra map `A → B`,
  `Algebra.IsSeparable` between `ResidueField`s agrees with that between maximal-ideal quotients,
  mirroring `Algebra.isSeparable_residueField_iff`.
* `TauCeti.IsLocalRing.isSepClosed_maximalIdeal_residueField`: if `IsLocalRing.ResidueField S` is
  separably closed, so is the prime residue field `(IsLocalRing.maximalIdeal S).ResidueField`.
* `TauCeti.Field.isSepClosed_residueField`: the residue field `IsLocalRing.ResidueField K` of a
  separably closed field `K` is separably closed.
-/

public section

namespace TauCeti

section Separable
open _root_.IsLocalRing
attribute [local instance] Ideal.Quotient.field

/-- For a local algebra map `A → B`, `ResidueField B / ResidueField A` is separable iff
`(B ⧸ maximalIdeal B) / (A ⧸ maximalIdeal A)` is separable. -/
theorem IsLocalRing.isSeparable_residueField_iff {A B : Type*} [CommRing A] [_root_.IsLocalRing A]
    [CommRing B] [_root_.IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) ↔
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) := by
  refine Algebra.IsSeparable.iff_of_equiv_equiv
    (TauCeti.residueFieldAlgEquivOfSurjective (ψ := Algebra.ofId A (A ⧸ maximalIdeal A))
      Ideal.Quotient.mk_surjective).toRingEquiv
    (TauCeti.residueFieldAlgEquivOfSurjective (ψ := Algebra.ofId B (B ⧸ maximalIdeal B))
      Ideal.Quotient.mk_surjective).toRingEquiv (RingHom.ext fun x ↦ ?_)
  obtain ⟨a, rfl⟩ := residue_surjective x
  have hA := TauCeti.residueFieldAlgEquivOfSurjective_residue
    (ψ := Algebra.ofId A (A ⧸ maximalIdeal A)) Ideal.Quotient.mk_surjective a
  have hB := TauCeti.residueFieldAlgEquivOfSurjective_residue
    (ψ := Algebra.ofId B (B ⧸ maximalIdeal B)) Ideal.Quotient.mk_surjective (algebraMap A B a)
  simp [hA, hB, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_mk_of_liesOver]
end Separable

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

end TauCeti
