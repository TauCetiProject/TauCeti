/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Separable-closedness instances on residue fields

This file provides `IsSepClosed` instances for residue fields of local rings and fields,
complementing `Mathlib.RingTheory.LocalRing.ResidueField.Instances`:

* `TauCeti.IsLocalRing.isSepClosed_maximalIdeal_residueField`: if `IsLocalRing.ResidueField S` is
  separably closed, so is the prime residue field `(IsLocalRing.maximalIdeal S).ResidueField`.
* `TauCeti.Field.isSepClosed_residueField`: the residue field `IsLocalRing.ResidueField K` of a
  separably closed field `K` is separably closed.
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

end TauCeti
