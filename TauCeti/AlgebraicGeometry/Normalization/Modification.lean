/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Normalization.Finite
public import TauCeti.AlgebraicGeometry.Normalization.IsIso

/-!
# The finite normalization of an integral scheme is a modification

Let `Y` be an integral scheme and `ν : Y^ν ⟶ Y` its normalization in its function field, along
`Spec k(Y) ⟶ Y`. Over an affine open `U = Spec A` of `Y`, the scheme `Y^ν` is the spectrum of the
integral closure of `A` in `k(Y)`, the fraction field of `A`.

So `ν` is an isomorphism over every affine open whose ring is integrally closed
(`TauCeti.AlgebraicGeometry.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed`, in
`TauCeti.AlgebraicGeometry.Normalization.IsIso`). When `ν` is finite, these rings are N-1
(`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_iff`, in
`TauCeti.AlgebraicGeometry.Normalization.Finite`), and an N-1 domain becomes integrally closed
after inverting one nonzero element. Hence `ν` is an isomorphism over a nonempty, so dense, basic
open of `Y`, and being finite it is proper: `ν` is a modification. Together with
`TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`, this shows that the
finite normalization of an integral locally Noetherian scheme of dimension at most one is a
resolution of singularities: a regular scheme with a finite modification to `Y` (Stacks,
Lemma 33.41.1 (0C45) over a field).

## Main results

* `TauCeti.AlgebraicGeometry.isModification_fromNormalization_fromSpecStalk_genericPoint`: if this
  normalization is finite, it is a modification.

## References

* [Stacks Project, Lemma 33.41.1](https://stacks.math.columbia.edu/tag/0C45).
* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- **Resolution of curves: the normalization is a modification.** If the normalization of an
integral scheme `Y` in its function field, along `Spec k(Y) ⟶ Y`, is finite over `Y`, then it is a
modification of `Y`: it is proper, and an isomorphism over a dense open of `Y` with dense preimage.
Stacks, Lemma 33.41.1 (0C45) over a field. -/
@[stacks 0C45 "modification part, for integral schemes"]
instance isModification_fromNormalization_fromSpecStalk_genericPoint
    [IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization] :
    IsModification (Y.fromSpecStalk (genericPoint Y)).fromNormalization where
  exists_isIso_morphismRestrict := by
    set ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
    obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Y)) isOpen_univ
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have := isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mp ‹_› V hV ‹_›
    -- Some nonzero `s` makes `Γ(Y, V)_s` integrally closed, and `ν` is an isomorphism over `D(s)`.
    obtain ⟨s, hs, _⟩ := Ring.IsN1.exists_isIntegrallyClosed_localization_away (R := Γ(Y, V))
    have := hV.isLocalization_basicOpen s
    have : IsIntegrallyClosed Γ(Y, Y.basicOpen s) := .of_equiv
      (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) _).toRingEquiv
    have hiso := isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed (hV.basicOpen s)
    obtain ⟨y, hy⟩ : (Y.basicOpen s : Set Y).Nonempty :=
      (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp ((basicOpen_eq_bot_iff _).not.mpr hs)
    refine ⟨Y.basicOpen s, (Y.basicOpen s).isOpen.dense ⟨y, hy⟩,
      (ν ⁻¹ᵁ Y.basicOpen s).isOpen.dense ⟨_, ((asIso (ν ∣_ Y.basicOpen s)).inv ⟨y, hy⟩).2⟩, hiso⟩

end TauCeti.AlgebraicGeometry
