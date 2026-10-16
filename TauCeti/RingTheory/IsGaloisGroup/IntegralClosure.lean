/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Galois groups of integral closures

If `G` is a finite Galois group of a field extension `M / L` and `C` is an integrally closed
domain with fraction field `L`, then `G` is a Galois group of the integral closure `B` of `C` in
`M` over `C`, for any action of `G` on `B` compatible with its action on `M`.

Mathlib's `IsGaloisGroup.of_isFractionRing` states this with `M` a fraction field of `B` and
`B / C` integral; both follow from `B` being the integral closure of `C` in `M`, which is how the
rings arise over a Dedekind base. The second statement is the form needed for a tower: for a
domain `A` with fraction field `K`, a finite extension `L` of `K`, an extension `M` of `L`, and
the integral closures `C` and `B` of `A` in `L` and in `M`, a Galois group of `M / L` is a Galois
group of `B / C`. The third statement specializes the tower to a fixed field: for a finite
extension `M / K` and a subgroup `H` of `Gal(M/K)`, with `C` the integral closure of `A` in
`M ^ H`, the subgroup `H` is a Galois group of `B / C`.

## Main results

* `IsGaloisGroup.of_isIntegralClosure`: a Galois group of `M / L` is a Galois group of the
  integral closure of `C` in `M` over `C`.
* `IsGaloisGroup.of_isIntegralClosure_tower`: the same for the integral closures of a common
  base `A` in `L` and in `M`.
* `IsGaloisGroup.of_isIntegralClosure_fixedField`: a subgroup `H` of `Gal(M/K)` is a Galois group
  of the integral closures of a common base in `M ^ H` and in `M`.
-/

public section

namespace IsGaloisGroup

section IntegrallyClosed

variable (G C B L M : Type*) [Group G] [Finite G] [CommRing C] [CommRing B]
  [Algebra C B] [Field L] [Field M] [Algebra C L] [Algebra L M] [Algebra C M] [Algebra B M]
  [IsScalarTower C L M] [IsScalarTower C B M] [IsFractionRing C L] [IsIntegrallyClosed C]
  [IsIntegralClosure B C M] [MulSemiringAction G M] [MulSemiringAction G B]
  [SMulDistribClass G B M]

/-- **A Galois group of fields is a Galois group of integral closures.** If `G` is a finite Galois
group of `M / L`, where `L` is the fraction field of an integrally closed domain `C`, then `G`
is a Galois group of the integral closure of `C` in `M` over `C`. -/
theorem of_isIntegralClosure [IsGaloisGroup G L M] : IsGaloisGroup G C B :=
  have : FiniteDimensional L M := IsGaloisGroup.finiteDimensional G L M
  have : IsDomain C := (IsFractionRing.injective C L).isDomain _
  have : IsDomain B := (IsIntegralClosure.algebraMap_injective B C M).isDomain _
  have : IsFractionRing B M := IsIntegralClosure.isFractionRing_of_finite_extension C L M B
  have : Algebra.IsIntegral C B := IsIntegralClosure.isIntegral_algebra C M
  of_isFractionRing G C B L M

end IntegrallyClosed

section Tower

variable (G A K L M C B : Type*) [Group G] [Finite G] [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Field M] [Algebra L M] [Algebra A M] [CommRing C] [Algebra A C]
  [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] [CommRing B] [Algebra A B]
  [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M] [Algebra C B] [Algebra C M]
  [IsScalarTower A C B] [IsScalarTower C L M] [IsScalarTower C B M]
  [MulSemiringAction G M] [MulSemiringAction G B] [SMulDistribClass G B M]

include A K in
/-- **Galois groups in a tower of integral closures.** Let `A` be a domain with fraction field
`K`, let `L` be a finite extension of `K` and `M` an extension of `L`, and let `C` and `B` be the
integral closures of `A` in `L` and in `M`. A finite Galois group of `M / L` is then a Galois
group of `B` over `C`. -/
theorem of_isIntegralClosure_tower [IsGaloisGroup G L M] : IsGaloisGroup G C B :=
  have : IsDomain C := (IsIntegralClosure.algebraMap_injective C A L).isDomain _
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : IsIntegrallyClosed C := (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mpr
    (IsIntegrallyClosedIn.of_isIntegralClosure A)
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have : IsScalarTower A C M := .of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq A B M, IsScalarTower.algebraMap_eq A C B,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq C B M]
  have : IsIntegralClosure B C M := IsIntegralClosure.tower_top (R := A)
  of_isIntegralClosure G C B L M

end Tower

section FixedField

open IntermediateField

variable (A : Type*) {K M : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field M] [Algebra K M] [FiniteDimensional K M] [Algebra A M]
  (H : Subgroup Gal(M/K)) [Algebra A (fixedField H)] [IsScalarTower A K (fixedField H)]
  (C B : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)] [IsIntegralClosure C A (fixedField H)] [CommRing B]
  [Algebra A B] [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M] [Algebra C B]
  [Algebra C M] [IsScalarTower A C B] [IsScalarTower C (fixedField H) M] [IsScalarTower C B M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

include A K in
/-- **Fixed-field subgroups as Galois groups of integral closures.** Let `A` be a domain with
fraction field `K`, let `M / K` be a finite extension, and let `H` be a subgroup of `Gal(M/K)`. If
`C` and `B` are the integral closures of `A` in the fixed field `M ^ H` and in `M`, then `H` is a
Galois group of `B` over `C`. The extension `M / K` need not be Galois. -/
theorem of_isIntegralClosure_fixedField : IsGaloisGroup H C B :=
  have : IsGalois (fixedField H) M := IsGalois.of_fixed_field M H
  have : IsGaloisGroup H (fixedField H) M :=
    of_mulEquiv_algEquiv (subgroupEquivAlgEquiv H) fun _ _ ↦ rfl
  of_isIntegralClosure_tower H A K (fixedField H) M C B

end FixedField

end IsGaloisGroup
