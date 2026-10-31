/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# The Galois group of a symmetric algebra over its invariants

Let `ρ` be a faithful representation of a group `G` on a module `M`, acting on the symmetric
algebra `Sym M` through `Representation.symmetricAlgebraMulSemiringAction`. The induced action on
`Sym M` is again faithful, since `Sym M` contains `M` in degree one
(`Representation.faithfulSMul_symmetricAlgebraMulSemiringAction_iff`), and its fixed subalgebra is
the invariant subalgebra `Sym(M)^G` by definition. So `G` is a Galois group of `Sym M` over
`Sym(M)^G` in the sense of Mathlib's `IsGaloisGroup`, and Mathlib's Galois theory for
`IsGaloisGroup` applies to it.

Over a domain `R` with `M` free, `Sym M` is a domain, and for a finite group the extension of
fraction fields `Frac(Sym M) / Frac(Sym(M)^G)` is Galois with group `G`. Taking `M = V*` with the
contragredient action, this is the extension `K(V) / K(V)^G` of rational functions on `V` and
its invariant subfield. Two consequences of the Galois correspondence are recorded:

* for a subgroup `H`, the elements of `G` fixing every `H`-invariant polynomial are exactly the
  elements of `H`. When `H` is normal, this says that `G ⧸ H` acts faithfully on `Sym(M)^H`,
  that is, on the intermediate quotient `V/H` in `V → V/H → V/G`;
* the rank of `Sym M` over `Sym(M)^G`, the generic degree of the quotient map `V → V/G`, is
  `|G|`.

A faithful action on `V` gives a faithful contragredient action on `V*` by
`Representation.dual_injective_iff`, so these statements apply to polynomial functions on `V`.

## Main results

* `Representation.isGaloisGroup_symmetricAlgebraInvariants`: for faithful `ρ`, `G` is a Galois
  group of `Sym M` over `Sym(M)^G`.
* `Representation.isGaloisGroup_fractionRing_symmetricAlgebraInvariants`: for finite `G`, it is
  the Galois group of the extension of fraction fields.
* `Representation.fixingSubgroup_symmetricAlgebraInvariants_comp_subtype`: the subgroup of `G`
  fixing the invariants of a subgroup `H` is `H`.
* `Representation.finrank_symmetricAlgebraInvariants`: `Sym M` has rank `|G|` over `Sym(M)^G`.

## References

* E. Artin, *Galois Theory*, Notre Dame Mathematical Lectures 2 (1942), for the fixed-field
  theorem behind the Galois correspondence of a finite group of automorphisms.
* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001).
* The Galois theory used here is Mathlib's `IsGaloisGroup` API (Thomas Browning), in
  `Mathlib.RingTheory.IsGaloisGroup` and `Mathlib.FieldTheory.Galois.IsGaloisGroup`.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

section Group

variable {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- For a faithful representation `ρ`, the group `G` is a Galois group of `Sym M` over the
invariant subalgebra `Sym(M)^G`: it acts faithfully on `Sym M` with fixed subalgebra
`Sym(M)^G`. -/
theorem isGaloisGroup_symmetricAlgebraInvariants (hρ : Function.Injective ρ) :
    letI := ρ.symmetricAlgebraMulSemiringAction
    IsGaloisGroup G ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  { faithful := ρ.faithfulSMul_symmetricAlgebraMulSemiringAction_iff.2 hρ
    commutes := ρ.symmetricAlgebraInvariants_eq_fixedPoints ▸ inferInstance
    isInvariant := ρ.isInvariant_symmetricAlgebraInvariants }

end Group

section Domain

variable {R G M : Type*} [CommRing R] [IsDomain R] [Group G] [AddCommGroup M] [Module R M]
  [Module.Free R M]
variable (ρ : Representation R G M)

attribute [local instance] FractionRing.liftAlgebra in
/-- For a faithful representation `ρ` of a finite group `G` on a free module over a domain, the
fraction field of `Sym M` is Galois over the fraction field of `Sym(M)^G` with Galois group `G`.
For `M = V*` this is the extension `K(V) / K(V)^G` of rational functions on `V`. -/
theorem isGaloisGroup_fractionRing_symmetricAlgebraInvariants [Finite G]
    (hρ : Function.Injective ρ) :
    letI := ρ.symmetricAlgebraMulSemiringAction
    letI := IsFractionRing.mulSemiringAction G (SymmetricAlgebra R M)
      (FractionRing (SymmetricAlgebra R M))
    IsGaloisGroup G (FractionRing ρ.symmetricAlgebraInvariants)
      (FractionRing (SymmetricAlgebra R M)) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  letI := IsFractionRing.mulSemiringAction G (SymmetricAlgebra R M)
    (FractionRing (SymmetricAlgebra R M))
  haveI := ρ.isGaloisGroup_symmetricAlgebraInvariants hρ
  IsGaloisGroup.to_isFractionRing G ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M)
    (FractionRing ρ.symmetricAlgebraInvariants) (FractionRing (SymmetricAlgebra R M))

/-- For a faithful representation `ρ` of a finite group `G` on a free module over a domain, the
elements of `G` fixing every polynomial invariant of a subgroup `H` are exactly the elements of
`H`. For normal `H`, this says that `G ⧸ H` acts faithfully on `Sym(M)^H`. -/
theorem fixingSubgroup_symmetricAlgebraInvariants_comp_subtype [Finite G]
    (hρ : Function.Injective ρ) (H : Subgroup G) :
    letI := ρ.symmetricAlgebraMulSemiringAction
    fixingSubgroup G
        (Representation.symmetricAlgebraInvariants (ρ.comp H.subtype) :
          Set (SymmetricAlgebra R M)) = H := by
  let := ρ.symmetricAlgebraMulSemiringAction
  have := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  have := ρ.isGaloisGroup_symmetricAlgebraInvariants hρ
  have : FaithfulSMul G (SymmetricAlgebra R M) :=
    ρ.faithfulSMul_symmetricAlgebraMulSemiringAction_iff.2 hρ
  -- `H` is a Galois group of `Sym M` over its fixed points, which are the invariants of `H`.
  have : IsGaloisGroup H (FixedPoints.subalgebra R (SymmetricAlgebra R M) H)
      (SymmetricAlgebra R M) :=
    { faithful := inferInstance
      commutes := inferInstance
      isInvariant := inferInstance }
  rw [ρ.symmetricAlgebraInvariants_comp_subtype H]
  simpa using IsGaloisGroup.fixingSubgroup_range_algebraMap G ρ.symmetricAlgebraInvariants
    (FixedPoints.subalgebra R (SymmetricAlgebra R M) H) (SymmetricAlgebra R M) H

/-- For a faithful representation `ρ` of a finite group `G` on a free module over a domain,
`Sym M` has rank `|G|` over the invariant subalgebra `Sym(M)^G`: this is the degree of the
extension of fraction fields. -/
theorem finrank_symmetricAlgebraInvariants [Finite G] (hρ : Function.Injective ρ) :
    Module.finrank ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M) = Nat.card G := by
  let := ρ.symmetricAlgebraMulSemiringAction
  have := ρ.isGaloisGroup_symmetricAlgebraInvariants hρ
  exact (IsGaloisGroup.card_eq_finrank' G _ _).symm

end Domain

end Representation
