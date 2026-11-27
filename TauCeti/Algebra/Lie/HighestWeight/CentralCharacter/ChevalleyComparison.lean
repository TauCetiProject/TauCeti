/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isomorphism
public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction

/-!
# The centre of the enveloping algebra and the invariant polynomials

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system,
with Weyl vector `ρ`. The linear Harish-Chandra isomorphism `Z(U(L)) ≃ₐ[K] S(H)^W`
(`TauCeti.harishChandraLinearIso b`) followed by the inverse of Chevalley's restriction
isomorphism `S(L)^L ≃ₐ[K] S(H)^W` (`LieSubalgebra.lieChevalleyRestrictionIso H`) is an
isomorphism of algebras

`Z(U(L)) ≃ₐ[K] S(L)^L`

from the centre to the invariant polynomials (`TauCeti.harishChandraChevalleyIso b`). It depends
on the Cartan subalgebra, the base and the translation by `-ρ` built into the linear
Harish-Chandra isomorphism; it is not the symmetrization map, which identifies `S(L)^L` with the
centre only linearly. Its value at a central element `z` is the invariant polynomial whose
restriction to `H` is the linear Harish-Chandra projection of `z`, so its restriction evaluated at
a weight `λ` is the central character `χ_{λ - ρ}(z)`.

## Main definitions

* `TauCeti.harishChandraChevalleyIso b`: the isomorphism `Z(U(L)) ≃ₐ[K] S(L)^L`.

## Main results

* `TauCeti.lieCartanRestriction_harishChandraChevalleyIso_apply`: the restriction to `H` of the
  invariant attached to `z` is the linear Harish-Chandra projection of `z`.
* `TauCeti.lift_lieCartanRestriction_harishChandraChevalleyIso_apply`: its value at `λ` is the
  central character `χ_{λ - ρ}(z)`.
* `TauCeti.harishChandraChevalleyIso_symm_apply`: the inverse sends an invariant `p` to the central
  element whose linear Harish-Chandra projection is the restriction of `p`.
-/

public section

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- **The centre of the enveloping algebra is isomorphic to the invariant polynomials**,
`Z(U(L)) ≃ₐ[K] S(L)^L`: the linear Harish-Chandra isomorphism `Z(U(L)) ≃ₐ[K] S(H)^W` followed by
the inverse of Chevalley's restriction isomorphism `S(L)^L ≃ₐ[K] S(H)^W`. It depends on `H`, on
the base `b` and on the translation by `-ρ`. -/
noncomputable def harishChandraChevalleyIso :
    Subalgebra.center K (U L) ≃ₐ[K] lieInvariants K L L :=
  (harishChandraLinearIso b).trans H.lieChevalleyRestrictionIso.symm

/-- The Chevalley isomorphism of the invariant attached to `z` is the linear Harish-Chandra
isomorphism of `z`. -/
@[simp]
theorem lieChevalleyRestrictionIso_harishChandraChevalleyIso_apply
    (z : Subalgebra.center K (U L)) :
    H.lieChevalleyRestrictionIso (harishChandraChevalleyIso b z) = harishChandraLinearIso b z :=
  AlgEquiv.apply_symm_apply _ _

/-- **The restriction to `H` of the invariant attached to `z` is the linear Harish-Chandra
projection of `z`.** -/
@[simp]
theorem lieCartanRestriction_harishChandraChevalleyIso_apply (z : Subalgebra.center K (U L)) :
    lieCartanRestriction H (harishChandraChevalleyIso b z : _root_.SymmetricAlgebra K L) =
      hcProjectionLinear b z := by
  rw [← LieSubalgebra.coe_lieChevalleyRestrictionIso_apply,
    lieChevalleyRestrictionIso_harishChandraChevalleyIso_apply, coe_harishChandraLinearIso_apply]

/-- **The invariant attached to `z` evaluates the central characters**: its restriction to `H`,
evaluated at a weight `λ`, is the central character `χ_{λ - ρ}(z)`. -/
theorem lift_lieCartanRestriction_harishChandraChevalleyIso_apply (lam : Module.Dual K H)
    (z : Subalgebra.center K (U L)) :
    _root_.SymmetricAlgebra.lift lam
        (lieCartanRestriction H (harishChandraChevalleyIso b z : _root_.SymmetricAlgebra K L)) =
      vermaCentralCharacter b (lam - weylVector (IsKilling.rootSystem H) b) z := by
  rw [lieCartanRestriction_harishChandraChevalleyIso_apply, lift_hcProjectionLinear]

/-- **The inverse isomorphism** sends an invariant `p` to the central element whose linear
Harish-Chandra projection is the restriction of `p` to `H`. -/
theorem hcProjectionLinear_harishChandraChevalleyIso_symm_apply (p : lieInvariants K L L) :
    hcProjectionLinear b ((harishChandraChevalleyIso b).symm p) =
      lieCartanRestriction H (p : _root_.SymmetricAlgebra K L) := by
  rw [harishChandraChevalleyIso, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
    hcProjectionLinear_harishChandraLinearIso_symm_apply,
    LieSubalgebra.coe_lieChevalleyRestrictionIso_apply]

end TauCeti
