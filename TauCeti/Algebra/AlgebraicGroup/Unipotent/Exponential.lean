/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Local nilpotence of invariant vector fields on unipotent groups

Every tangent vector at the identity of a reduced finite-type unipotent affine group over
an algebraically closed field has a locally nilpotent invariant derivation on its coordinate
ring. Faithful upper-unitriangular representations supply the input to this intrinsic
local-nilpotence result.

The local-nilpotence statement holds in every characteristic. In characteristic zero,
Cartier's theorem removes the reducedness assumption, and every tangent vector consequently
defines the intrinsic polynomial exponential curve `Bialgebra.expPointPolynomial` and its
one-parameter homomorphisms `Bialgebra.expPointHom`. Local nilpotence is a conclusion here,
rather than an additional hypothesis on the tangent vector. No connectedness hypothesis or
choice of a matrix realization occurs in that conclusion.

## Main declarations

* `Derivation.tangentMatrix_derivationComp_coordinateBialgHom_apply`: tangent matrix entries
  are derivatives of coefficient-matrix entries.
* `tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular` in
  `Derivation`: the tangent matrix of an upper-unitriangular representation is strictly upper
  triangular.
* `Derivation.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular`:
  that tangent matrix is nilpotent.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular`:
  a faithful upper-unitriangular representation gives locally nilpotent invariant derivations.
* `TauCeti.HopfAlgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint`:
  automatic local nilpotence for reduced groups with unipotent points.
* `exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint_of_charZero` in
  `TauCeti.HopfAlgebra`: the characteristic-zero form without a reducedness assumption.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 14.
-/

public section

namespace Derivation

open TauCeti

variable {R H M B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [CommRing B] [Algebra R B] {n : ℕ}

/-- Differentiating a representation's coordinate morphism differentiates each entry of its
coefficient matrix, with values in any commutative coefficient algebra. -/
-- The generic tangent-matrix and derivation computation rules already simplify its left side.
theorem tangentMatrix_derivationComp_coordinateBialgHom_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) i j =
      Bialgebra.CounitAlgebra.algEquivSelf R H B (d (Comodule.coefficientMatrix b i j)) := by
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply]
  -- The coordinate formula uses the bialgebra-hom coercion rather than its algebra-hom coercion.
  exact congrArg (fun h ↦ Bialgebra.CounitAlgebra.algEquivSelf R H B (d h))
    (Comodule.coordinateBialgHom_X b i j)

/-- Differentiating an upper-unitriangular representation gives zero entries on and below the
matrix diagonal, over any commutative coefficient algebra. -/
theorem tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (i j : Fin n) (hji : j ≤ i) :
    GeneralLinear.tangentMatrix n
      (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) i j = 0 := by
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom_apply b]
  rcases eq_or_lt_of_le hji with rfl | hji
  · rw [hb.apply_diag, d.map_one_eq_zero, map_zero]
  · rw [hb.isUpperTriangular hji, map_zero, map_zero]

/-- Differentiating an upper-unitriangular representation gives a nilpotent matrix over
any commutative coefficient algebra. No characteristic or reducedness assumption is needed. -/
theorem isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    IsNilpotent (GeneralLinear.tangentMatrix n
      (derivationComp (Comodule.coordinateBialgHom (H := H) b) d)) := by
  have hzero :=
    d.tangentMatrix_derivationComp_coordinateBialgHom_apply_eq_zero_of_isUpperUnitriangular b hb
  exact Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero
    (fun _ _ hji ↦ hzero _ _ hji.le) (fun i ↦ hzero i i le_rfl)

/-- A faithful upper-unitriangular representation makes every invariant tangent derivation
locally nilpotent on the coordinate ring, over any commutative base ring. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 :=
  BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _
      (d.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_of_isUpperUnitriangular b hb))

end Derivation

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} {H : Type v} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- Every invariant tangent derivation on a reduced finite-type affine group over an
algebraically closed field with unipotent rational points is locally nilpotent. The group need
not be connected, and the field may have positive characteristic. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint
    [IsReduced H] (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  obtain ⟨M, n, b, hb, hsurj⟩ :=
    Comodule.exists_coordinateBialgHom_surjective_of_forall_isUnipotentPoint hH
  exact d.exists_iterate_leftInvariantDerivation_eq_zero_of_isUpperUnitriangular b hb hsurj

/-- Invariant tangent derivations of a finite-type affine group over an algebraically closed
field of characteristic zero with unipotent rational points are locally nilpotent without any
reducedness assumption.
Thus every tangent vector is an admissible input to the intrinsic polynomial exponential. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint_of_charZero
    [CharZero k] (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  have := isReduced_of_charZero k H
  exact exists_iterate_leftInvariantDerivation_eq_zero_of_forall_isUnipotentPoint hH d

end TauCeti.HopfAlgebra
