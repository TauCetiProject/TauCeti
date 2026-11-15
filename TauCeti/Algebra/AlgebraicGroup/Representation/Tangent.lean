/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential

/-!
# Tangent matrices of representations

Differentiating a representation's coordinate morphism differentiates its coefficient matrix
entrywise. For an upper-unitriangular coefficient matrix, the tangent matrix is strictly upper
triangular and hence nilpotent. If the coordinate morphism is also surjective, local nilpotence
of the invariant derivation descends from the general-linear coordinate algebra.

These statements work over arbitrary commutative base rings. Tangent matrix entries may take
values in any commutative coefficient algebra. No reducedness or characteristic assumption is
needed.

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
