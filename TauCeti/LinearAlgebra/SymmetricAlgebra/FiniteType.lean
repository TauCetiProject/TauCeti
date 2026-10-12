/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.FiniteType
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Finite generation of symmetric algebras

The symmetric algebra of a finite module is a finitely generated algebra. No freeness or
Noetherian hypothesis is needed. This supplies the algebraic finiteness input for the
projective spectrum of a symmetric algebra.

The instances provide finite type over both the coefficient semiring and the degree-zero
part. They are intended for Noetherianity of symmetric algebras and finiteness properties
of their projective spectra.
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric algebra of a finite module is of finite type over the coefficient semiring,
without any freeness assumption. -/
instance instFiniteType [Module.Finite R M] : Algebra.FiniteType R (SymmetricAlgebra R M) := by
  -- This finite-free presentation argument follows the original proof in
  -- `TauCeti.LinearAlgebra.SymmetricAlgebra.Noetherian`, using Mathlib's
  -- `SymmetricAlgebra.equivMvPolynomial` and Tau Ceti's `SymmetricAlgebra.map_surjective`.
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  let : Algebra.FiniteType R (SymmetricAlgebra R (Fin n → R)) :=
    Algebra.FiniteType.equiv inferInstance
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).symm
  exact Algebra.FiniteType.of_surjective (SymmetricAlgebra.map R g)
    (SymmetricAlgebra.map_surjective R g hg)

/-- A finite module has a symmetric algebra of finite type over its degree-zero part. -/
instance instFiniteTypeGradeZero [Module.Finite R M] :
    Algebra.FiniteType (homogeneousSubmodule R M 0) (SymmetricAlgebra R M) := by
  let : IsScalarTower R (homogeneousSubmodule R M 0) (SymmetricAlgebra R M) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule R M 0)
      (A := SymmetricAlgebra R M) fun r => by simp
  exact Algebra.FiniteType.of_restrictScalars_finiteType R
    (homogeneousSubmodule R M 0) (SymmetricAlgebra R M)

end TauCeti.SymmetricAlgebra
