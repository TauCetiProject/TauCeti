/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix targets for Lie representations

A faithful finite-dimensional representation `ρ : L →ₗ⁅K⁆ Module.End K V` becomes an injective Lie
homomorphism `L →ₗ⁅K⁆ Matrix (Fin n) (Fin n) K` once a basis of `V` is chosen, and conversely a
matrix algebra acts faithfully on its coordinate space. So the endomorphism and matrix
formulations of faithfulness are interchangeable.

The dictionary is a statement about two existentials and needs no finiteness of `L`, so it is
independent of any construction of a faithful representation; a construction supplying one
formulation reads off the other by rewriting.

## Main result

* `TauCeti.faithfulRepresentation_iff_exists_injective_lieHom_matrix`: the endomorphism and matrix
  formulations of a faithful finite-dimensional representation agree.
-/

public section

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]

/-- **The matrix and endomorphism formulations of faithfulness agree.** A faithful
finite-dimensional representation becomes an injective Lie homomorphism into a matrix algebra once
a basis of the carrier is chosen, and conversely a matrix algebra acts faithfully on the
coordinate space. No finiteness of `L` is needed: this is a dictionary between two existential
statements. -/
theorem faithfulRepresentation_iff_exists_injective_lieHom_matrix :
    (∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ) ↔
      ∃ (n : ℕ) (f : L →ₗ⁅K⁆ Matrix (Fin n) (Fin n) K), Function.Injective f := by
  constructor
  · rintro ⟨V, _, _, _, ρ, hρ⟩
    refine ⟨Module.finrank K V,
      (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toLieEquiv.toLieHom.comp ρ, ?_⟩
    exact (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).injective.comp hρ
  · rintro ⟨n, f, hf⟩
    let b : Module.Basis (Fin n) K (ULift.{v} (Fin n → K)) :=
      (Pi.basisFun K (Fin n)).map (ULift.moduleEquiv (R := K) (M := Fin n → K)).symm
    exact ⟨ULift.{v} (Fin n → K), inferInstance, inferInstance, Module.Finite.of_basis b,
      (LinearMap.toMatrixAlgEquiv b).symm.toLieEquiv.toLieHom.comp f,
      (LinearMap.toMatrixAlgEquiv b).symm.injective.comp hf⟩

end TauCeti
