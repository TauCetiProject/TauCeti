/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Subgroup.Unitary
import TauCeti.Geometry.Lie.Adjoint.Units.Basic
import TauCeti.LinearAlgebra.Complex.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Matrix coordinates on the Lie algebra of `U(n)`

The Lie algebra `𝔲(n)` of the unitary group (`TauCeti.UnitaryGroup.lieAlgebra n`) is the Lie
algebra of the unitary subgroup of the real Lie group `GL(n, ℂ)`. In matrix coordinates
(`TauCeti.UnitaryGroup.toMatrix`) it consists of the skew-Hermitian matrices
(`TauCeti.UnitaryGroup.exists_toMatrix_eq_iff`), with the commutator bracket
(`TauCeti.UnitaryGroup.toMatrix_lie`), and it has real dimension `n²`
(`TauCeti.UnitaryGroup.finrank_lieAlgebra`). The adjoint action of `U ∈ U(n)` is conjugation,
`A ↦ U A U*` (`TauCeti.UnitaryGroup.toMatrix_adjointRepresentation`).

## Main definitions

* `TauCeti.UnitaryGroup.lieAlgebra`: the Lie algebra `𝔲(n)`.
* `TauCeti.UnitaryGroup.toMatrix`: its matrix coordinates.
* `TauCeti.UnitaryGroup.adjointRepresentation`: the adjoint representation of `U(n)`.
-/

public section

noncomputable section

open Module Complex
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

-- The matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

namespace UnitaryGroup

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Lie algebra `𝔲(n)` of the unitary group: the Lie algebra of the unitary subgroup of the
real Lie group `GL(n, ℂ)`. -/
abbrev lieAlgebra :
    LieSubalgebra ℝ (LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (GL n ℂ)) :=
  Lie.lieSubalgebraOfSubgroup (unitarySubgroup (GL n ℂ))

/-- The matrix coordinates of `𝔲(n)`, as an injective homomorphism of real Lie algebras into the
complex `n × n` matrices with their commutator bracket. Its range is the skew-Hermitian matrices
(`TauCeti.UnitaryGroup.exists_toMatrix_eq_iff`). -/
def toMatrix : lieAlgebra n →ₗ⁅ℝ⁆ Matrix n n ℂ :=
  (Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) :
    LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (GL n ℂ) →ₗ⁅ℝ⁆ Matrix n n ℂ).comp
      (lieAlgebra n).incl

variable {n}

/-- The matrix coordinates of `X` are its image under the canonical identification of the Lie
algebra of `GL(n, ℂ)` with the complex `n × n` matrices. -/
theorem toMatrix_apply (X : lieAlgebra n) :
    toMatrix n X = unitsLieAlgebraEquiv (R := Matrix n n ℂ)
      (X : LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (GL n ℂ)) :=
  Lie.unitsLieAlgebraLieEquiv_apply _

/-- An element of `𝔲(n)` is determined by its matrix coordinates. -/
theorem toMatrix_injective : Function.Injective (toMatrix n) := fun X Y h ↦ by
  rw [toMatrix_apply, toMatrix_apply] at h
  exact Subtype.ext ((unitsLieAlgebraEquiv (R := Matrix n n ℂ)).injective h)

/-- **The matrices of `𝔲(n)` are the skew-Hermitian matrices.** -/
theorem exists_toMatrix_eq_iff (A : Matrix n n ℂ) : (∃ X, toMatrix n X = A) ↔ Aᴴ = -A := by
  rw [← Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg,
    Lie.unitsLieAlgebraLieEquiv_symm_apply]
  refine ⟨?_, fun hA ↦ ⟨⟨_, hA⟩, ?_⟩⟩
  · rintro ⟨X, rfl⟩
    rw [toMatrix_apply, LinearEquiv.symm_apply_apply]
    exact X.2
  · rw [toMatrix_apply, LinearEquiv.apply_symm_apply]

/-- The matrix coordinates of an element of `𝔲(n)` are skew-Hermitian. -/
@[simp]
theorem conjTranspose_toMatrix (X : lieAlgebra n) : (toMatrix n X)ᴴ = -toMatrix n X :=
  (exists_toMatrix_eq_iff _).1 ⟨X, rfl⟩

/-- The matrix coordinates of an element of `𝔲(n)` form a skew-adjoint matrix. -/
private theorem toMatrix_mem_skewAdjoint (X : lieAlgebra n) :
    toMatrix n X ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, conjTranspose_toMatrix]

/-- For a Hermitian matrix `H`, the skew-Hermitian matrix `i H` is the matrix of an element of
`𝔲(n)`. -/
theorem exists_toMatrix_eq_I_smul (H : selfAdjoint (Matrix n n ℂ)) :
    ∃ X, toMatrix n X = I • (H : Matrix n n ℂ) := by
  rw [exists_toMatrix_eq_iff, ← Matrix.star_eq_conjTranspose, ← skewAdjoint.mem_iff,
    Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint]
  exact H.2

/-- The matrix coordinates of a bracket in `𝔲(n)` are the commutator of the matrix coordinates. -/
theorem toMatrix_lie (X Y : lieAlgebra n) :
    toMatrix n ⁅X, Y⁆ = toMatrix n X * toMatrix n Y - toMatrix n Y * toMatrix n X := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]

/-- The Lie algebra `𝔲(n)` is finite-dimensional, as its matrix coordinates are injective. -/
instance instFiniteDimensionalLieAlgebra : FiniteDimensional ℝ (lieAlgebra n) :=
  Module.Finite.of_injective (toMatrix n).toLinearMap toMatrix_injective

/-- The matrix coordinates identify `𝔲(n)` with the skew-Hermitian matrices, as real vector
spaces. -/
private def skewAdjointEquiv : lieAlgebra n ≃ₗ[ℝ] skewAdjoint (Matrix n n ℂ) :=
  LinearEquiv.ofBijective
    ((toMatrix n).toLinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
      toMatrix_mem_skewAdjoint)
    ⟨fun X Y h ↦ toMatrix_injective (congrArg Subtype.val h), fun A ↦ by
      obtain ⟨X, hX⟩ := (exists_toMatrix_eq_iff (A : Matrix n n ℂ)).2 (by
        rw [← Matrix.star_eq_conjTranspose]; exact skewAdjoint.mem_iff.1 A.2)
      exact ⟨X, Subtype.ext hX⟩⟩

private theorem coe_skewAdjointEquiv (X : lieAlgebra n) :
    (skewAdjointEquiv X : Matrix n n ℂ) = toMatrix n X :=
  rfl

/-- Multiplication by `-i` identifies `𝔲(n)` with the Hermitian matrices, as real vector spaces. -/
private def hermitianEquiv : lieAlgebra n ≃ₗ[ℝ] selfAdjoint (Matrix n n ℂ) :=
  LinearEquiv.ofBijective (skewAdjoint.negISMul ∘ₗ skewAdjointEquiv.toLinearMap)
    ⟨fun X Y h ↦ skewAdjointEquiv.injective (Subtype.ext (by
      rw [← skewAdjoint.I_smul_neg_I (skewAdjointEquiv X), ← skewAdjoint.I_smul_neg_I
        (skewAdjointEquiv Y)]
      exact congrArg (fun H : selfAdjoint (Matrix n n ℂ) ↦ I • (H : Matrix n n ℂ)) h)),
    fun H ↦ by
      obtain ⟨X, hX⟩ := exists_toMatrix_eq_I_smul H
      refine ⟨X, Subtype.ext ?_⟩
      simp [skewAdjoint.negISMul, coe_skewAdjointEquiv, hX, smul_smul]⟩

/-- **`𝔲(n)` has real dimension `n²`.** -/
theorem finrank_lieAlgebra : finrank ℝ (lieAlgebra n) = Fintype.card n ^ 2 := by
  rw [hermitianEquiv.finrank_eq]
  exact (finrank_selfAdjoint_submodule (A := Matrix n n ℂ)).trans (by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq])

/-! ### The adjoint representation of `U(n)` -/

/-- The inclusion of `U(n)` into `GL(n, ℂ)` lands in the unitary subgroup. -/
private theorem toUnits_mem_unitarySubgroup (U : Matrix.unitaryGroup n ℂ) :
    Unitary.toUnits U ∈ unitarySubgroup (GL n ℂ) :=
  mem_unitarySubgroup_GL_iff_mem_unitaryGroup.2 U.2

private theorem stable (U : Matrix.unitaryGroup n ℂ)
    (X : LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (GL n ℂ)) (hX : X ∈ lieAlgebra n) :
    ((Lie.continuousAdjointRepresentation (I := 𝓘(ℝ, Matrix n n ℂ)) (G := GL n ℂ)).restrict
      Unitary.toUnits) U X ∈ lieAlgebra n := by
  simpa only [ContRepresentation.restrict_apply_apply, Lie.continuousAdjointRepresentation_apply]
    using Lie.Ad_mem_lieSubalgebraOfSubgroup
      (Subgroup.le_normalizer (toUnits_mem_unitarySubgroup U)) hX

variable (n) in
/-- The adjoint representation of `U(n)` on its Lie algebra `𝔲(n)`: the adjoint representation of
`GL(n, ℂ)`, restricted to `U(n)` and to the invariant subspace `𝔲(n)`. -/
def adjointRepresentation : ContRepresentation ℝ (Matrix.unitaryGroup n ℂ) (lieAlgebra n) :=
  ((Lie.continuousAdjointRepresentation (I := 𝓘(ℝ, Matrix n n ℂ)) (G := GL n ℂ)).restrict
    Unitary.toUnits).subrepresentation (lieAlgebra n).toSubmodule stable

/-- Coercing the restricted action recovers the adjoint action of `GL(n, ℂ)`. -/
@[simp]
theorem coe_adjointRepresentation_apply (U : Matrix.unitaryGroup n ℂ) (X : lieAlgebra n) :
    (adjointRepresentation n U X : LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (GL n ℂ)) =
      Lie.Ad (I := 𝓘(ℝ, Matrix n n ℂ)) (Unitary.toUnits U) X := by
  rw [adjointRepresentation, ContRepresentation.coe_subrepresentation_apply,
    ContRepresentation.restrict_apply_apply, Lie.continuousAdjointRepresentation_apply]

/-- **The adjoint action of `U(n)` in matrix coordinates** is conjugation, `A ↦ U A U*`. -/
@[simp]
theorem toMatrix_adjointRepresentation (U : Matrix.unitaryGroup n ℂ) (X : lieAlgebra n) :
    toMatrix n (adjointRepresentation n U X) =
      (U : Matrix n n ℂ) * toMatrix n X * star (U : Matrix n n ℂ) := by
  rw [toMatrix_apply, coe_adjointRepresentation_apply, Lie.unitsLieAlgebraEquiv_Ad,
    ← toMatrix_apply, Unitary.val_toUnits_apply, Unitary.val_inv_toUnits_apply,
    Matrix.UnitaryGroup.inv_val]

end UnitaryGroup

end TauCeti
