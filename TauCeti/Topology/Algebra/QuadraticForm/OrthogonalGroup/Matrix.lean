/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed

/-!
# Orthogonal groups in continuous matrix coordinates

An isometry to the standard quadratic form identifies the abstract orthogonal group with the
matrix orthogonal group, and the special orthogonal group with the matrix special orthogonal
group. These identifications respect the canonical forward-and-inverse topology
on linear automorphisms and the entrywise topology on matrices. Both the coordinate map and its
inverses are continuous, and determinants agree. Over the reals this is the coordinate comparison
between definite quadratic orthogonal groups and the Euclidean orthogonal group.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance] starRingOfComm

noncomputable section

variable {R V n : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup V] [Module R V] [Fintype n] [DecidableEq n] {Q : QuadraticForm R V}

/-- Standard quadratic coordinates give a topological group isomorphism with the matrix
orthogonal group, when multiplication by two is injective. -/
def orthogonalGroupContinuousMulEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    QuadraticMap.orthogonalGroup Q ≃ₜ* Matrix.orthogonalGroup n R := by
  -- The local `starRingOfComm` instance makes star definitionally the identity.
  let : ContinuousStar R := ⟨continuous_id⟩
  let : ContinuousAdd (Module.End R V) := IsModuleTopology.toContinuousAdd R _
  let : ContinuousAdd (Module.End R (n → R)) := IsModuleTopology.toContinuousAdd R _
  let E := orthogonalGroupEquivMatrix h2 e
  let C := (e.toLinearEquiv.conjAlgEquiv (R := R)).toLinearMap
  have hC (g : QuadraticMap.orthogonalGroup Q) :
      C (g : Module.End R V) =
        (e.orthogonalGroupCongr g : Module.End R (n → R)) := by
    ext x
    simp [C, LinearEquiv.conjAlgEquiv_apply]
  have hforward : Continuous E := by
    apply continuous_induced_rng.mpr
    have h : Continuous fun g : QuadraticMap.orthogonalGroup Q ↦
        LinearMap.toMatrix' (C (g : Module.End R V)) :=
      (IsModuleTopology.continuous_of_linearMap LinearMap.toMatrix'.toLinearMap).comp
        ((IsModuleTopology.continuous_of_linearMap C).comp
          (continuous_linearEquiv_toLinearMap.comp continuous_subtypeVal))
    exact h.congr fun g ↦ by simp [E, hC]
  let D := (e.toLinearEquiv.symm.conjAlgEquiv (R := R)).toLinearMap
  have hD (A : Matrix.orthogonalGroup n R) :
      D (Matrix.toLin' (A : Matrix n n R)) = (E.symm A : Module.End R V) := by
    ext x
    simp [D, E, LinearEquiv.conjAlgEquiv_apply]
  have hback : Continuous fun A : Matrix.orthogonalGroup n R ↦
      (E.symm A : Module.End R V) := by
    exact ((IsModuleTopology.continuous_of_linearMap D).comp
      ((IsModuleTopology.continuous_of_linearMap Matrix.toLin'.toLinearMap).comp
        continuous_subtypeVal)).congr hD
  refine { E with continuous_toFun := hforward, continuous_invFun := ?_ }
  apply continuous_induced_rng.mpr
  apply continuous_linearEquiv_iff.mpr
  refine ⟨hback, ?_⟩
  exact (hback.comp continuous_inv).congr fun A ↦ by simp

/-- The topological coordinate comparison is the algebraic one. -/
@[simp]
theorem toMulEquiv_orthogonalGroupContinuousMulEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    (orthogonalGroupContinuousMulEquivMatrix h2 e :
        QuadraticMap.orthogonalGroup Q ≃* Matrix.orthogonalGroup n R) =
      orthogonalGroupEquivMatrix h2 e :=
  (rfl)

/-- The coordinate comparison sends an automorphism to the matrix of its conjugate by the
chosen quadratic isometry. -/
@[simp]
theorem coe_orthogonalGroupContinuousMulEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupContinuousMulEquivMatrix h2 e g : Matrix n n R) =
      LinearMap.toMatrix' (e.orthogonalGroupCongr g : Module.End R (n → R)) := by
  simp [orthogonalGroupContinuousMulEquivMatrix]

/-- The inverse coordinate comparison acts by matrix multiplication in the chosen coordinates. -/
@[simp]
theorem orthogonalGroupContinuousMulEquivMatrix_symm_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (A : Matrix.orthogonalGroup n R) (x : V) :
    ((orthogonalGroupContinuousMulEquivMatrix h2 e).symm A : V ≃ₗ[R] V) x =
      e.symm ((A : Matrix n n R) *ᵥ e x) := by
  have h := congrArg (fun M : Matrix n n R ↦ M *ᵥ e x)
    (coe_orthogonalGroupContinuousMulEquivMatrix_apply h2 e
      ((orthogonalGroupContinuousMulEquivMatrix h2 e).symm A))
  rw [ContinuousMulEquiv.apply_symm_apply, LinearMap.toMatrix'_mulVec] at h
  apply e.injective
  simpa using h.symm

/-- The coordinate comparison preserves the determinant, so it also identifies the
determinant-one subgroups. -/
-- This is a named rewrite because simp already expands the left-hand side into the
-- determinant of a conjugated endomorphism.
theorem det_orthogonalGroupContinuousMulEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupContinuousMulEquivMatrix h2 e g : Matrix n n R).det =
      (_root_.QuadraticMap.orthogonalDet Q g : R) :=
  det_orthogonalGroupEquivMatrix h2 e g

/-- Standard quadratic coordinates give a topological group isomorphism with the matrix special
orthogonal group, when multiplication by two is injective. -/
def specialOrthogonalGroupContinuousMulEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    QuadraticMap.specialOrthogonalGroup Q ≃ₜ* Matrix.specialOrthogonalGroup n R where
  toMulEquiv := specialOrthogonalGroupEquivMatrix h2 e
  continuous_toFun := by
    -- The special orthogonal comparison is the orthogonal one on the underlying automorphism.
    apply continuous_induced_rng.mpr
    refine (continuous_subtypeVal.comp
      ((orthogonalGroupContinuousMulEquivMatrix h2 e).continuous.comp
        (_root_.QuadraticMap.continuous_specialOrthogonalToOrthogonal Q))).congr fun g ↦ ?_
    exact (coe_specialOrthogonalGroupEquivMatrix_eq_orthogonalGroupEquivMatrix h2 e g).symm
  continuous_invFun := by
    -- The inverse is the orthogonal inverse on the underlying orthogonal matrix.
    apply continuous_induced_rng.mpr
    refine (continuous_subtypeVal.comp
      ((orthogonalGroupContinuousMulEquivMatrix h2 e).symm.continuous.comp
        (continuous_subtypeVal.subtype_mk fun A ↦
          (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1))).congr fun A ↦ ?_
    ext x
    simp

/-- The topological special orthogonal coordinate comparison is the algebraic one. -/
@[simp]
theorem toMulEquiv_specialOrthogonalGroupContinuousMulEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    (specialOrthogonalGroupContinuousMulEquivMatrix h2 e :
        QuadraticMap.specialOrthogonalGroup Q ≃* Matrix.specialOrthogonalGroup n R) =
      specialOrthogonalGroupEquivMatrix h2 e :=
  (rfl)

/-- The special orthogonal coordinate comparison sends an automorphism to the matrix of its
conjugate by the chosen quadratic isometry. -/
@[simp]
theorem coe_specialOrthogonalGroupContinuousMulEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    (specialOrthogonalGroupContinuousMulEquivMatrix h2 e g : Matrix n n R) =
      LinearMap.toMatrix' (e.specialOrthogonalGroupCongr g : Module.End R (n → R)) :=
  coe_specialOrthogonalGroupEquivMatrix_apply h2 e g

/-- The inverse special orthogonal coordinate comparison acts by matrix multiplication in the
chosen coordinates. -/
@[simp]
theorem specialOrthogonalGroupContinuousMulEquivMatrix_symm_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (A : Matrix.specialOrthogonalGroup n R) (x : V) :
    ((specialOrthogonalGroupContinuousMulEquivMatrix h2 e).symm A : V ≃ₗ[R] V) x =
      e.symm ((A : Matrix n n R) *ᵥ e x) :=
  specialOrthogonalGroupEquivMatrix_symm_apply h2 e A x

end

end TauCeti
