/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Algebra.BigOperators.Finset.Pairs
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Frobenius geometry and unitary conjugation on self-adjoint matrix subspaces

For `[RCLike 𝕜]`, `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is the real symmetric
subspace at `𝕜 = ℝ` and the complex Hermitian subspace at `𝕜 = ℂ`. This file equips it uniformly
over `𝕜` with the ambient Frobenius norm and real inner product `⟪A, B⟫ = RCLike.re tr(B * A)` on
the subtype uniformity, builds `Matrix.UnitaryGroup.selfAdjointConj` as a real linear isometry
equivalence, and reads the subspace in real diagonal and strict upper coordinates. The Borel
structure and `volume` live in `TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic`.

## Main declarations

* `TauCeti.selfAdjointMatrixNormedAddCommGroup`, `TauCeti.selfAdjointMatrixInnerProductSpace`.
* `selfAdjoint.coe_inner`, `selfAdjoint.isHermitian_coe`, `selfAdjoint.conjTranspose_coe`,
  `selfAdjoint.inner_eq_rclike_re_trace_mul`, `selfAdjoint.norm_sq_eq_rclike_re_trace_sq`.
* `Matrix.UnitaryGroup.selfAdjointConj`.
* `TauCeti.selfAdjointCoordinates` reads the real diagonal and strict upper entries.
* `TauCeti.selfAdjointDiagonal` embeds real diagonal entries as a self-adjoint diagonal matrix.
* `TauCeti.unitaryConjCoordinates` expresses unitary conjugation in these coordinates.
-/

public section

noncomputable section

open Module
open scoped ComplexConjugate Matrix RealInnerProductSpace

namespace TauCeti
section instances
variable (p : ℕ) (𝕜 : Type*) [RCLike 𝕜]

/-! Scoped in `TauCeti.SelfAdjointMatrix` (and re-exported globally at `ℝ` and `ℂ`) so the global
`ℝ` instance elaborates `selfAdjoint.submodule` with `Real.instAddCommMonoid` rather than
`RCLike.toNormedAddCommGroup` and avoids `[RCLike ?𝕜]` branching on `ESeminormedAddMonoid`. -/

/-- The real self-adjoint matrix subspace over `𝕜` carries the ambient Frobenius norm rebuilt on
the subtype uniformity. -/
@[expose, instance_reducible] def selfAdjointMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
  letI base := Submodule.normedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜))
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

attribute [local instance] selfAdjointMatrixNormedAddCommGroup

/-- The real self-adjoint matrix subspace over `𝕜` carries the real Frobenius inner product
(`selfAdjoint.inner_eq_rclike_re_trace_mul`). -/
@[expose, instance_reducible] def selfAdjointMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)))
    norm_smul_le r A := norm_smul_le r (A : Matrix (Fin p) (Fin p) 𝕜)
    inner A B := ⟪(A : Matrix (Fin p) (Fin p) 𝕜), (B : Matrix (Fin p) (Fin p) 𝕜)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) 𝕜)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) 𝕜) ↑B
    add_left A B C := by
      rw [Submodule.coe_add]
      exact InnerProductSpace.add_left (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) 𝕜) ↑B ↑C
    smul_left A B r := Matrix.frobenius_inner_smul_left r (A : Matrix (Fin p) (Fin p) 𝕜) ↑B }

attribute [local instance] selfAdjointMatrixInnerProductSpace

/-- Uniform additive group structure on the self-adjoint matrix subspace over `𝕜`. -/
theorem selfAdjointMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

/-- Second-countable topology on the self-adjoint matrix subspace over `𝕜`. -/
theorem selfAdjointMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  letI : ProperSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
    FiniteDimensional.proper ℝ _
  secondCountable_of_proper

/-- Completeness of the self-adjoint matrix subspace over `𝕜`. -/
theorem selfAdjointMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  FiniteDimensional.completeSpace ℝ _

/-- Continuous extended norm on the self-adjoint matrix subspace over `𝕜`. -/
@[expose, instance_reducible] def selfAdjointMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  ESeminormedAddMonoid.toContinuousENorm

namespace SelfAdjointMatrix
attribute [scoped instance] selfAdjointMatrixNormedAddCommGroup selfAdjointMatrixInnerProductSpace
  selfAdjointMatrixIsUniformAddGroup selfAdjointMatrixSecondCountableTopology
  selfAdjointMatrixCompleteSpace selfAdjointMatrixContinuousENorm
end SelfAdjointMatrix
end instances
end TauCeti

open scoped TauCeti.SelfAdjointMatrix

namespace selfAdjoint
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

open scoped Matrix.Norms.Frobenius in
/-- The inner product on the self-adjoint subspace is the ambient real Frobenius inner product. -/
@[simp] theorem coe_inner (A B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ⟪A, B⟫ = ⟪(A : Matrix (Fin p) (Fin p) 𝕜), (B : Matrix (Fin p) (Fin p) 𝕜)⟫ := (rfl)

/-- Every element of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is a Hermitian matrix. -/
theorem isHermitian_coe (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    (A : Matrix (Fin p) (Fin p) 𝕜).IsHermitian := A.property

/-- Every element of the self-adjoint matrix subspace equals its conjugate transpose. -/
@[simp] theorem conjTranspose_coe (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    (A : Matrix (Fin p) (Fin p) 𝕜)ᴴ = (A : Matrix (Fin p) (Fin p) 𝕜) := (isHermitian_coe A).eq

/-- Swapping indices conjugates the entry of an element of the self-adjoint matrix subspace. -/
theorem conj_coe_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) (i j : Fin p) :
    conj ((A : Matrix (Fin p) (Fin p) 𝕜) j i) = (A : Matrix (Fin p) (Fin p) 𝕜) i j := by
  simpa using (isHermitian_coe A).apply i j

/-- On the self-adjoint matrix subspace over `𝕜`, `⟪A, Θ⟫ = RCLike.re tr(Θ * A)`. -/
theorem inner_eq_rclike_re_trace_mul
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ⟪A, Θ⟫ = RCLike.re ((Θ : Matrix (Fin p) (Fin p) 𝕜) * (A : Matrix (Fin p) (Fin p) 𝕜)).trace := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner, Matrix.frobenius_inner_def]
  simp only [real_inner_eq_re_inner, RCLike.inner_apply', Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [conj_coe_apply A j i, mul_comm]

/-- On the self-adjoint matrix subspace over `𝕜`, `‖A‖ ^ 2 = RCLike.re tr(A ^ 2)`. -/
theorem norm_sq_eq_rclike_re_trace_sq (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ‖A‖ ^ 2 = RCLike.re (((A : Matrix (Fin p) (Fin p) 𝕜) ^ 2).trace) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_rclike_re_trace_mul, sq]

end selfAdjoint

namespace Matrix.UnitaryGroup
section Algebra
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

/-- Unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence of
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)`. -/
def selfAdjointConj (U : Matrix.unitaryGroup (Fin p) 𝕜) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜) :=
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin p) (Fin p) 𝕜) U
  { toLinearEquiv := LinearEquiv.ofLinearMap
      (e.toAlgEquiv.toLinearMap.restrict (p := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜))
        fun _ hA ↦ IsSelfAdjoint.conjugate hA U)
      (e.symm.toAlgEquiv.toLinearMap.restrict
        (p := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜))
        fun _ hA ↦ by rw [Unitary.conjStarAlgAut_symm]; exact IsSelfAdjoint.conjugate hA (star U))
      (LinearMap.ext fun A ↦ Subtype.ext (e.apply_symm_apply A.val))
      (LinearMap.ext fun A ↦ Subtype.ext (e.symm_apply_apply A.val))
    norm_map' A := by
      let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      have hsq := Matrix.frobenius_norm_sq_conj_unitary
        (star (U : Matrix (Fin p) (Fin p) 𝕜)) (A : Matrix (Fin p) (Fin p) 𝕜) (star U).property
      rwa [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at hsq }

/-- Ambient matrix coercion of `Matrix.UnitaryGroup.selfAdjointConj`. -/
@[simp] theorem coe_selfAdjointConj_apply (U : Matrix.unitaryGroup (Fin p) 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    (selfAdjointConj U A : Matrix (Fin p) (Fin p) 𝕜) =
      (U : Matrix (Fin p) (Fin p) 𝕜) * A * (U : Matrix (Fin p) (Fin p) 𝕜)ᴴ := by rfl

/-- Ambient matrix coercion of the inverse of `Matrix.UnitaryGroup.selfAdjointConj`. -/
@[simp] theorem coe_selfAdjointConj_symm_apply (U : Matrix.unitaryGroup (Fin p) 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ((selfAdjointConj U).symm A : Matrix (Fin p) (Fin p) 𝕜) =
      (U : Matrix (Fin p) (Fin p) 𝕜)ᴴ * A * (U : Matrix (Fin p) (Fin p) 𝕜) := by rfl

/-- Conjugating by the identity unitary matrix is the identity isometry. -/
@[simp] theorem selfAdjointConj_one :
    selfAdjointConj (1 : Matrix.unitaryGroup (Fin p) 𝕜) = LinearIsometryEquiv.refl ℝ _ :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext <| by simp

/-- Unitary conjugation is a left action of `Matrix.unitaryGroup`. -/
theorem selfAdjointConj_mul (U V : Matrix.unitaryGroup (Fin p) 𝕜) :
    selfAdjointConj (U * V) = (selfAdjointConj V).trans (selfAdjointConj U) :=
  LinearIsometryEquiv.ext fun A ↦ Subtype.ext <| by
    simpa only [coe_selfAdjointConj_apply, LinearIsometryEquiv.trans_apply,
      Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose] using
      Unitary.conjStarAlgAut_mul_apply (S := ℝ) U V (A : Matrix (Fin p) (Fin p) 𝕜)

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
@[simp] theorem selfAdjointConj_inv (U : Matrix.unitaryGroup (Fin p) 𝕜) :
    selfAdjointConj U⁻¹ = (selfAdjointConj U).symm :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext <| by
    rw [coe_selfAdjointConj_apply, coe_selfAdjointConj_symm_apply, ← Unitary.star_eq_inv,
      Unitary.coe_star, star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

end Algebra

end Matrix.UnitaryGroup

namespace TauCeti

open Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Real diagonal coordinates paired with strict upper-triangular entries. -/
abbrev SelfAdjointCoordinates (n : ℕ) (𝕜 : Type*) := (Fin n → ℝ) × (FinStrictUpper n → 𝕜)

/-- Read the real parts of the diagonal and the entries strictly above it. -/
def selfAdjointCoordinatesLinearMap :
    Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] SelfAdjointCoordinates n 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ (fun i ↦ RCLike.re (A i i), fun ij ↦ A ij.val.1 ij.val.2)
      map_add' := fun A B ↦ by ext <;> simp
      map_smul' := fun c A ↦ by ext <;> simp [RCLike.smul_re] }

/-- The diagonal coordinate is the real part of the corresponding diagonal entry. -/
@[simp] theorem selfAdjointCoordinatesLinearMap_fst (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    (selfAdjointCoordinatesLinearMap A).1 i = RCLike.re (A i i) := (rfl)

/-- The second component reads the corresponding strict upper entry. -/
@[simp] theorem selfAdjointCoordinatesLinearMap_snd (A : Matrix (Fin n) (Fin n) 𝕜)
    (ij : FinStrictUpper n) :
    (selfAdjointCoordinatesLinearMap A).2 ij = A ij.val.1 ij.val.2 := (rfl)

/-- On the self-adjoint subspace, the real diagonal and strict upper coordinates
determine the matrix by conjugate reflection. -/
def selfAdjointCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) ≃L[ℝ] SelfAdjointCoordinates n 𝕜 :=
  LinearEquiv.toContinuousLinearEquiv
    { selfAdjointCoordinatesLinearMap.toLinearMap.comp (selfAdjoint.submodule ℝ _).subtype with
      invFun := fun x ↦ ⟨Matrix.of fun i j ↦
        if hij : i < j then x.2 ⟨(i, j), hij⟩
        else if hji : j < i then star (x.2 ⟨(j, i), hji⟩)
        else (x.1 i : 𝕜), by
          refine Matrix.IsHermitian.ext fun i j ↦ ?_
          rcases lt_trichotomy i j with h | rfl | h
          · simp [h, h.not_gt]
          · simp
          · simp [h, h.not_gt]⟩
      left_inv := fun A ↦ Subtype.ext (by
        ext i j
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h]
        · simpa using RCLike.conj_eq_iff_re.mp ((selfAdjoint.isHermitian_coe A).apply i i)
        · simpa [h, h.not_gt] using (selfAdjoint.isHermitian_coe A).apply i j)
      right_inv := fun x ↦ by
        apply Prod.ext
        · funext i
          simp
        · funext ij
          simp [ij.property] }

/-- Evaluating the self-adjoint coordinate equivalence uses the ambient coordinate map. -/
theorem selfAdjointCoordinates_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)) :
    selfAdjointCoordinates A = selfAdjointCoordinatesLinearMap (A : Matrix (Fin n) (Fin n) 𝕜) :=
  (rfl)

/-- The inverse coordinate map restores the real diagonal. -/
@[simp] theorem coe_selfAdjointCoordinates_symm_apply_diag
    (x : SelfAdjointCoordinates n 𝕜) (i : Fin n) :
    (selfAdjointCoordinates.symm x : Matrix (Fin n) (Fin n) 𝕜) i i = (x.1 i : 𝕜) := by
  simp [selfAdjointCoordinates]

/-- The inverse coordinate map reads a strict upper entry from the second component. -/
@[simp] theorem coe_selfAdjointCoordinates_symm_apply_of_lt
    (x : SelfAdjointCoordinates n 𝕜) {i j : Fin n} (h : i < j) :
    (selfAdjointCoordinates.symm x : Matrix (Fin n) (Fin n) 𝕜) i j = x.2 ⟨(i, j), h⟩ := by
  simp [selfAdjointCoordinates, h]

/-- The lower entries of the inverse coordinate map are conjugate reflections. -/
@[simp] theorem coe_selfAdjointCoordinates_symm_apply_of_gt
    (x : SelfAdjointCoordinates n 𝕜) {i j : Fin n} (h : j < i) :
    (selfAdjointCoordinates.symm x : Matrix (Fin n) (Fin n) 𝕜) i j = star (x.2 ⟨(j, i), h⟩) := by
  simp [selfAdjointCoordinates, h, h.not_gt]

/-- The self-adjoint diagonal matrix with the given real diagonal entries, as the matrix whose
diagonal coordinates are these entries and whose strict upper coordinates vanish. -/
def selfAdjointDiagonal :
    (Fin n → ℝ) →L[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
  selfAdjointCoordinates.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (FinStrictUpper n → 𝕜))

/-- The self-adjoint diagonal has the given diagonal coordinates and no strict upper ones. -/
@[simp] theorem selfAdjointCoordinates_selfAdjointDiagonal (d : Fin n → ℝ) :
    selfAdjointCoordinates (selfAdjointDiagonal (𝕜 := 𝕜) d) = (d, 0) :=
  selfAdjointCoordinates.apply_symm_apply _

/-- Ambient matrix formula for the self-adjoint diagonal. -/
@[simp] theorem coe_selfAdjointDiagonal (d : Fin n → ℝ) :
    (selfAdjointDiagonal (𝕜 := 𝕜) d : Matrix (Fin n) (Fin n) 𝕜) = diagonal fun i ↦ (d i : 𝕜) := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [selfAdjointDiagonal, h, h.ne]
  · simp [selfAdjointDiagonal]
  · simp [selfAdjointDiagonal, h, h.ne']

/-- Coordinate change induced by conjugation with a unitary frame. -/
def unitaryConjCoordinates (U : unitaryGroup (Fin n) 𝕜) :
    SelfAdjointCoordinates n 𝕜 ≃L[ℝ] SelfAdjointCoordinates n 𝕜 :=
  selfAdjointCoordinates.symm.trans
    ((UnitaryGroup.selfAdjointConj U).toLinearEquiv.toContinuousLinearEquiv.trans
      selfAdjointCoordinates)

/-- The conjugation in self-adjoint matrix coordinates has absolute determinant one. -/
theorem abs_det_unitaryConjCoordinates (U : unitaryGroup (Fin n) 𝕜) :
    |(unitaryConjCoordinates U).toContinuousLinearMap.det| = 1 := by
  let e := (selfAdjointCoordinates (n := n) (𝕜 := 𝕜)).toLinearEquiv
  let T := UnitaryGroup.selfAdjointConj U
  have h : (unitaryConjCoordinates U).toContinuousLinearMap.toLinearMap =
      (e.symm.trans (T.toLinearEquiv.trans e)).toLinearMap := rfl
  rw [ContinuousLinearMap.det, h]
  -- Conjugating the real linear isometry by a coordinate equivalence preserves its determinant.
  have he : (e.symm.trans (T.toLinearEquiv.trans e)).toLinearMap =
      e.toLinearMap ∘ₗ T.toLinearEquiv.toLinearMap ∘ₗ e.symm.toLinearMap := rfl
  rw [he, LinearMap.det_conj]
  -- In an orthonormal basis the isometry has an orthogonal matrix, whose determinant is a unit.
  let b := stdOrthonormalBasis ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))
  rw [← LinearMap.det_toMatrix b.toBasis, ← Real.norm_eq_abs]
  exact CStarRing.norm_of_mem_unitary (det_of_mem_unitary (T.toMatrix_mem_unitaryGroup b b))

/-- The unitary coordinate change reads the coordinates of the unitary conjugate of the
self-adjoint matrix with the given coordinates. -/
theorem unitaryConjCoordinates_apply (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    unitaryConjCoordinates U x =
      selfAdjointCoordinatesLinearMap
        (Unitary.conjStarAlgAut ℝ _ U (selfAdjointCoordinates.symm x : Matrix (Fin n) (Fin n) 𝕜)) :=
  (rfl)

/-- Conjugating the coordinates of a self-adjoint matrix gives the coordinates of its
unitary conjugate. -/
theorem unitaryConjCoordinates_apply_selfAdjointCoordinatesLinearMap
    (U : unitaryGroup (Fin n) 𝕜) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)) :
    unitaryConjCoordinates U (selfAdjointCoordinatesLinearMap A.val) =
      selfAdjointCoordinatesLinearMap (Unitary.conjStarAlgAut ℝ _ U A.val) := by
  rw [← selfAdjointCoordinates_apply A, unitaryConjCoordinates_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end TauCeti
