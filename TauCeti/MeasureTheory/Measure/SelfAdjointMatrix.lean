/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Frobenius geometry and unitary conjugation on self-adjoint matrix subspaces

For `[RCLike 𝕜]`, `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is the real symmetric
subspace when `𝕜 = ℝ` and the complex Hermitian subspace when `𝕜 = ℂ`. This file equips it
uniformly over `𝕜` with the ambient Frobenius norm and real inner product
`⟪A, B⟫ = RCLike.re tr(B * A)` while keeping the subtype topology and uniformity definitionally
equal to the induced product ones, and builds unitary conjugation
`Matrix.UnitaryGroup.selfAdjointConj` as a real linear isometry equivalence preserving `volume`.

## Main declarations

* `TauCeti.selfAdjointMatrixNormedAddCommGroup`, `TauCeti.selfAdjointMatrixInnerProductSpace` —
  Frobenius norm and real trace inner product on the self-adjoint matrix subspace over `𝕜`.
* `selfAdjoint.coe_inner`, `selfAdjoint.isHermitian_coe`, `selfAdjoint.conjTranspose_coe`,
  `selfAdjoint.inner_eq_rclike_re_trace_mul`, `selfAdjoint.norm_sq_eq_rclike_re_trace_sq`.
* `Matrix.UnitaryGroup.selfAdjointConj` and `measurePreserving_selfAdjointConj_volume`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate Matrix RealInnerProductSpace

namespace TauCeti

section instances
variable (p : ℕ) (𝕜 : Type*) [RCLike 𝕜]

/-! Scoped in `TauCeti.SelfAdjointMatrix` (and re-exported globally at `ℝ` and `ℂ`) so the global
`ℝ` instance elaborates `selfAdjoint.submodule` with `Real.instAddCommMonoid` rather than
`RCLike.toNormedAddCommGroup` and avoids `[RCLike ?𝕜]` branching on `ESeminormedAddMonoid`. -/

/-- The real self-adjoint matrix subspace over `𝕜` carries the Frobenius norm induced from ambient
matrices, rebuilt on the subtype uniformity so uniform and topological structures match. -/
@[expose, instance_reducible] def selfAdjointMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :=
    Submodule.normedAddCommGroup _
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

attribute [local instance] selfAdjointMatrixNormedAddCommGroup

/-- The real self-adjoint matrix subspace over `𝕜` carries the real Frobenius inner product of the
underlying matrices (`selfAdjoint.inner_eq_rclike_re_trace_mul`). -/
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

/-- Borel measurable structure on the self-adjoint matrix subspace over `𝕜`. -/
theorem selfAdjointMatrixBorelSpace [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) := Subtype.borelSpace _

namespace SelfAdjointMatrix
attribute [scoped instance] selfAdjointMatrixNormedAddCommGroup selfAdjointMatrixInnerProductSpace
  selfAdjointMatrixIsUniformAddGroup selfAdjointMatrixSecondCountableTopology
  selfAdjointMatrixCompleteSpace selfAdjointMatrixContinuousENorm selfAdjointMatrixBorelSpace
end SelfAdjointMatrix
end instances
end TauCeti

open scoped TauCeti.SelfAdjointMatrix

namespace selfAdjoint

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

open scoped Matrix.Norms.Frobenius in
/-- The inner product on `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is the real Frobenius
inner product of the underlying matrices. -/
@[simp] theorem coe_inner (A B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ⟪A, B⟫ = ⟪(A : Matrix (Fin p) (Fin p) 𝕜), (B : Matrix (Fin p) (Fin p) 𝕜)⟫ := (rfl)

/-- Every element of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is a Hermitian matrix. -/
theorem isHermitian_coe (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    (A : Matrix (Fin p) (Fin p) 𝕜).IsHermitian := A.2

/-- Every element of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` equals its conjugate
transpose. -/
@[simp] theorem conjTranspose_coe (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    (A : Matrix (Fin p) (Fin p) 𝕜)ᴴ = (A : Matrix (Fin p) (Fin p) 𝕜) := (isHermitian_coe A).eq

/-- Swapping indices conjugates the entry of an element of the self-adjoint matrix subspace. -/
theorem coe_apply_conj (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) (i j : Fin p) :
    conj ((A : Matrix (Fin p) (Fin p) 𝕜) j i) = (A : Matrix (Fin p) (Fin p) 𝕜) i j := by
  simpa using (isHermitian_coe A).apply i j

/-- On `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)`, the real Frobenius inner product is
`RCLike.re tr(Θ * A)`. -/
theorem inner_eq_rclike_re_trace_mul
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ⟪A, Θ⟫ = RCLike.re ((Θ : Matrix (Fin p) (Fin p) 𝕜) * (A : Matrix (Fin p) (Fin p) 𝕜)).trace := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner, Matrix.frobenius_inner_def]
  simp only [real_inner_eq_re_inner, RCLike.inner_apply', Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [coe_apply_conj A j i, mul_comm]

/-- The squared Frobenius norm of `A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` is
`RCLike.re tr(A ^ 2)`. -/
theorem norm_sq_eq_rclike_re_trace_sq
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) :
    ‖A‖ ^ 2 = RCLike.re (((A : Matrix (Fin p) (Fin p) 𝕜) ^ 2).trace) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_rclike_re_trace_mul, sq]

end selfAdjoint

namespace Matrix.UnitaryGroup

section Algebra

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

/-- Unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence of
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)`. Over `𝕜 = ℝ` this is orthogonal conjugation
`A ↦ U * A * Uᵀ`; over `𝕜 = ℂ` it is complex unitary conjugation. -/
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
      (LinearMap.ext fun A ↦ Subtype.ext (e.apply_symm_apply A.1))
      (LinearMap.ext fun A ↦ Subtype.ext (e.symm_apply_apply A.1))
    norm_map' A := by
      let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) 𝕜) := Matrix.frobeniusNormedAddCommGroup
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      have hsq := Matrix.frobenius_norm_sq_conj_unitary
        (star (U : Matrix (Fin p) (Fin p) 𝕜)) (A : Matrix (Fin p) (Fin p) 𝕜) (star U).2
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
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext <| by
    rw [coe_selfAdjointConj_apply, OneMemClass.coe_one, Matrix.conjTranspose_one, one_mul, mul_one]
    rfl

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

/-- Unitary conjugation preserves Frobenius `volume` on
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)`. -/
theorem measurePreserving_selfAdjointConj_volume {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] {p : ℕ} (U : Matrix.unitaryGroup (Fin p) 𝕜) :
    MeasurePreserving (selfAdjointConj U) volume volume := (selfAdjointConj U).measurePreserving

end Matrix.UnitaryGroup
