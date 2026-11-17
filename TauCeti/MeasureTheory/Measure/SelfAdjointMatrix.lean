/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Frobenius inner product and unitary conjugation on self-adjoint matrices

Distributions on real symmetric (`𝕜 = ℝ`) and complex Hermitian (`𝕜 = ℂ`) matrices live on
Mathlib's real self-adjoint subspace `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)`. By
`Matrix.isHermitian_iff_isSelfAdjoint`, its elements are precisely the Hermitian `ι × ι` matrices
over `𝕜` (which over `ℝ` are the symmetric matrices).

This file equips `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)` uniformly for every `[RCLike 𝕜]` and
`[Fintype ι]` with the real Frobenius norm and inner product `⟪A, B⟫_ℝ = RCLike.re (A * B).trace`
while preserving the subtype uniformity and topology definitionally: the norm is induced from
`Matrix.frobeniusNormedAddCommGroup`, whose uniformity and topology are definitionally the product
ones, and `volume` is supplied by `measureSpaceOfInnerProductSpace`.

It also packages unitary (and, at `𝕜 = ℝ`, orthogonal) conjugation `A ↦ U * A * Uᴴ` as a single
real linear isometry equivalence `Matrix.UnitaryGroup.selfAdjointConj U`, proves its group laws and
trace invariance of powers, and shows that it preserves every additive Haar measure on the subspace
(including Frobenius `volume`, `TauCeti.symmetricLebesgue`, and `TauCeti.hermitianLebesgue`).

## Main declarations

* `TauCeti.selfAdjointMatrixNormedAddCommGroup`, `TauCeti.selfAdjointMatrixInnerProductSpace` —
  the real Frobenius structure on `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)` for `[RCLike 𝕜]`
  (with one-line syntactic specializations `*Real`/`*Complex` delegating directly to them so
  `rw` matches concrete `ℝ`/`ℂ` goals at `reducible` transparency with zero diamonds).
* `selfAdjoint.isHermitian_coe`, `selfAdjoint.conjTranspose_coe`, `selfAdjoint.coe_apply_conj` —
  self-adjointness and entry symmetries of elements of `selfAdjoint.submodule S (Matrix ι ι R)`.
* `selfAdjoint.coe_inner`, `selfAdjoint.inner_eq_re_trace_mul`,
  `selfAdjoint.norm_sq_eq_re_trace_sq` — the Frobenius inner product agrees with the ambient real
  Frobenius pairing and equals `RCLike.re (A * B).trace`.
* `Matrix.UnitaryGroup.selfAdjointConj` — unitary/orthogonal conjugation `A ↦ U * A * Uᴴ` as a
  real linear isometry equivalence of `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)`, together with its
  group laws (`selfAdjointConj_one`, `selfAdjointConj_mul`, `selfAdjointConj_symm`), power and
  trace invariance (`coe_selfAdjointConj_pow`, `trace_selfAdjointConj_pow`,
  `trace_selfAdjointConj`), and preservation of every additive Haar measure
  (`measurePreserving_selfAdjointConj`).
-/

public section

noncomputable section

open MeasureTheory Module
open scoped RealInnerProductSpace Matrix

namespace TauCeti

/-! ### The real Frobenius structure on the self-adjoint matrix subspace -/

section instances

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- The real self-adjoint matrix subspace carries the Frobenius norm induced from the ambient
matrices, with its metric rebuilt on the subtype uniformity so that the uniform and topological
structures agree definitionally with the subtype instances. -/
instance selfAdjointMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :=
  letI : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :=
    Submodule.normedAddCommGroup _
  -- Forces the uniformity field of the metric to be the subtype uniformity itself, so that
  -- downstream instance search unifies the two syntactically rather than only up to `rfl`.
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

/-- The real self-adjoint matrix subspace carries the real Frobenius inner product
`⟪A, B⟫_ℝ = ∑ i, ∑ j, ⟪A i j, B i j⟫_ℝ`, which equals `RCLike.re (A * B).trace`
(`selfAdjoint.inner_eq_re_trace_mul`). -/
instance selfAdjointMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :=
  letI : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix ι ι 𝕜) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix ι ι 𝕜) := Matrix.frobeniusInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)))
    norm_smul_le r A := norm_smul_le r (A : Matrix ι ι 𝕜)
    inner A B := ⟪(A : Matrix ι ι 𝕜), (B : Matrix ι ι 𝕜)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix ι ι 𝕜)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix ι ι 𝕜) ↑B
    add_left A B C := by
      rw [Submodule.coe_add]
      exact InnerProductSpace.add_left (𝕜 := ℝ) (A : Matrix ι ι 𝕜) ↑B ↑C
    smul_left A B r := Matrix.frobenius_inner_smul_left r (A : Matrix ι ι 𝕜) ↑B }

instance selfAdjointMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :=
  ESeminormedAddMonoid.toContinuousENorm

end instances

section concreteInstances

variable {ι : Type*} [Fintype ι]

/-- Syntactic specialization of `selfAdjointMatrixNormedAddCommGroup` at `𝕜 = ℝ`.
Because `selfAdjoint.submodule ℝ (Matrix ι ι ℝ)` embeds `AddCommMonoid ℝ` and `Module ℝ ℝ` directly
in its type expression, the polymorphic `[RCLike 𝕜]` instance carries `RCLike.toDenselyNormedField`
rather than `Real.instAddCommMonoid`, which prevents `rw`/`kabstract` from matching goals at
`reducible` transparency. Forwarding directly here eliminates the syntactic mismatch with zero
duplicated logic and zero diamonds (verified in `sanityChecks` below via
`with_reducible_and_instances rfl`). -/
instance selfAdjointMatrixNormedAddCommGroupReal :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)) :=
  selfAdjointMatrixNormedAddCommGroup

/-- Syntactic specialization of `selfAdjointMatrixInnerProductSpace` at `𝕜 = ℝ`; see
`selfAdjointMatrixNormedAddCommGroupReal`. -/
instance selfAdjointMatrixInnerProductSpaceReal :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)) :=
  selfAdjointMatrixInnerProductSpace

/-- Syntactic specialization of `selfAdjointMatrixNormedAddCommGroup` at `𝕜 = ℂ`; see
`selfAdjointMatrixNormedAddCommGroupReal`. -/
instance selfAdjointMatrixNormedAddCommGroupComplex :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :=
  selfAdjointMatrixNormedAddCommGroup

/-- Syntactic specialization of `selfAdjointMatrixInnerProductSpace` at `𝕜 = ℂ`; see
`selfAdjointMatrixNormedAddCommGroupReal`. -/
instance selfAdjointMatrixInnerProductSpaceComplex :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :=
  selfAdjointMatrixInnerProductSpace

end concreteInstances

section propInstances

variable {ι 𝕜 : Type*} [Finite ι] [RCLike 𝕜]

instance selfAdjointMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) := by
  have := Fintype.ofFinite ι
  exact SeminormedAddCommGroup.to_isUniformAddGroup

instance selfAdjointMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) := by
  have := Fintype.ofFinite ι
  exact secondCountable_of_proper

instance selfAdjointMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) := by
  have := Fintype.ofFinite ι
  exact FiniteDimensional.completeSpace ℝ _

/-- The measurable structure is the Borel structure of the subtype topology. Declared explicitly
so that instance search finds it regardless of which (definitionally equal) route it takes to
the topology. -/
instance selfAdjointMatrixBorelSpace [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) := by
  have := Fintype.ofFinite ι
  exact Subtype.borelSpace _

end propInstances

section sanityChecks

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- The uniformity of the Frobenius structure is definitionally the subtype uniformity. -/
example :
    (selfAdjointMatrixNormedAddCommGroup (ι := ι) (𝕜 := 𝕜)).toMetricSpace.toUniformSpace =
      (instUniformSpaceSubtype : UniformSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))) := by
  with_reducible_and_instances rfl

/-- The uniformity of the Frobenius structure induces the subtype topology definitionally. -/
example :
    (selfAdjointMatrixNormedAddCommGroup (ι := ι) (𝕜 := 𝕜)).toUniformSpace.toTopologicalSpace =
      (instTopologicalSpaceSubtype :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))) := by
  with_reducible_and_instances rfl

/-- The selected topology is the subtype topology. -/
example :
    (inferInstance : TopologicalSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))) =
      @instTopologicalSpaceSubtype _ _ inferInstance := by
  with_reducible_and_instances rfl

/-- `volume` is supplied by `measureSpaceOfInnerProductSpace`. -/
example [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    (inferInstance : MeasureSpace (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))) =
      measureSpaceOfInnerProductSpace :=
  rfl

/-- The `ℝ` specialization agrees with the polymorphic instance with zero diamonds. -/
example :
    (selfAdjointMatrixNormedAddCommGroupReal (ι := ι)) =
      selfAdjointMatrixNormedAddCommGroup := by
  with_reducible_and_instances rfl

/-- The `ℝ` inner-product specialization agrees with the polymorphic instance. -/
example :
    (selfAdjointMatrixInnerProductSpaceReal (ι := ι)) =
      selfAdjointMatrixInnerProductSpace := by
  with_reducible_and_instances rfl

/-- The `ℂ` specialization agrees with the polymorphic instance with zero diamonds. -/
example :
    (selfAdjointMatrixNormedAddCommGroupComplex (ι := ι)) =
      selfAdjointMatrixNormedAddCommGroup := by
  with_reducible_and_instances rfl

/-- The `ℂ` inner-product specialization agrees with the polymorphic instance. -/
example :
    (selfAdjointMatrixInnerProductSpaceComplex (ι := ι)) =
      selfAdjointMatrixInnerProductSpace := by
  with_reducible_and_instances rfl

end sanityChecks

end TauCeti

/-! ### Self-adjointness, entry symmetries, and the trace pairing -/

namespace selfAdjoint

/-- An element of `selfAdjoint.submodule S (Matrix ι ι R)` is a Hermitian matrix; over `ℝ` this
says that it is symmetric. -/
theorem isHermitian_coe {ι S R : Type*} [Semiring S] [StarMul S] [TrivialStar S]
    [AddCommMonoid R] [StarAddMonoid R] [Module S R] [StarModule S R]
    (A : selfAdjoint.submodule S (Matrix ι ι R)) :
    (A : Matrix ι ι R).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.2 A.2

/-- An element of `selfAdjoint.submodule S (Matrix ι ι R)` is fixed by conjugate transposition. -/
@[simp]
theorem conjTranspose_coe {ι S R : Type*} [Semiring S] [StarMul S] [TrivialStar S]
    [AddCommMonoid R] [StarAddMonoid R] [Module S R] [StarModule S R]
    (A : selfAdjoint.submodule S (Matrix ι ι R)) :
    (A : Matrix ι ι R)ᴴ = (A : Matrix ι ι R) :=
  (isHermitian_coe A).eq

/-- Swapping indices of a self-adjoint matrix applies `star` to the entry. -/
theorem coe_apply_conj {ι S R : Type*} [Semiring S] [StarMul S] [TrivialStar S]
    [AddCommMonoid R] [StarAddMonoid R] [Module S R] [StarModule S R]
    (A : selfAdjoint.submodule S (Matrix ι ι R)) (i j : ι) :
    (A : Matrix ι ι R) j i = star ((A : Matrix ι ι R) i j) :=
  ((isHermitian_coe A).apply j i).symm

open scoped Matrix.Norms.Frobenius in
/-- The real inner product on the self-adjoint matrix subspace is the ambient real Frobenius inner
product of the underlying matrices. -/
-- Mathlib's `Submodule.coe_inner` states this for the induced instance
-- `Submodule.innerProductSpace`; `TauCeti.selfAdjointMatrixInnerProductSpace` is built directly,
-- so that lemma does not apply to it.
@[simp]
theorem coe_inner {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    (A B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    ⟪A, B⟫ = ⟪(A : Matrix ι ι 𝕜), (B : Matrix ι ι 𝕜)⟫ :=
  (rfl)

/-- On the self-adjoint matrix subspace, the real Frobenius inner product is
`RCLike.re (A * B).trace`. -/
theorem inner_eq_re_trace_mul {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    (A B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    ⟪A, B⟫ = RCLike.re ((A : Matrix ι ι 𝕜) * (B : Matrix ι ι 𝕜)).trace := by
  let _ : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix ι ι 𝕜) := Matrix.frobeniusInnerProductSpace
  let _ : InnerProductSpace 𝕜 (Matrix ι ι 𝕜) := Matrix.frobeniusInnerProductSpace
  rw [coe_inner, Matrix.frobenius_inner_def]
  conv_rhs =>
    rw [← conjTranspose_coe A, ← Matrix.frobenius_inner_eq_trace_conjTranspose_mul,
      Matrix.frobenius_inner_def]
  simp only [map_sum]
  rfl

/-- The squared Frobenius norm of a self-adjoint matrix is `RCLike.re (A ^ 2).trace`. -/
theorem norm_sq_eq_re_trace_sq {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    ‖A‖ ^ 2 = RCLike.re ((A : Matrix ι ι 𝕜) ^ 2).trace := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_re_trace_mul, sq]

end selfAdjoint

/-! ### Unitary conjugation on the self-adjoint matrix subspace -/

namespace Matrix.UnitaryGroup

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Unitary (and, for `𝕜 = ℝ`, orthogonal) conjugation `A ↦ U * A * Uᴴ` as a real linear isometry
equivalence of `selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)`. -/
def selfAdjointConj (U : Matrix.unitaryGroup ι 𝕜) :
    selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) where
  toFun A :=
    ⟨(U : Matrix ι ι 𝕜) * (A : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)ᴴ,
      Matrix.isHermitian_iff_isSelfAdjoint.1
        (Matrix.isHermitian_mul_mul_conjTranspose _ (selfAdjoint.isHermitian_coe A))⟩
  invFun A :=
    ⟨(U : Matrix ι ι 𝕜)ᴴ * (A : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜),
      Matrix.isHermitian_iff_isSelfAdjoint.1
        (Matrix.isHermitian_conjTranspose_mul_mul _ (selfAdjoint.isHermitian_coe A))⟩
  map_add' A B := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' r A := Subtype.ext (by simp)
  left_inv A := Subtype.ext (by
    have hU : (U : Matrix ι ι 𝕜)ᴴ * (U : Matrix ι ι 𝕜) = 1 :=
      Matrix.mem_unitaryGroup_iff'.1 U.2
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix ι ι 𝕜)ᴴ, hU, one_mul, mul_one])
  right_inv A := Subtype.ext (by
    have hU : (U : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.1 U.2
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix ι ι 𝕜), hU, one_mul, mul_one])
  norm_map' A := by
    let _ : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.frobeniusNormedAddCommGroup
    have hU' : (U : Matrix ι ι 𝕜)ᴴ ∈ Matrix.unitaryGroup ι 𝕜 := by
      simpa [Matrix.star_eq_conjTranspose] using U⁻¹.2
    have hsq := Matrix.frobenius_norm_sq_conj_unitary
      (U : Matrix ι ι 𝕜)ᴴ (A : Matrix ι ι 𝕜) hU'
    rw [Matrix.conjTranspose_conjTranspose] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Coercing `selfAdjointConj U A` yields `U * A * Uᴴ`. -/
@[simp]
theorem coe_selfAdjointConj_apply (U : Matrix.unitaryGroup ι 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    (selfAdjointConj U A : Matrix ι ι 𝕜) =
      (U : Matrix ι ι 𝕜) * (A : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)ᴴ :=
  (rfl)

/-- Coercing `(selfAdjointConj U).symm A` yields `Uᴴ * A * U`. -/
theorem coe_selfAdjointConj_symm_apply (U : Matrix.unitaryGroup ι 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    ((selfAdjointConj U).symm A : Matrix ι ι 𝕜) =
      (U : Matrix ι ι 𝕜)ᴴ * (A : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜) :=
  (rfl)

/-- Conjugation by the identity matrix is the identity equivalence. -/
@[simp]
theorem selfAdjointConj_one :
    selfAdjointConj (1 : Matrix.unitaryGroup ι 𝕜) = LinearIsometryEquiv.refl ℝ _ := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp

/-- Conjugation respects group multiplication in `Matrix.unitaryGroup`. -/
theorem selfAdjointConj_mul (U V : Matrix.unitaryGroup ι 𝕜) :
    selfAdjointConj (U * V) = (selfAdjointConj V).trans (selfAdjointConj U) := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The inverse of unitary conjugation by `U` is conjugation by `U⁻¹`. -/
@[simp]
theorem selfAdjointConj_symm (U : Matrix.unitaryGroup ι 𝕜) :
    (selfAdjointConj U).symm = selfAdjointConj U⁻¹ := by
  refine LinearIsometryEquiv.ext fun A => Subtype.ext ?_
  simp [coe_selfAdjointConj_symm_apply, Matrix.star_eq_conjTranspose]

/-- Powers commute with unitary conjugation: `(U * A * Uᴴ) ^ k = U * A ^ k * Uᴴ`. -/
theorem coe_selfAdjointConj_pow (U : Matrix.unitaryGroup ι 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) (k : ℕ) :
    (selfAdjointConj U A : Matrix ι ι 𝕜) ^ k =
      (U : Matrix ι ι 𝕜) * (A : Matrix ι ι 𝕜) ^ k * (U : Matrix ι ι 𝕜)ᴴ := by
  rw [coe_selfAdjointConj_apply]
  simpa [Matrix.star_eq_conjTranspose] using (Unitary.toUnits U).conj_pow (A : Matrix ι ι 𝕜) k

/-- Unitary conjugation preserves the trace of every power of a self-adjoint matrix. -/
theorem trace_selfAdjointConj_pow (U : Matrix.unitaryGroup ι 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) (k : ℕ) :
    ((selfAdjointConj U A : Matrix ι ι 𝕜) ^ k).trace = ((A : Matrix ι ι 𝕜) ^ k).trace := by
  have hU : (U : Matrix ι ι 𝕜)ᴴ * (U : Matrix ι ι 𝕜) = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  rw [coe_selfAdjointConj_pow, Matrix.trace_mul_cycle, hU, one_mul]

/-- Unitary conjugation preserves the trace of a self-adjoint matrix. -/
theorem trace_selfAdjointConj (U : Matrix.unitaryGroup ι 𝕜)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    (selfAdjointConj U A : Matrix ι ι 𝕜).trace = (A : Matrix ι ι 𝕜).trace := by
  simpa only [pow_one] using trace_selfAdjointConj_pow U A 1

/-- Unitary conjugation preserves every additive Haar measure on the real self-adjoint matrix
subspace (in particular Frobenius `volume`, `TauCeti.symmetricLebesgue`, and
`TauCeti.hermitianLebesgue`). -/
theorem measurePreserving_selfAdjointConj [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (U : Matrix.unitaryGroup ι 𝕜)
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))) [μ.IsAddHaarMeasure] :
    MeasurePreserving (selfAdjointConj U) μ μ :=
  (selfAdjointConj U).measurePreserving_addHaar μ

end Matrix.UnitaryGroup
