/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Analysis.Matrix.UnitaryGroup.SchurHorn
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Subgroup.Unitary
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Geometry.Lie.Adjoint.Units.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# The coadjoint orbits of `U(n)` as Hermitian eigenvalue orbits

The Lie algebra `𝔲(n)` of the unitary group (`TauCeti.UnitaryGroup.lieAlgebra n`, the Lie algebra
of the unitary subgroup of the real Lie group `GL(n, ℂ)`) consists, in matrix coordinates
(`TauCeti.UnitaryGroup.toMatrix`), of the skew-Hermitian matrices; it has real dimension `n²`
(`TauCeti.UnitaryGroup.finrank_lieAlgebra`). This file identifies its dual with the Hermitian
matrices and computes the coadjoint action, orbits and Kirillov–Kostant–Souriau form of `U(n)` in
these terms, with the pairing fixed as

`⟨H, X⟩ = -i tr (H X)`

for Hermitian `H` and skew-Hermitian `X`, which is real. Every functional on `𝔲(n)` is
`ν_H = ⟨H, ·⟩` for a unique Hermitian `H` (`TauCeti.UnitaryGroup.hermitianDualEquiv`). In this
model:

* the coadjoint action of `X ∈ 𝔲(n)`, with matrix `A`, is the commutator, `⁅X, ν_H⁆ = ν_[A, H]`
  (`TauCeti.UnitaryGroup.lie_hermitianDualEquiv`), so the coadjoint stabilizer of `ν_H` is the
  commutant of `H` (`TauCeti.UnitaryGroup.mem_lieAnnihilator_hermitianDualEquiv_iff`), and the
  KKS form is `ω_H([X], [Y]) = re (-i tr (H [A, B]))`
  (`TauCeti.UnitaryGroup.kksForm_hermitianDualEquiv_mk`);
* the coadjoint action of `U ∈ U(n)` is conjugation, `Ad*_U ν_H = ν_(U H U*)`
  (`TauCeti.UnitaryGroup.coadjointRepresentation_hermitianDualEquiv`), so **the coadjoint orbit of
  `ν_H` is the Hermitian eigenvalue orbit** of the Hermitian matrices with the same eigenvalues
  as `H`, counted with multiplicity
  (`TauCeti.UnitaryGroup.range_coadjointRepresentation_hermitianDualEquiv`).

The diagonal maximal torus has Lie algebra the matrices `diag(i θ)`
(`TauCeti.UnitaryGroup.torusCoords`), and in these real coordinates `θ` the restriction of `ν_H` to
it is the diagonal of `H`: **the diagonal projection is the moment map of the torus**
(`TauCeti.UnitaryGroup.torusMomentMap_hermitianDualEquiv`). The Schur–Horn theorem then says that
the image of a coadjoint orbit under this moment map is the permutohedron of the eigenvalues
(`TauCeti.UnitaryGroup.torusMomentMap_image_range_coadjointRepresentation`). For a real diagonal
matrix `diag(d)` with distinct entries the coadjoint stabilizer of `ν_diag(d)` is exactly the torus
Lie algebra (`TauCeti.UnitaryGroup.toSubmodule_lieAnnihilator_hermitianDualEquiv_diagonal`), so
the algebraic tangent model `𝔲(n) ⧸ 𝔲(n)_ν` of such a regular orbit has dimension `n² - n`, the
dimension of the complete flag manifold `U(n) / T`
(`TauCeti.UnitaryGroup.finrank_quotient_lieAnnihilator_hermitianDualEquiv_diagonal_add`).

## Main definitions

* `TauCeti.UnitaryGroup.hermitianDualEquiv`: the identification of the Hermitian matrices with
  `𝔲(n)*`.
* `TauCeti.UnitaryGroup.adjointRepresentation`, `TauCeti.UnitaryGroup.coadjointRepresentation`:
  the adjoint and coadjoint representations of `U(n)`.
* `TauCeti.UnitaryGroup.torusCoords`, `TauCeti.UnitaryGroup.torusMomentMap`: the coordinates of the
  Lie algebra of the diagonal torus and the restriction of functionals to it.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, American
  Mathematical Society, 2004, Section 1.2 (coadjoint orbits and the KKS form).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Inventiones
  Mathematicae 67 (1982), 491–513 (coadjoint orbits of `U(n)` and the Schur–Horn theorem as a
  moment-map image).
-/

public section

noncomputable section

open Module Complex
open scoped ComplexOrder ContDiff Manifold Matrix Matrix.Norms.Operator

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

/-- The element of `𝔲(n)` with matrix coordinates `i H` for a Hermitian matrix `H`. -/
private theorem exists_toMatrix_eq_I_smul (H : selfAdjoint (Matrix n n ℂ)) :
    ∃ X, toMatrix n X = I • (H : Matrix n n ℂ) := by
  rw [exists_toMatrix_eq_iff, ← Matrix.star_eq_conjTranspose, ← skewAdjoint.mem_iff,
    Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint]
  exact H.2

/-- The trace pairing `H, A ↦ re (-i tr (H A))` of Hermitian and skew-Hermitian matrices. -/
private def tracePairing : selfAdjoint (Matrix n n ℂ) →ₗ[ℝ] Dual ℝ (lieAlgebra n) :=
  LinearMap.mk₂ ℝ (fun H X ↦ (-I * ((H : Matrix n n ℂ) * toMatrix n X).trace).re)
    (fun H H' X ↦ by simp [add_mul, Matrix.trace_add, mul_add])
    (fun c H X ↦ by
      simp [Matrix.trace_smul, Complex.real_smul, mul_left_comm])
    (fun H X X' ↦ by simp [mul_add, Matrix.trace_add])
    (fun c H X ↦ by
      simp [Matrix.trace_smul, Complex.real_smul, mul_left_comm])

private theorem tracePairing_apply (H : selfAdjoint (Matrix n n ℂ)) (X : lieAlgebra n) :
    tracePairing H X = (-I * ((H : Matrix n n ℂ) * toMatrix n X).trace).re :=
  rfl

private theorem tracePairing_injective : Function.Injective (tracePairing (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro H hH
  obtain ⟨X, hX⟩ := exists_toMatrix_eq_I_smul H
  have h := LinearMap.congr_fun hH X
  rw [tracePairing_apply, hX, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
    neg_mul, I_mul_I, neg_neg, one_mul, LinearMap.zero_apply] at h
  -- The trace of `H H = Hᴴ H` is real, and its real part vanishes.
  have hreal : starRingEnd ℂ ((H : Matrix n n ℂ) * H).trace = ((H : Matrix n n ℂ) * H).trace := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      ← Matrix.star_eq_conjTranspose, H.2.star_eq]
  have h0 : ((H : Matrix n n ℂ) * H).trace = 0 :=
    Complex.ext h (Complex.conj_eq_iff_im.1 hreal)
  have h0' : ((H : Matrix n n ℂ)ᴴ * H).trace = 0 := by
    rwa [← Matrix.star_eq_conjTranspose, H.2.star_eq]
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0')

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
  have := (hermitianEquiv (n := n)).finiteDimensional
  have := (skewAdjointEquiv (n := n)).finiteDimensional
  have h := (StarModule.decomposeProdAdjoint ℝ (Matrix n n ℂ)).finrank_eq
  rw [Module.finrank_matrix, Complex.finrank_real_complex, Module.finrank_prod,
    ← hermitianEquiv.finrank_eq, ← skewAdjointEquiv.finrank_eq] at h
  linarith

private theorem tracePairing_bijective : Function.Bijective (tracePairing (n := n)) := by
  have : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    hermitianEquiv.finiteDimensional
  refine ⟨tracePairing_injective, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 tracePairing_injective
  rw [Subspace.dual_finrank_eq, hermitianEquiv.finrank_eq]

variable (n) in
/-- **The Hermitian model of `𝔲(n)*`.** A Hermitian matrix `H` defines the functional
`ν_H(X) = re (-i tr (H X))` on `𝔲(n)`, where `X` is read as a skew-Hermitian matrix through
`TauCeti.UnitaryGroup.toMatrix`; since `tr (H X)` is purely imaginary, `-i tr (H X)` is already
real. Every functional on `𝔲(n)` is `ν_H` for a unique Hermitian `H`. -/
def hermitianDualEquiv : selfAdjoint (Matrix n n ℂ) ≃ₗ[ℝ] Dual ℝ (lieAlgebra n) :=
  LinearEquiv.ofBijective tracePairing tracePairing_bijective

/-- The functional `ν_H` evaluates `X ∈ 𝔲(n)` as `re (-i tr (H X))`. -/
@[simp]
theorem hermitianDualEquiv_apply (H : selfAdjoint (Matrix n n ℂ)) (X : lieAlgebra n) :
    hermitianDualEquiv n H X = (-I * ((H : Matrix n n ℂ) * toMatrix n X).trace).re :=
  (rfl)

/-- The pairing `-i tr (H X)` of a Hermitian matrix with a skew-Hermitian one is real, so the
functional `ν_H` is the whole complex number `-i tr (H X)`. -/
theorem ofReal_hermitianDualEquiv_apply (H : selfAdjoint (Matrix n n ℂ)) (X : lieAlgebra n) :
    (hermitianDualEquiv n H X : ℂ) = -I * ((H : Matrix n n ℂ) * toMatrix n X).trace := by
  have ht : starRingEnd ℂ ((H : Matrix n n ℂ) * toMatrix n X).trace =
      -((H : Matrix n n ℂ) * toMatrix n X).trace := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      conjTranspose_toMatrix, ← Matrix.star_eq_conjTranspose, H.2.star_eq, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.trace_mul_comm]
  rw [hermitianDualEquiv_apply]
  exact Complex.conj_eq_iff_re.1 (by rw [map_mul, map_neg, Complex.conj_I, neg_neg, ht, mul_neg,
    neg_mul])

/-! ### The infinitesimal coadjoint action and the KKS form -/

/-- The commutator `[A, H] = A H - H A` of the matrix `A` of `X ∈ 𝔲(n)` with a Hermitian matrix
`H`, which is again Hermitian. In the Hermitian model it is the coadjoint action of `X` on `ν_H`
(`TauCeti.UnitaryGroup.lie_hermitianDualEquiv`). -/
def lieHermitian (X : lieAlgebra n) (H : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  ⟨toMatrix n X * H - H * toMatrix n X, by
    rw [selfAdjoint.mem_iff, star_sub, star_mul, star_mul, H.2.star_eq,
      Matrix.star_eq_conjTranspose, conjTranspose_toMatrix, Matrix.mul_neg, Matrix.neg_mul,
      sub_neg_eq_add, neg_add_eq_sub]⟩

@[simp]
theorem coe_lieHermitian (X : lieAlgebra n) (H : selfAdjoint (Matrix n n ℂ)) :
    (lieHermitian X H : Matrix n n ℂ) = toMatrix n X * H - H * toMatrix n X :=
  (rfl)

/-- The matrix coordinates of a bracket in `𝔲(n)` are the commutator of the matrix coordinates. -/
theorem toMatrix_lie (X Y : lieAlgebra n) :
    toMatrix n ⁅X, Y⁆ = toMatrix n X * toMatrix n Y - toMatrix n Y * toMatrix n X := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]

/-- **The coadjoint action in the Hermitian model** is the commutator: `⁅X, ν_H⁆ = ν_[A, H]`, where
`A` is the skew-Hermitian matrix of `X`. -/
@[simp]
theorem lie_hermitianDualEquiv (X : lieAlgebra n) (H : selfAdjoint (Matrix n n ℂ)) :
    ⁅X, hermitianDualEquiv n H⁆ = hermitianDualEquiv n (lieHermitian X H) := by
  refine LinearMap.ext fun Y ↦ ?_
  set A := toMatrix n X
  set B := toMatrix n Y
  have key : ((H : Matrix n n ℂ) * (A * B - B * A)).trace = -((A * H - H * A) * B).trace := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_cycle (H : Matrix n n ℂ) B A]
    ring
  rw [Module.Dual.lie_apply, hermitianDualEquiv_apply, hermitianDualEquiv_apply, toMatrix_lie,
    coe_lieHermitian, key, mul_neg, Complex.neg_re, neg_neg]

/-- **The coadjoint stabilizer in the Hermitian model** is the commutant: `X ∈ 𝔲(n)` fixes `ν_H`
infinitesimally exactly when its matrix commutes with `H`. -/
theorem mem_lieAnnihilator_hermitianDualEquiv_iff {X : lieAlgebra n}
    {H : selfAdjoint (Matrix n n ℂ)} :
    X ∈ lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n H) ↔
      Commute (toMatrix n X) (H : Matrix n n ℂ) := by
  rw [mem_lieAnnihilator, lie_hermitianDualEquiv, LinearEquiv.map_eq_zero_iff, Subtype.ext_iff,
    coe_lieHermitian, ZeroMemClass.coe_zero, sub_eq_zero]
  exact Iff.rfl

/-- **The Kirillov–Kostant–Souriau form in the Hermitian model**:
`ω_H([X], [Y]) = re (-i tr (H [A, B]))`, where `A` and `B` are the matrices of `X` and `Y`. -/
theorem kksForm_hermitianDualEquiv_mk (H : selfAdjoint (Matrix n n ℂ)) (X Y : lieAlgebra n) :
    (hermitianDualEquiv n H).kksForm (Submodule.Quotient.mk X) (Submodule.Quotient.mk Y) =
      (-I * ((H : Matrix n n ℂ) *
        (toMatrix n X * toMatrix n Y - toMatrix n Y * toMatrix n X)).trace).re := by
  rw [Module.Dual.kksForm_mk, hermitianDualEquiv_apply, toMatrix_lie]

/-! ### The adjoint and coadjoint representations of `U(n)` -/

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

variable (n) in
/-- The **coadjoint representation** of `U(n)` on the dual `𝔲(n)*` of its Lie algebra:
`(Ad*_U ν)(X) = ν (Ad_{U⁻¹} X)`, the dual of the adjoint representation. -/
def coadjointRepresentation :
    Representation ℝ (Matrix.unitaryGroup n ℂ) (Dual ℝ (lieAlgebra n)) :=
  (adjointRepresentation n).toRepresentation.dual

/-- The coadjoint action evaluates as `(Ad*_U ν)(X) = ν (Ad_{U⁻¹} X)`. -/
theorem coadjointRepresentation_apply (U : Matrix.unitaryGroup n ℂ) (ν : Dual ℝ (lieAlgebra n))
    (X : lieAlgebra n) :
    coadjointRepresentation n U ν X = ν (adjointRepresentation n U⁻¹ X) :=
  (rfl)

/-- **The coadjoint action of `U(n)` in the Hermitian model** is conjugation:
`Ad*_U ν_H = ν_(U H U*)`. -/
@[simp]
theorem coadjointRepresentation_hermitianDualEquiv (U : Matrix.unitaryGroup n ℂ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    coadjointRepresentation n U (hermitianDualEquiv n H) =
      hermitianDualEquiv n ⟨U * H * star (U : Matrix n n ℂ), H.2.conjugate _⟩ := by
  refine LinearMap.ext fun X ↦ ?_
  rw [coadjointRepresentation_apply, hermitianDualEquiv_apply, hermitianDualEquiv_apply,
    toMatrix_adjointRepresentation]
  rw [Matrix.UnitaryGroup.inv_val, star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm _ (U : Matrix n n ℂ), ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-! ### Orbits -/

/-- **The coadjoint orbits of `U(n)` are the Hermitian eigenvalue orbits**: the orbit of `ν_H` is
the set of `ν_K` for the Hermitian matrices `K` with the same characteristic polynomial as `H`,
that is, with the same eigenvalues counted with multiplicity. -/
theorem range_coadjointRepresentation_hermitianDualEquiv (H : selfAdjoint (Matrix n n ℂ)) :
    Set.range (fun U ↦ coadjointRepresentation n U (hermitianDualEquiv n H)) =
      hermitianDualEquiv n ''
        {K | (K : Matrix n n ℂ).charpoly = (H : Matrix n n ℂ).charpoly} := by
  ext ν
  obtain ⟨K, rfl⟩ := (hermitianDualEquiv n).surjective ν
  simp only [Set.mem_range, coadjointRepresentation_hermitianDualEquiv,
    (hermitianDualEquiv n).injective.eq_iff, (hermitianDualEquiv n).injective.mem_set_image,
    Set.mem_ofPred_eq, Subtype.ext_iff]
  exact (IsSelfAdjoint.isHermitian H.2).exists_unitaryGroup_mul_mul_star_eq_iff
    (IsSelfAdjoint.isHermitian K.2)

/-! ### The diagonal torus and its moment map -/

/-- The diagonal matrix `diag(i θ)` of a real vector `θ`. -/
private def diagonalI : (n → ℝ) →ₗ[ℝ] Matrix n n ℂ where
  toFun θ := Matrix.diagonal fun j ↦ (θ j : ℂ) * I
  map_add' θ θ' := by simp [add_mul, Matrix.diagonal_add]
  map_smul' c θ := by
    ext i j
    by_cases h : i = j <;> simp [h, Complex.real_smul, mul_assoc]

private theorem diagonalI_mem (θ : n → ℝ) :
    (Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).symm (diagonalI θ) ∈ lieAlgebra n := by
  rw [Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagonalI, Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply]
  · simp [diagonalI, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h),
      Matrix.conjTranspose_apply]

variable (n) in
/-- The coordinates `θ ↦ diag(i θ)` of the Lie algebra of the diagonal maximal torus of `U(n)`:
the element of `𝔲(n)` whose matrix is the diagonal matrix with entries `i θⱼ`. Its matrix
exponential is `diag(e^(i θⱼ))`, a point of the diagonal torus `TauCeti.unitaryTorus n`, so the
torus has period `2π` in each coordinate. -/
def torusCoords : (n → ℝ) →ₗ[ℝ] lieAlgebra n :=
  ((Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).symm.toLinearMap.comp diagonalI).codRestrict
    (lieAlgebra n).toSubmodule diagonalI_mem

/-- The matrix of `torusCoords θ` is `diag(i θ)`. -/
@[simp]
theorem toMatrix_torusCoords (θ : n → ℝ) :
    toMatrix n (torusCoords n θ) = Matrix.diagonal fun j ↦ (θ j : ℂ) * I := by
  rw [toMatrix_apply, ← Lie.unitsLieAlgebraLieEquiv_apply]
  exact (Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).apply_symm_apply (diagonalI θ)

/-- The functional `ν_H` pairs the torus element `diag(i θ)` with `∑ⱼ re (Hⱼⱼ) θⱼ`. -/
theorem hermitianDualEquiv_torusCoords (H : selfAdjoint (Matrix n n ℂ)) (θ : n → ℝ) :
    hermitianDualEquiv n H (torusCoords n θ) = ∑ j, ((H : Matrix n n ℂ) j j).re * θ j := by
  rw [hermitianDualEquiv_apply, toMatrix_torusCoords, Matrix.trace, Finset.mul_sum,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal]
  simp [mul_comm, mul_left_comm, mul_assoc]

variable (n) in
/-- The **moment map of the diagonal torus** on `𝔲(n)*`: the restriction of a functional to the
torus Lie algebra, read in the coordinates `θ` of `TauCeti.UnitaryGroup.torusCoords` by pairing
with the standard basis. Composed with the inclusion of a coadjoint orbit into `𝔲(n)*`, which is
the moment map of the coadjoint action, it is the moment map of the action of the diagonal torus on
that orbit. -/
def torusMomentMap : Dual ℝ (lieAlgebra n) →ₗ[ℝ] (n → ℝ) :=
  LinearMap.pi fun j ↦ LinearMap.applyₗ (torusCoords n (Pi.single j 1))

@[simp]
theorem torusMomentMap_apply (ν : Dual ℝ (lieAlgebra n)) (j : n) :
    torusMomentMap n ν j = ν (torusCoords n (Pi.single j 1)) :=
  (rfl)

/-- **The diagonal projection is the moment map of the diagonal torus**: in the Hermitian model,
`ν_H` restricts on the torus Lie algebra to the real parts of the diagonal entries of `H`. -/
@[simp]
theorem torusMomentMap_hermitianDualEquiv (H : selfAdjoint (Matrix n n ℂ)) :
    torusMomentMap n (hermitianDualEquiv n H) = fun j ↦ ((H : Matrix n n ℂ) j j).re := by
  funext j
  rw [torusMomentMap_apply, hermitianDualEquiv_torusCoords, Finset.sum_eq_single j
    (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, mul_zero]) (by simp), Pi.single_eq_same, mul_one]

/-- **The Schur–Horn theorem as a moment-map image**: the image of the coadjoint orbit of `ν_H`
under the moment map of the diagonal torus is the permutohedron of the eigenvalues of `H`, the
convex hull of their rearrangements. -/
theorem torusMomentMap_image_range_coadjointRepresentation (H : selfAdjoint (Matrix n n ℂ)) :
    torusMomentMap n '' Set.range (fun U ↦ coadjointRepresentation n U (hermitianDualEquiv n H)) =
      convexHull ℝ
        (Set.range fun σ : Equiv.Perm n ↦ (IsSelfAdjoint.isHermitian H.2).eigenvalues ∘ σ) := by
  rw [← Set.range_comp, ← (IsSelfAdjoint.isHermitian H.2).range_re_diag_unitary_mul_mul_star]
  congr 1
  funext U
  rw [Function.comp_apply, coadjointRepresentation_hermitianDualEquiv,
    torusMomentMap_hermitianDualEquiv]
  rfl

omit [Fintype n] in
variable (n) in
/-- The real diagonal matrix `diag(d)`, as a Hermitian matrix. -/
def realDiagonal (d : n → ℝ) : selfAdjoint (Matrix n n ℂ) :=
  ⟨Matrix.diagonal fun j ↦ (d j : ℂ),
    (Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext j; simp)).isSelfAdjoint⟩

omit [Fintype n] in
@[simp]
theorem coe_realDiagonal (d : n → ℝ) :
    (realDiagonal n d : Matrix n n ℂ) = Matrix.diagonal fun j ↦ (d j : ℂ) :=
  (rfl)

/-- A skew-Hermitian matrix commuting with a real diagonal matrix with distinct entries is the
matrix `diag(i θ)` of a torus element. -/
private theorem eq_diagonal_of_commute {A : Matrix n n ℂ} (hA : Aᴴ = -A) {d : n → ℝ}
    (hd : Function.Injective d) (hc : Commute A (Matrix.diagonal fun j ↦ (d j : ℂ))) :
    A = Matrix.diagonal fun j ↦ ((A j j).im : ℂ) * I := by
  have hdiag := isDiag_of_commute_diagonal (Complex.ofReal_injective.comp hd) hc.symm
  conv_lhs => rw [← hdiag.diagonal_diag]
  congr 1
  funext j
  -- The diagonal entries of a skew-Hermitian matrix are purely imaginary.
  have hjj := congrArg Complex.re (congrFun (congrFun hA j) j)
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply, RCLike.star_def, Complex.conj_re,
    Complex.neg_re] at hjj
  exact Complex.ext (by simpa using (by linarith : (A j j).re = 0)) (by simp)

/-- **The stabilizer of a regular covector is the torus Lie algebra**: for a real diagonal matrix
`diag(d)` with distinct entries, the coadjoint stabilizer of `ν_diag(d)` in `𝔲(n)` is the Lie
algebra `{diag(i θ)}` of the diagonal maximal torus. The coadjoint orbit through such a point is the
regular orbit `U(n) / T` of the complete flags. -/
theorem toSubmodule_lieAnnihilator_hermitianDualEquiv_diagonal {d : n → ℝ}
    (hd : Function.Injective d) :
    (lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n (realDiagonal n d))).toSubmodule =
      LinearMap.range (torusCoords n) := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, mem_lieAnnihilator_hermitianDualEquiv_iff, coe_realDiagonal,
    LinearMap.mem_range]
  constructor
  · intro hc
    refine ⟨fun j ↦ (toMatrix n X j j).im, toMatrix_injective ?_⟩
    rw [toMatrix_torusCoords]
    exact (eq_diagonal_of_commute (conjTranspose_toMatrix X) hd hc).symm
  · rintro ⟨θ, rfl⟩
    rw [toMatrix_torusCoords]
    exact Matrix.commute_diagonal _ _

/-- **The regular coadjoint orbits of `U(n)` have dimension `n² - n`**: for a real diagonal matrix
`diag(d)` with distinct entries, the tangent model `𝔲(n) ⧸ 𝔲(n)_ν` of the coadjoint orbit through
`ν = ν_diag(d)` has dimension `n² - n`, the dimension of the complete flag manifold `U(n) / T`. -/
theorem finrank_quotient_lieAnnihilator_hermitianDualEquiv_diagonal_add {d : n → ℝ}
    (hd : Function.Injective d) :
    finrank ℝ (lieAlgebra n ⧸
        (lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n (realDiagonal n d))).toSubmodule) +
      Fintype.card n =
      Fintype.card n ^ 2 := by
  have hinj : Function.Injective (torusCoords n) := fun θ θ' h ↦ by
    have h' := congrArg (toMatrix n) h
    rw [toMatrix_torusCoords, toMatrix_torusCoords] at h'
    funext j
    have := congrFun (congrFun h' j) j
    simpa [Matrix.diagonal_apply_eq, I_ne_zero] using this
  rw [← finrank_lieAlgebra, ← Submodule.finrank_quotient_add_finrank
    (lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n (realDiagonal n d))).toSubmodule,
    toSubmodule_lieAnnihilator_hermitianDualEquiv_diagonal hd, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fintype_fun_eq_card]

end UnitaryGroup

end TauCeti
