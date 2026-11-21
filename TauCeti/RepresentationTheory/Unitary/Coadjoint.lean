/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Analysis.Matrix.UnitaryGroup.SchurHorn
public import TauCeti.RepresentationTheory.Unitary.LieAlgebra
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Complex.Conjugation
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The coadjoint orbits of `U(n)` as Hermitian eigenvalue orbits

The Lie algebra `𝔲(n)` of the unitary group (`TauCeti.UnitaryGroup.lieAlgebra n`) consists, in
matrix coordinates (`TauCeti.UnitaryGroup.toMatrix`), of the skew-Hermitian matrices. This file
identifies its dual with the Hermitian matrices and computes the coadjoint action, orbits and
Kirillov–Kostant–Souriau form of `U(n)` in these terms, with the pairing fixed as

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
Lie algebra (`TauCeti.UnitaryGroup.toSubmodule_lieAnnihilator_hermitianDualEquiv_realDiagonal`), so
the algebraic tangent model `𝔲(n) ⧸ 𝔲(n)_ν` of such a regular orbit has dimension `n² - n`, the
dimension of the complete flag manifold `U(n) / T`
(`TauCeti.UnitaryGroup.finrank_quotient_lieAnnihilator_hermitianDualEquiv_realDiagonal_add_card`).

## Main definitions

* `TauCeti.UnitaryGroup.hermitianDualEquiv`: the identification of the Hermitian matrices with
  `𝔲(n)*`.
* `TauCeti.UnitaryGroup.coadjointRepresentation`: the coadjoint representation of `U(n)`.
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

variable {n : Type*} [Fintype n] [DecidableEq n]

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

omit [DecidableEq n] in
/-- For a Hermitian matrix `H`, the complex conjugate of `tr (H M)` is `tr (Mᴴ H)`. -/
private theorem starRingEnd_trace_mul (H : selfAdjoint (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    starRingEnd ℂ ((H : Matrix n n ℂ) * M).trace = (Mᴴ * H).trace := by
  rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    (IsSelfAdjoint.isHermitian H.2).eq]

private theorem tracePairing_injective : Function.Injective (tracePairing (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro H hH
  obtain ⟨X, hX⟩ := exists_toMatrix_eq_I_smul H
  have h := LinearMap.congr_fun hH X
  rw [tracePairing_apply, hX, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
    neg_mul, I_mul_I, neg_neg, one_mul, LinearMap.zero_apply] at h
  -- The trace of `H H = Hᴴ H` is real, and its real part vanishes.
  have hH' : (H : Matrix n n ℂ)ᴴ = H := (IsSelfAdjoint.isHermitian H.2).eq
  have hreal := starRingEnd_trace_mul H H
  rw [hH'] at hreal
  have h0 : ((H : Matrix n n ℂ) * H).trace = 0 :=
    Complex.ext h (Complex.conj_eq_iff_im.1 hreal)
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 (by rwa [hH']))

private theorem tracePairing_bijective : Function.Bijective (tracePairing (n := n)) := by
  have : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    Module.Finite.of_injective _ tracePairing_injective
  refine ⟨tracePairing_injective, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 tracePairing_injective
  rw [Subspace.dual_finrank_eq, finrank_lieAlgebra]
  exact (finrank_selfAdjoint_submodule (A := Matrix n n ℂ)).trans (by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq])

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
    rw [starRingEnd_trace_mul, conjTranspose_toMatrix, Matrix.neg_mul, Matrix.trace_neg,
      Matrix.trace_mul_comm]
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
    coe_lieHermitian, ZeroMemClass.coe_zero, sub_eq_zero, commute_iff_eq]

/-- **The Kirillov–Kostant–Souriau form in the Hermitian model**:
`ω_H([X], [Y]) = re (-i tr (H [A, B]))`, where `A` and `B` are the matrices of `X` and `Y`. -/
theorem kksForm_hermitianDualEquiv_mk (H : selfAdjoint (Matrix n n ℂ)) (X Y : lieAlgebra n) :
    (hermitianDualEquiv n H).kksForm (Submodule.Quotient.mk X) (Submodule.Quotient.mk Y) =
      (-I * ((H : Matrix n n ℂ) *
        (toMatrix n X * toMatrix n Y - toMatrix n Y * toMatrix n X)).trace).re := by
  rw [Module.Dual.kksForm_mk, hermitianDualEquiv_apply, toMatrix_lie]

/-! ### The coadjoint representation of `U(n)` -/

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
  toFun θ := Matrix.diagonal fun j ↦ I * θ j
  map_add' θ θ' := by simp [mul_add, Matrix.diagonal_add]
  map_smul' c θ := by
    ext i j
    by_cases h : i = j <;> simp [h, Complex.real_smul, mul_left_comm]

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
    toMatrix n (torusCoords n θ) = Matrix.diagonal fun j ↦ I * θ j := by
  rw [toMatrix_apply, ← Lie.unitsLieAlgebraLieEquiv_apply]
  exact (Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).apply_symm_apply (diagonalI θ)

/-- The torus coordinates `θ ↦ diag(i θ)` are injective. -/
theorem torusCoords_injective : Function.Injective (torusCoords n) := fun θ θ' h ↦ by
  have h' := congrArg (toMatrix n) h
  rw [toMatrix_torusCoords, toMatrix_torusCoords] at h'
  funext j
  simpa [Matrix.diagonal_apply_eq, I_ne_zero] using congrFun (congrFun h' j) j

/-- The functional `ν_H` pairs the torus element `diag(i θ)` with `∑ⱼ re (Hⱼⱼ) θⱼ`. -/
theorem hermitianDualEquiv_torusCoords (H : selfAdjoint (Matrix n n ℂ)) (θ : n → ℝ) :
    hermitianDualEquiv n H (torusCoords n θ) = ∑ j, ((H : Matrix n n ℂ) j j).re * θ j := by
  rw [hermitianDualEquiv_apply, toMatrix_torusCoords, Matrix.neg_I_mul_trace_mul_diagonal_I_mul,
    Complex.re_sum]
  simp [mul_comm]

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
  simp only [RCLike.re_to_complex, Unitary.coe_star]

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

/-- **The stabilizer of a regular covector is the torus Lie algebra**: for a real diagonal matrix
`diag(d)` with distinct entries, the coadjoint stabilizer of `ν_diag(d)` in `𝔲(n)` is the Lie
algebra `{diag(i θ)}` of the diagonal maximal torus `T`, as expected for the flag manifold
`U(n) / T`. -/
theorem toSubmodule_lieAnnihilator_hermitianDualEquiv_realDiagonal {d : n → ℝ}
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
    exact (eq_diagonal_I_mul_of_commute_diagonal (conjTranspose_toMatrix X) hd hc).symm
  · rintro ⟨θ, rfl⟩
    rw [toMatrix_torusCoords]
    exact Matrix.commute_diagonal _ _

/-- **The tangent model of a regular coadjoint orbit has dimension `n² - n`**: for a real diagonal
matrix `diag(d)` with distinct entries, the tangent model `𝔲(n) ⧸ 𝔲(n)_ν` of the coadjoint orbit
through `ν = ν_diag(d)` has dimension `n² - n`, the dimension of the complete flag manifold
`U(n) / T`. -/
theorem finrank_quotient_lieAnnihilator_hermitianDualEquiv_realDiagonal_add_card {d : n → ℝ}
    (hd : Function.Injective d) :
    finrank ℝ (lieAlgebra n ⧸
        (lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n (realDiagonal n d))).toSubmodule) +
      Fintype.card n =
      Fintype.card n ^ 2 := by
  rw [← finrank_lieAlgebra, ← Submodule.finrank_quotient_add_finrank
    (lieAnnihilator ℝ (lieAlgebra n) (hermitianDualEquiv n (realDiagonal n d))).toSubmodule,
    toSubmodule_lieAnnihilator_hermitianDualEquiv_realDiagonal hd,
    LinearMap.finrank_range_of_inj torusCoords_injective, Module.finrank_fintype_fun_eq_card]

end UnitaryGroup

end TauCeti
