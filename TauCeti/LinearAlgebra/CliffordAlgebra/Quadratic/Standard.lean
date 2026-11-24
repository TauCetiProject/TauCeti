/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.LinearAlgebra.CliffordAlgebra.StandardBivector
public import TauCeti.LinearAlgebra.QuadraticForm.Standard

/-!
# The quadratic realization in the coordinates of the standard form

Two identifications of the orthogonal Lie algebra with the quadratic elements of a Clifford algebra
are in the library. For the sum-of-squares form `Q₀ = QuadraticMap.weightedSumSquares K 1` on
`Fin n → K`, `CliffordAlgebra.bivectorEquivSo` identifies the exterior square, with the bracket of
quadratic Clifford elements, with Mathlib's matrix Lie algebra `LieAlgebra.Orthogonal.so (Fin n) K`.
For an arbitrary nondegenerate form, `CliffordAlgebra.soEquivQuadratic` identifies the
endomorphisms skew-adjoint for the polar form with the quadratic elements. Both are pinned by the
same generator action: a skew endomorphism `f` corresponds to the quadratic element `q` with
`⁅q, ι Q x⁆ = ι Q (f x)`, and the bivector of `u` and `v` acts by
`x ↦ polar Q v x • u - polar Q u x • v`.

This file proves that the two agree for the standard form, once a skew-adjoint endomorphism is
read as its matrix through `TauCeti.QuadraticForm.standardSkewAdjointLieEquiv`. It then transports
the comparison to an abstract nondegenerate quadratic space `(V, Q)` along a specified isometry
`e : Q.IsometryEquiv Q₀`: the matrix Lie algebra is identified with the quadratic elements of
`CliffordAlgebra Q` so that a matrix `A` acts on generators by `x ↦ e⁻¹ (A *ᵥ e x)` and the
standard bivector matrix of `u ∧ v` becomes the Clifford bivector of `e⁻¹ u` and `e⁻¹ v`.

## Main definitions

* `CliffordAlgebra.matrixSoEquivQuadratic`: the matrix orthogonal Lie algebra realized by quadratic
  Clifford elements along a specified isometry with the standard form.

## Main results

* `CliffordAlgebra.bivectorEquivSo_eq_trans_soEquivQuadratic_symm`: for the standard form,
  `bivectorEquivSo` factors through the abstract quadratic realization.
* `CliffordAlgebra.matrixSoEquivQuadratic_lie_ι`: the generator action of the matrix realization.
* `CliffordAlgebra.matrixSoEquivQuadratic_bivectorEquivSo` and
  `CliffordAlgebra.matrixSoEquivQuadratic_bivectorEquivSo_ιMulti`: the matrix realization is the
  transport of the standard bivector equivalence along the isometry.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 6.
-/

public section

open scoped Matrix

open TauCeti

universe u v

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section Standard

variable (n : ℕ) (K : Type u) [Field K] [Invertible (2 : K)]

/-- The realization of the skew endomorphism of a standard bivector matrix is the quadratic element
of the corresponding exterior bivector. -/
private theorem soEquivQuadratic_standardSkewAdjointLieEquiv_symm_bivectorEquivSo
    (hQ : (QuadraticMap.weightedSumSquares K (1 : Fin n → K)).Nondegenerate)
    (z : ⋀[K]^2 (Fin n → K)) :
    let Q := QuadraticMap.weightedSumSquares K (1 : Fin n → K)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    soEquivQuadratic Q hQ
        ((QuadraticForm.standardSkewAdjointLieEquiv K (Fin n)).symm (bivectorEquivSo n K z)) =
      bivectorLieEquiv Q z := by
  intro Q
  apply quadraticLieSubalgebra_ext Q hQ
  intro x
  rw [soEquivQuadratic_lie_ι, QuadraticForm.coe_standardSkewAdjointLieEquiv_symm_apply,
    lieEquivMatrix'_symm_apply, Matrix.toLin'_apply, bivectorLieEquiv_apply]
  exact ι_bivectorEquivSo_mulVec n K z x

/-- **The standard bivector equivalence is the quadratic realization in coordinates.** For the
sum-of-squares form `Q` on `Fin n → K`, `bivectorEquivSo` is the composite of the exterior-square
model `bivectorLieEquiv Q` of the quadratic elements, the inverse of the abstract quadratic
realization `soEquivQuadratic`, and the matrix of a skew-adjoint endomorphism. -/
theorem bivectorEquivSo_eq_trans_soEquivQuadratic_symm
    (hQ : (QuadraticMap.weightedSumSquares K (1 : Fin n → K)).Nondegenerate) :
    let Q := QuadraticMap.weightedSumSquares K (1 : Fin n → K)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    bivectorEquivSo n K = (bivectorLieEquiv Q).trans ((soEquivQuadratic Q hQ).symm.trans
      (QuadraticForm.standardSkewAdjointLieEquiv K (Fin n))) := by
  intro Q
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  refine LieEquiv.ext fun z => ?_
  rw [LieEquiv.trans_apply, LieEquiv.trans_apply,
    ← soEquivQuadratic_standardSkewAdjointLieEquiv_symm_bivectorEquivSo n K hQ z,
    LieEquiv.symm_apply_apply, LieEquiv.apply_symm_apply]

end Standard

section Transport

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- **The matrix orthogonal Lie algebra realized by quadratic Clifford elements.** A specified
isometry `e` from a nondegenerate quadratic form `Q` to the sum-of-squares form on `κ → K`
identifies `LieAlgebra.Orthogonal.so κ K` with the quadratic elements of `CliffordAlgebra Q`:
a skew matrix is read as a skew-adjoint endomorphism of `κ → K`, conjugated back to `V` along
`e`, and realized by `soEquivQuadratic`. The space `V` is finite-dimensional through `e`. -/
noncomputable def matrixSoEquivQuadratic (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares K (1 : κ → K))) :
    LieAlgebra.Orthogonal.so κ K ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  haveI := e.symm.toLinearEquiv.finiteDimensional
  ((QuadraticForm.standardSkewAdjointLieEquiv K κ).symm.trans
    e.symm.skewAdjointLieSubalgebraCongr).trans (soEquivQuadratic Q hQ)

/-- The matrix realization of `A` acts on Clifford generators by the endomorphism
`x ↦ e⁻¹ (A *ᵥ e x)`. -/
@[simp]
theorem matrixSoEquivQuadratic_lie_ι (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares K (1 : κ → K)))
    (A : LieAlgebra.Orthogonal.so κ K) (x : V) :
    ⁅(matrixSoEquivQuadratic Q hQ e A : CliffordAlgebra Q), ι Q x⁆ =
      ι Q (e.symm ((A : Matrix κ κ K) *ᵥ e x)) := by
  have := e.symm.toLinearEquiv.finiteDimensional
  rw [matrixSoEquivQuadratic, LieEquiv.trans_apply, LieEquiv.trans_apply, soEquivQuadratic_lie_ι,
    QuadraticMap.IsometryEquiv.coe_skewAdjointLieSubalgebraCongr_apply,
    QuadraticForm.coe_standardSkewAdjointLieEquiv_symm_apply, lieEquivMatrix'_symm_apply,
    Matrix.toLin'_apply, QuadraticMap.IsometryEquiv.symm_symm]

/-- **The matrix realization transports the standard bivector equivalence.** On the matrix of an
exterior bivector of the standard form, the realization along `e` is the transport along `e⁻¹` of
the corresponding quadratic element of the standard Clifford algebra. -/
theorem matrixSoEquivQuadratic_bivectorEquivSo {n : ℕ} (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares K (1 : Fin n → K)))
    (z : ⋀[K]^2 (Fin n → K)) :
    let Q₀ := QuadraticMap.weightedSumSquares K (1 : Fin n → K)
    letI := bivectorLieRing Q₀
    letI := bivectorLieAlgebra Q₀
    matrixSoEquivQuadratic Q hQ e (bivectorEquivSo n K z) =
      quadraticLieSubalgebraCongr e.symm (bivectorLieEquiv Q₀ z) := by
  intro Q₀
  have hQ₀ : Q₀.Nondegenerate := e.nondegenerate_iff.1 hQ
  rw [matrixSoEquivQuadratic, LieEquiv.trans_apply, LieEquiv.trans_apply,
    soEquivQuadratic_skewAdjointLieSubalgebraCongr hQ₀ hQ,
    soEquivQuadratic_standardSkewAdjointLieEquiv_symm_bivectorEquivSo n K hQ₀ z]

/-- The matrix realization along `e` of the standard bivector matrix `2 * (u vᵀ - v uᵀ)` is the
Clifford bivector of `e⁻¹ u` and `e⁻¹ v`. -/
@[simp]
theorem matrixSoEquivQuadratic_bivectorEquivSo_ιMulti {n : ℕ} (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares K (1 : Fin n → K)))
    (u v : Fin n → K) :
    let Q₀ := QuadraticMap.weightedSumSquares K (1 : Fin n → K)
    letI := bivectorLieRing Q₀
    letI := bivectorLieAlgebra Q₀
    matrixSoEquivQuadratic Q hQ e (bivectorEquivSo n K (exteriorPower.ιMulti K 2 ![u, v])) =
      ⟨bivector Q (e.symm u) (e.symm v),
        bivector_mem_quadraticLieSubalgebra Q (e.symm u) (e.symm v)⟩ := by
  intro Q₀
  have h : bivectorLieEquiv Q₀ (exteriorPower.ιMulti K 2 ![u, v]) =
      ⟨bivector Q₀ u v, bivector_mem_quadraticLieSubalgebra Q₀ u v⟩ := by
    apply Subtype.ext
    rw [bivectorLieEquiv_apply, coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply,
      bivectorExterior_apply_ιMulti]
  refine (matrixSoEquivQuadratic_bivectorEquivSo Q hQ e _).trans ?_
  rw [h, quadraticLieSubalgebraCongr_bivector]

end Transport

end CliffordAlgebra
