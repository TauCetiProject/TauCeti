/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.PointedSection
public import TauCeti.RingTheory.Flat.MatrixFactorization

/-!
# Universal exactness of the node-section complex

Let `A` be a commutative ring, `γ δ s t : A`, `q = x ^ 2 + γ * x * y + δ * y ^ 2` and
`R = A[Y][X] ⧸ (q(X, Y) - q(s, t))` the pointed node ring `TauCeti.PointedNodeRing γ δ s t` of
a section `(s, t)` through the node. On `R` the node-section matrix `Φ` and its adjugate `Ψ`
compose to zero in both orders. Here we prove that the two-periodic complex
`⋯ → R² --Ψ--> R² --Φ--> R² --Ψ--> ⋯` and its transpose remain exact after tensoring over `A`
with an arbitrary `A`-module `N`: `ker (Φ ⊗ N) = im (Ψ ⊗ N)`, `ker (Ψ ⊗ N) = im (Φ ⊗ N)`, and
likewise for `Φᵀ` and `Ψᵀ`.

This is the exactness in Knudsen's Proposition 3.1, in the form needed for changes of
coefficients: no Noetherian, nontriviality, unit-discriminant or flatness hypothesis is made on
`A` or `N`, so the form `q` may be degenerate (for instance `q = x ^ 2`, a double line). Knudsen
presents the section ideal `J = (u - s, v - t)` and its dual `Hom_R(J, R)` as the cokernels of
`Ψ` and `Φ`; universal exactness is what lets these presentations commute with every change of
coefficients.

Over `A[Y][X]` the node-section matrix and its adjugate are a matrix factorization of the defining
polynomial `F = q(X, Y) - q(s, t)`, which is monic in `X` and hence a nonzerodivisor, and the
quotient `R` is free, hence flat, over `A`. So the statements are instances of
`Matrix.exact_rTensor_mulVecLin_map_of_mul_eq_smul_one`.

## Main declarations

* `TauCeti.PointedNodeRing.exact_rTensor_adjugate_sectionMatrix`: `ker (Φ ⊗ N) = im (Ψ ⊗ N)`.
* `TauCeti.PointedNodeRing.exact_rTensor_sectionMatrix_adjugate`: `ker (Ψ ⊗ N) = im (Φ ⊗ N)`.
* `TauCeti.PointedNodeRing.exact_rTensor_transpose_adjugate_sectionMatrix`,
  `TauCeti.PointedNodeRing.exact_rTensor_transpose_sectionMatrix_adjugate`: the same for the
  transposed complex.

## References

* F. F. Knudsen, *A closer look at the stacks of stable pointed curves*, arXiv:1106.1588v2
  (2012), §3, Key Example and Proposition 3.1.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial
open BinaryQuadraticForm (nodeForm)

variable {A : Type*} [CommRing A] (γ δ s t : A)

namespace PointedNodeRing

/-- The quotient map `A[Y][X] → R` as a map of `A`-algebras. -/
private abbrev mkₐ : A[X][X] →ₐ[A] PointedNodeRing γ δ s t :=
  (AdjoinRoot.mkₐ (pointedNodePolynomial γ δ s t)).restrictScalars A

/-- The node-section matrix over `A[Y][X]`, at the coordinates `(X, Y)` and the section
`(s, t)`. -/
private abbrev sectionMatrixLift : Matrix (Fin 2) (Fin 2) A[X][X] :=
  (nodeForm (C (C γ)) (C (C δ))).sectionMatrix X (C X) (C (C s)) (C (C t))

private theorem ker_mkₐ :
    RingHom.ker (mkₐ γ δ s t) = Ideal.span {pointedNodePolynomial γ δ s t} := by
  ext P
  simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]

private theorem sectionMatrix_eq_map :
    sectionMatrix γ δ s t = (sectionMatrixLift γ δ s t).map (mkₐ γ δ s t) := by
  rw [sectionMatrix_def, sectionMatrixLift, ← AlgHom.coe_toRingHom,
    BinaryQuadraticForm.map_sectionMatrix]
  simp only [AlgHom.coe_restrictScalars, AdjoinRoot.mkₐ_toRingHom, BinaryQuadraticForm.map_nodeForm,
    mk_X, mk_C_X, mk_C_C]

private theorem adjugate_sectionMatrix_eq_map :
    (sectionMatrix γ δ s t).adjugate = (sectionMatrixLift γ δ s t).adjugate.map (mkₐ γ δ s t) := by
  rw [sectionMatrix_eq_map, ← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, RingHom.map_adjugate]

/-- The determinant `q(X, Y) - q(s, t)` of the node-section matrix over `A[Y][X]` is the defining
polynomial `F`, so the matrix and its adjugate are a matrix factorization of `F`. -/
private theorem eval_sub_eval_sectionMatrixLift :
    (nodeForm (C (C γ)) (C (C δ))).eval X (C X) - (nodeForm (C (C γ)) (C (C δ))).eval
      (C (C s)) (C (C t)) = pointedNodePolynomial γ δ s t := by
  rw [pointedNodePolynomial_eq_eval_sub]
  simp only [BinaryQuadraticForm.eval_nodeForm, C_mul, C_pow, C_add]

private theorem sectionMatrixLift_mul_adjugate :
    sectionMatrixLift γ δ s t * (sectionMatrixLift γ δ s t).adjugate =
      pointedNodePolynomial γ δ s t • 1 := by
  rw [BinaryQuadraticForm.sectionMatrix_mul_adjugate, eval_sub_eval_sectionMatrixLift]

private theorem adjugate_mul_sectionMatrixLift :
    (sectionMatrixLift γ δ s t).adjugate * sectionMatrixLift γ δ s t =
      pointedNodePolynomial γ δ s t • 1 := by
  rw [BinaryQuadraticForm.adjugate_mul_sectionMatrix, eval_sub_eval_sectionMatrixLift]

private theorem transpose_adjugate_mul_transpose_sectionMatrixLift :
    (sectionMatrixLift γ δ s t).adjugate.transpose * (sectionMatrixLift γ δ s t).transpose =
      pointedNodePolynomial γ δ s t • 1 := by
  rw [← Matrix.transpose_mul, sectionMatrixLift_mul_adjugate, Matrix.transpose_smul,
    Matrix.transpose_one]

private theorem transpose_sectionMatrixLift_mul_transpose_adjugate :
    (sectionMatrixLift γ δ s t).transpose * (sectionMatrixLift γ δ s t).adjugate.transpose =
      pointedNodePolynomial γ δ s t • 1 := by
  rw [← Matrix.transpose_mul, adjugate_mul_sectionMatrixLift, Matrix.transpose_smul,
    Matrix.transpose_one]

variable (N : Type*) [AddCommGroup N] [Module A N]

/-- The reductions to `R` of a matrix factorization `Ψ * Φ = Φ * Ψ = F • 1` of the defining
polynomial over `A[Y][X]` form an exact sequence after tensoring with any `A`-module `N`. -/
private theorem exact_rTensor_map_mkₐ {Φ Ψ : Matrix (Fin 2) (Fin 2) A[X][X]}
    (hΨΦ : Ψ * Φ = pointedNodePolynomial γ δ s t • 1)
    (hΦΨ : Φ * Ψ = pointedNodePolynomial γ δ s t • 1) :
    Function.Exact (((Ψ.map (mkₐ γ δ s t)).mulVecLin.restrictScalars A).rTensor N)
      (((Φ.map (mkₐ γ δ s t)).mulVecLin.restrictScalars A).rTensor N) :=
  Matrix.exact_rTensor_mulVecLin_map_of_mul_eq_smul_one Φ Ψ _ AdjoinRoot.mk_surjective
    (ker_mkₐ γ δ s t) (isRegular_pointedNodePolynomial γ δ s t).left.isSMulRegular hΨΦ hΦΨ N

/-- **Universal exactness of the node-section complex at `Φ`.** For every `A`-module `N`, the
kernel of `Φ ⊗ N` on `R² ⊗[A] N` is the image of `Ψ ⊗ N`, where `Φ` is the node-section matrix
and `Ψ` its adjugate. -/
theorem exact_rTensor_adjugate_sectionMatrix :
    Function.Exact
      (((sectionMatrix γ δ s t).adjugate.mulVecLin.restrictScalars A).rTensor N)
      (((sectionMatrix γ δ s t).mulVecLin.restrictScalars A).rTensor N) := by
  rw [adjugate_sectionMatrix_eq_map, sectionMatrix_eq_map]
  exact exact_rTensor_map_mkₐ γ δ s t N (adjugate_mul_sectionMatrixLift γ δ s t)
    (sectionMatrixLift_mul_adjugate γ δ s t)

/-- **Universal exactness of the node-section complex at `Ψ`.** For every `A`-module `N`, the
kernel of `Ψ ⊗ N` on `R² ⊗[A] N` is the image of `Φ ⊗ N`, where `Φ` is the node-section matrix
and `Ψ` its adjugate. -/
theorem exact_rTensor_sectionMatrix_adjugate :
    Function.Exact
      (((sectionMatrix γ δ s t).mulVecLin.restrictScalars A).rTensor N)
      (((sectionMatrix γ δ s t).adjugate.mulVecLin.restrictScalars A).rTensor N) := by
  rw [adjugate_sectionMatrix_eq_map, sectionMatrix_eq_map]
  exact exact_rTensor_map_mkₐ γ δ s t N (sectionMatrixLift_mul_adjugate γ δ s t)
    (adjugate_mul_sectionMatrixLift γ δ s t)

/-- **Universal exactness of the transposed node-section complex at `Φᵀ`.** For every
`A`-module `N`, the kernel of `Φᵀ ⊗ N` on `R² ⊗[A] N` is the image of `Ψᵀ ⊗ N`. -/
theorem exact_rTensor_transpose_adjugate_sectionMatrix :
    Function.Exact
      (((sectionMatrix γ δ s t).adjugate.transpose.mulVecLin.restrictScalars A).rTensor N)
      (((sectionMatrix γ δ s t).transpose.mulVecLin.restrictScalars A).rTensor N) := by
  rw [adjugate_sectionMatrix_eq_map, sectionMatrix_eq_map, ← Matrix.transpose_map,
    ← Matrix.transpose_map]
  exact exact_rTensor_map_mkₐ γ δ s t N
    (transpose_adjugate_mul_transpose_sectionMatrixLift γ δ s t)
    (transpose_sectionMatrixLift_mul_transpose_adjugate γ δ s t)

/-- **Universal exactness of the transposed node-section complex at `Ψᵀ`.** For every
`A`-module `N`, the kernel of `Ψᵀ ⊗ N` on `R² ⊗[A] N` is the image of `Φᵀ ⊗ N`. -/
theorem exact_rTensor_transpose_sectionMatrix_adjugate :
    Function.Exact
      (((sectionMatrix γ δ s t).transpose.mulVecLin.restrictScalars A).rTensor N)
      (((sectionMatrix γ δ s t).adjugate.transpose.mulVecLin.restrictScalars A).rTensor N) := by
  rw [adjugate_sectionMatrix_eq_map, sectionMatrix_eq_map, ← Matrix.transpose_map,
    ← Matrix.transpose_map]
  exact exact_rTensor_map_mkₐ γ δ s t N
    (transpose_sectionMatrixLift_mul_transpose_adjugate γ δ s t)
    (transpose_adjugate_mul_transpose_sectionMatrixLift γ δ s t)

end PointedNodeRing

end TauCeti
