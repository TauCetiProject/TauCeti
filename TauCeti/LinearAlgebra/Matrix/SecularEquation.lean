/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.LinearAlgebra.Matrix.SchurComplement

/-!
# The secular equation for rank-one perturbations

Let `A` be a square matrix over a field, `u` and `v` vectors, and `μ` a scalar outside the
spectrum of `A`. Then `μ` is an eigenvalue of the rank-one perturbation `A + u vᵀ` exactly when
it solves the *secular equation*

`1 + v ⬝ᵥ (A - μ • 1)⁻¹ *ᵥ u = 0`.

Every eigenvector `x` of `A + u vᵀ` for such a `μ` is `-(v ⬝ᵥ x) • (A - μ • 1)⁻¹ *ᵥ u`, and at a
root of the secular equation the eigenspace is the line spanned by `(A - μ • 1)⁻¹ *ᵥ u`; the
eigenvector formulas hold over any commutative ring. The eigenvalues of a rank-one
perturbation which leave the spectrum of the unperturbed matrix (outliers) are located by this
equation, and the formula for their eigenvectors gives their overlap with the perturbation
direction.

The resolvent convention `(A - μ • 1)⁻¹` matches `Matrix.IsHermitian.inv_sub_smul_one_apply`.

## Main results

* `Matrix.mem_spectrum_add_vecMulVec_iff` — the secular equation;
* `Matrix.eq_neg_dotProduct_smul_inv_sub_smul_one_mulVec` and
  `Matrix.add_vecMulVec_mulVec_inv_sub_smul_one_mulVec` — the form of every eigenvector at a
  point outside the spectrum of `A`, and the eigenvector at a root of the secular equation;
* `Matrix.eigenspace_mulVecLin_add_vecMulVec` and
  `Matrix.finrank_eigenspace_mulVecLin_add_vecMulVec` — at a root of the secular equation the
  eigenspace is the line spanned by `(A - μ • 1)⁻¹ *ᵥ u`.

## References

* F. Benaych-Georges, R. R. Nadakuditi, *The eigenvalues and eigenvectors of finite, low rank
  perturbations of large random matrices*, Adv. Math. 227 (2011), 494–521, Lemmas 4.1 and 5.1.
* G. H. Golub, *Some modified matrix eigenvalue problems*, SIAM Review 15 (1973), 318–334, §5.
-/

public section

namespace Matrix

section CommRing

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] {A : Matrix n n R} {μ : R}

/-- A scalar outside the spectrum makes the shifted matrix `A - μ • 1` invertible. -/
theorem isUnit_sub_smul_one_of_notMem_spectrum (hμ : μ ∉ spectrum R A) : IsUnit (A - μ • 1) := by
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one] at hμ
  simpa using hμ.neg

/-- An eigenvector `x` of the rank-one perturbation `A + u vᵀ` for a scalar `μ` outside the
spectrum of `A` is the multiple `-(v ⬝ᵥ x)` of `(A - μ • 1)⁻¹ *ᵥ u`. -/
theorem eq_neg_dotProduct_smul_inv_sub_smul_one_mulVec (hμ : μ ∉ spectrum R A)
    {u v x : n → R} (hx : (A + vecMulVec u v) *ᵥ x = μ • x) :
    x = -(v ⬝ᵥ x) • ((A - μ • 1)⁻¹ *ᵥ u) := by
  have hunit := isUnit_sub_smul_one_of_notMem_spectrum hμ
  have hshift : (A - μ • 1) *ᵥ x = -(v ⬝ᵥ x) • u := by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul] at hx
    rw [sub_mulVec, smul_mulVec, one_mulVec, ← hx, neg_smul]
    abel
  rw [← mulVec_smul, ← hshift, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit),
    one_mulVec]

/-- At a root `μ` of the secular equation outside the spectrum of `A`, the vector
`(A - μ • 1)⁻¹ *ᵥ u` is an eigenvector of `A + u vᵀ` for `μ`. -/
theorem add_vecMulVec_mulVec_inv_sub_smul_one_mulVec (hμ : μ ∉ spectrum R A) {u v : n → R}
    (h : 1 + v ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = 0) :
    (A + vecMulVec u v) *ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = μ • ((A - μ • 1)⁻¹ *ᵥ u) := by
  have hunit := isUnit_sub_smul_one_of_notMem_spectrum hμ
  have hw : (A - μ • 1) *ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = u := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_iff_eq_add] at hw
  have hsum : u + (v ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ u)) • u = 0 := by
    rw [← zero_smul R u, ← h, add_smul, one_smul]
  rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hw, add_right_comm, hsum, zero_add]

/-- At a root `μ` of the secular equation outside the spectrum of `A`, the eigenspace of
`A + u vᵀ` for `μ` is the line spanned by `(A - μ • 1)⁻¹ *ᵥ u`. -/
theorem eigenspace_mulVecLin_add_vecMulVec (hμ : μ ∉ spectrum R A) {u v : n → R}
    (h : 1 + v ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = 0) :
    Module.End.eigenspace (A + vecMulVec u v).mulVecLin μ = R ∙ ((A - μ • 1)⁻¹ *ᵥ u) := by
  ext x
  rw [Module.End.mem_eigenspace_iff, mulVecLin_apply, Submodule.mem_span_singleton]
  refine ⟨fun hx ↦ ⟨-(v ⬝ᵥ x), (eq_neg_dotProduct_smul_inv_sub_smul_one_mulVec hμ hx).symm⟩, ?_⟩
  rintro ⟨a, rfl⟩
  rw [mulVec_smul, add_vecMulVec_mulVec_inv_sub_smul_one_mulVec hμ h, smul_comm]

end CommRing

section Field

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {A : Matrix n n K} {μ : K}

/-- **The secular equation.** A scalar `μ` outside the spectrum of `A` lies in the spectrum of
the rank-one perturbation `A + u vᵀ` exactly when `1 + v ⬝ᵥ (A - μ • 1)⁻¹ *ᵥ u = 0`. -/
theorem mem_spectrum_add_vecMulVec_iff (hμ : μ ∉ spectrum K A) (u v : n → K) :
    μ ∈ spectrum K (A + vecMulVec u v) ↔ 1 + v ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = 0 := by
  have h := isUnit_add_vecMulVec_iff (A - μ • 1) (isUnit_sub_smul_one_of_notMem_spectrum hμ) u v
  rw [isUnit_iff_ne_zero, sub_add_eq_add_sub] at h
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← IsUnit.neg_iff, neg_sub, h, not_not]

/-- At a root `μ` of the secular equation outside the spectrum of `A`, the eigenvalue `μ` of
`A + u vᵀ` has geometric multiplicity one. -/
theorem finrank_eigenspace_mulVecLin_add_vecMulVec (hμ : μ ∉ spectrum K A) {u v : n → K}
    (h : 1 + v ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ u) = 0) :
    Module.finrank K (Module.End.eigenspace (A + vecMulVec u v).mulVecLin μ) = 1 := by
  rw [eigenspace_mulVecLin_add_vecMulVec hμ h]
  refine finrank_span_singleton fun hw ↦ ?_
  rw [hw, dotProduct_zero, add_zero] at h
  exact one_ne_zero h

end Field

end Matrix
