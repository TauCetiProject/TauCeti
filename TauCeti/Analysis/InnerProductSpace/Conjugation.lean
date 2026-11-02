/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinatewise conjugation in an orthonormal basis

There is no canonical conjugation on an abstract inner product space, so this file attaches one to
an orthonormal basis `e` by conjugating the coordinates in it:
`e.conjugation x = ∑ i, conj ⟪e i, x⟫ • e i`. It is a conjugate-linear isometric involution of `V`
(`OrthonormalBasis.conjugation`, `OrthonormalBasis.conjugation_conjugation`), and conjugating an
operator by it, `A ↦ J ∘ A ∘ J` (`OrthonormalBasis.conjCLM`), is the coordinate-free description
of conjugating the matrix of `A` entrywise.

## Main definitions

* `OrthonormalBasis.conjugation`: the conjugate-linear isometric involution attached to an
  orthonormal basis.
* `OrthonormalBasis.conjCLM`: conjugation of continuous linear operators, `A ↦ J ∘ A ∘ J`, itself
  a conjugate-linear isometric involution of the operators.

## Main statements

* `OrthonormalBasis.conjugation_conjugation` and
  `OrthonormalBasis.inner_conjugation_conjugation`: conjugation is an involution, and reverses
  the inner product.
* `OrthonormalBasis.conjugation_basis`: the basis it is attached to is fixed vector by vector,
  which is what makes it *the* conjugation of that basis.
* `OrthonormalBasis.inner_conjugation_left_basis`: pairing a conjugate against a basis vector
  swaps the two arguments of the inner product.
* `OrthonormalBasis.conjCLM_one`, `OrthonormalBasis.conjCLM_mul` and
  `OrthonormalBasis.conjCLM_conjCLM`: conjugation of operators is a multiplicative involution
  fixing the identity, so with its conjugate-linearity it is a conjugate-linear ring involution of
  the operators.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

section Conjugation

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Coordinatewise conjugation in an orthonormal basis.** A conjugate-linear isometric involution
of `V`, which on coordinates is `x i ↦ conj (x i)`. -/
noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) : V ≃ₗᵢ⋆[𝕜] V :=
  let J : V →ₗ⋆[𝕜] V :=
    { toFun x := ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i
      map_add' x y := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
      map_smul' c x := by simp [inner_smul_right, Finset.smul_sum, smul_smul] }
  have hJ (x : V) (j : ι) : ⟪e j, J x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 :=
    e.orthonormal.inner_right_fintype _ j
  have hJJ : Function.Involutive J := fun x ↦ by
    conv_rhs => rw [← e.sum_repr' x]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hJ, RCLike.conj_conj]
  { LinearEquiv.ofInvolutive J hJJ with
    norm_map' x := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [← e.sum_sq_norm_inner_right, ← e.sum_sq_norm_inner_right]
      simp [hJ, norm_inner_symm] }

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugation, expanded as the coordinate sum defining it. -/
theorem conjugation_apply (x : V) :
    e.conjugation x = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i :=
  (rfl)

/-- The coordinates of a conjugate are the conjugated coordinates. -/
@[simp]
theorem inner_conjugation (x : V) (j : ι) :
    ⟪e j, e.conjugation x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 := by
  rw [conjugation_apply]
  exact e.orthonormal.inner_right_fintype _ j

/-- Conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : V) : e.conjugation (e.conjugation x) = x := by
  conv_rhs => rw [← e.sum_repr' x]
  simp [conjugation_apply (x := e.conjugation x)]

/-- Conjugation is its own inverse. -/
@[simp]
theorem conjugation_symm : e.conjugation.symm = e.conjugation :=
  LinearIsometryEquiv.ext fun x ↦
    e.conjugation.symm_apply_eq.mpr (e.conjugation_conjugation x).symm

/-- **Conjugation fixes the basis it is attached to.** Coordinatewise conjugation is the identity
on the vectors whose coordinates are `0` and `1`. -/
@[simp]
theorem conjugation_basis (j : ι) : e.conjugation (e j) = e j := by
  classical
  conv_rhs => rw [← e.sum_repr' (e j)]
  simp [conjugation_apply, orthonormal_iff_ite.mp e.orthonormal, apply_ite]

/-- Conjugation reverses the inner product: it is conjugate-linear and isometric. -/
@[simp]
theorem inner_conjugation_conjugation (x y : V) :
    ⟪e.conjugation x, e.conjugation y⟫_𝕜 = (starRingEnd 𝕜) ⟪x, y⟫_𝕜 := by
  rw [← e.sum_inner_mul_inner, ← e.sum_inner_mul_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← inner_conj_symm (e.conjugation x) (e i), inner_conjugation, inner_conjugation, map_mul,
    inner_conj_symm]

/-- **Pairing a conjugate against a basis vector swaps the arguments.** Conjugation fixes `e j`, so
the reversal of the inner product turns `⟪J x, e j⟫` into `⟪e j, x⟫`. This is the form in which the
conjugation is contracted against a coordinate. -/
@[simp]
theorem inner_conjugation_left_basis (x : V) (j : ι) :
    ⟪e.conjugation x, e j⟫_𝕜 = ⟪e j, x⟫_𝕜 := by
  conv_lhs => rw [← conjugation_basis e j]
  rw [inner_conjugation_conjugation, inner_conj_symm]

end Conjugation

section ConjugateOperator

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Conjugation of continuous linear operators**, `A ↦ J ∘ A ∘ J` for `J` the conjugation of
`e`. The two conjugate-linearities of `J` cancel, so `J ∘ A ∘ J` is again `𝕜`-linear, and it has the
norm of `A` because `J` is an isometric involution. As a map of operators it is itself a
conjugate-linear isometric involution. -/
noncomputable def conjCLM (e : OrthonormalBasis ι 𝕜 V) : (V →L[𝕜] V) ≃ₗᵢ⋆[𝕜] (V →L[𝕜] V) :=
  let J : V →SL[starRingEnd 𝕜] V := e.conjugation
  let C : (V →L[𝕜] V) →ₗ⋆[𝕜] (V →L[𝕜] V) :=
    { toFun A := J.comp (A.comp J)
      map_add' A B := by ext; simp [J]
      map_smul' c A := by ext; simp [J] }
  { LinearEquiv.ofInvolutive C fun A ↦ by ext; simp [C, J] with
    norm_map' A := (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp _ _).trans
      (A.opNorm_comp_linearIsometryEquiv e.conjugation) }

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Evaluation of a conjugated operator. -/
@[simp]
theorem conjCLM_apply (A : V →L[𝕜] V) (x : V) :
    e.conjCLM A x = e.conjugation (A (e.conjugation x)) :=
  (rfl)

/-- Conjugation fixes the identity, because `J` is an involution. -/
@[simp]
theorem conjCLM_one : e.conjCLM 1 = 1 := by
  ext x
  simp

/-- Conjugation is multiplicative, again because `J` is an involution: the two inner copies of `J`
cancel. -/
@[simp]
theorem conjCLM_mul (A B : V →L[𝕜] V) : e.conjCLM (A * B) = e.conjCLM A * e.conjCLM B := by
  ext x
  simp

/-- Conjugation of operators is an involution, because `J` is. -/
@[simp]
theorem conjCLM_conjCLM (A : V →L[𝕜] V) : e.conjCLM (e.conjCLM A) = A := by
  ext x
  simp

/-- Conjugation of operators is its own inverse. -/
@[simp]
theorem conjCLM_symm : e.conjCLM.symm = e.conjCLM :=
  LinearIsometryEquiv.ext fun A ↦ e.conjCLM.symm_apply_eq.mpr (e.conjCLM_conjCLM A).symm

end ConjugateOperator

end OrthonormalBasis
