/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Definiteness of the form of a symmetric operator on its spectral subspaces

Let `A` be a symmetric operator on a finite-dimensional inner product space. Its quadratic form
`x ↦ re ⟪A x, x⟫` is negative definite on the negative spectral subspace
`A.pointSpectralSubspace (Iio 0)`, positive definite on the positive spectral subspace
`A.pointSpectralSubspace (Ioi 0)`, positive semidefinite on `A.pointSpectralSubspace (Ici 0)`,
the orthogonal complement of the negative spectral subspace, and negative semidefinite on
`A.pointSpectralSubspace (Iic 0)`. When `A` is injective the negative and positive spectral
subspaces are complementary. Over `ℝ`, the dimensions of these subspaces are the indices of
inertia of the form (`LinearMap.IsSymmetric.sigNeg_eq_finrank_pointSpectralSubspace` and
`LinearMap.IsSymmetric.sigPos_eq_finrank_pointSpectralSubspace` in
`TauCeti.Analysis.InnerProductSpace.Symmetric.Signature`). For the Riesz operator `B♯` of a real bilinear form `B`, with
`⟪B♯ u, v⟫ = B u v`, the form `B` itself is negative definite on the negative spectral subspace
of `B♯` and positive definite on the positive one.

Together with the smooth dependence of the spectral projections on an invertible self-adjoint
operator (`TauCeti.Analysis.InnerProductSpace.Spectral.Projection`), this splits a smooth family of
nondegenerate symmetric bilinear forms into smooth families of negative and positive definite
subspaces of the dimensions prescribed by Sylvester's law of inertia.

## Main results

* `LinearMap.IsSymmetric.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio`,
  `LinearMap.IsSymmetric.re_inner_apply_self_pos_of_mem_pointSpectralSubspace_Ioi`: the form is
  negative definite on the negative spectral subspace and positive definite on the positive one.
* `LinearMap.IsSymmetric.re_inner_apply_self_nonneg_of_mem_pointSpectralSubspace_Ici`,
  `LinearMap.IsSymmetric.re_inner_apply_self_nonpos_of_mem_pointSpectralSubspace_Iic`: the form is
  positive semidefinite on the spectral subspace of the nonnegative eigenvalues and negative
  semidefinite on that of the nonpositive eigenvalues.
* `LinearMap.IsSymmetric.isCompl_pointSpectralSubspace_Iio_Ioi`: for an injective symmetric
  operator the negative and positive spectral subspaces are complementary.
* `InnerProductSpace.apply_self_neg_of_mem_pointSpectralSubspace_Iio`,
  `InnerProductSpace.apply_self_pos_of_mem_pointSpectralSubspace_Ioi`: a real bilinear form with a
  self-adjoint Riesz operator is negative definite on the negative spectral subspace of that
  operator and positive definite on the positive one.
-/

public section

open Set
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : Module.End 𝕜 E}

/-- The quadratic form of a symmetric operator is negative definite on its negative spectral
subspace. -/
theorem re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio (hA : A.IsSymmetric) {x : E}
    (hx : x ∈ A.pointSpectralSubspace (Iio 0)) (hx0 : x ≠ 0) : RCLike.re ⟪A x, x⟫_𝕜 < 0 := by
  set U := A.pointSpectralSubspace (Iio 0)
  -- The finitely many eigenvalues carried by `U` are bounded above by some `a < 0`.
  have hfin := (A.finite_restrictedPointSpectrum U).insert (-1)
  have ha : sSup (insert (-1) (A.restrictedPointSpectrum U)) < 0 := by
    rcases (insert_nonempty _ _).csSup_mem hfin with h | h
    · rw [h]
      norm_num
    · exact Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp
        (A.pointSpectrumIn_pointSpectralSubspace (Iio 0)) h
  have hle := hA.re_inner_apply_self_le_of_pointSpectrumIn (U := U)
    (fun y hy ↦ Module.End.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hy))
    (Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mpr
      fun μ hμ ↦ le_csSup hfin.bddAbove (mem_insert_of_mem _ hμ)) hx
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  nlinarith

/-- The quadratic form of a symmetric operator is positive definite on its positive spectral
subspace. -/
theorem re_inner_apply_self_pos_of_mem_pointSpectralSubspace_Ioi (hA : A.IsSymmetric) {x : E}
    (hx : x ∈ A.pointSpectralSubspace (Ioi 0)) (hx0 : x ≠ 0) : 0 < RCLike.re ⟪A x, x⟫_𝕜 := by
  have hA' : (-A).IsSymmetric := fun y z ↦ by simp [hA y z]
  have h := hA'.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio
    (by rwa [Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero]) hx0
  simpa only [LinearMap.neg_apply, inner_neg_left, map_neg, neg_lt_zero] using h

/-- The quadratic form of a symmetric operator is positive semidefinite on the spectral subspace
of its nonnegative eigenvalues. -/
theorem re_inner_apply_self_nonneg_of_mem_pointSpectralSubspace_Ici (hA : A.IsSymmetric) {x : E}
    (hx : x ∈ A.pointSpectralSubspace (Ici 0)) : 0 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  simpa only [zero_mul] using hA.le_re_inner_apply_self_of_pointSpectrumIn
    (fun y hy ↦ Module.End.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hy))
    (A.pointSpectrumIn_pointSpectralSubspace (Ici 0)) hx

/-- The quadratic form of a symmetric operator is negative semidefinite on the spectral subspace
of its nonpositive eigenvalues. -/
theorem re_inner_apply_self_nonpos_of_mem_pointSpectralSubspace_Iic (hA : A.IsSymmetric) {x : E}
    (hx : x ∈ A.pointSpectralSubspace (Iic 0)) : RCLike.re ⟪A x, x⟫_𝕜 ≤ 0 := by
  simpa only [zero_mul] using hA.re_inner_apply_self_le_of_pointSpectrumIn
    (fun y hy ↦ Module.End.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hy))
    (A.pointSpectrumIn_pointSpectralSubspace (Iic 0)) hx

/-- For an injective symmetric operator, the negative and positive spectral subspaces are
complementary: the space is their direct sum. -/
theorem isCompl_pointSpectralSubspace_Iio_Ioi (hA : A.IsSymmetric) (hker : LinearMap.ker A = ⊥) :
    IsCompl (A.pointSpectralSubspace (Iio 0)) (A.pointSpectralSubspace (Ioi 0)) := by
  refine ⟨(hA.isOrtho_pointSpectralSubspace Ioi_disjoint_Iio_same.symm).disjoint,
    codisjoint_iff.mpr ?_⟩
  rw [← Module.End.pointSpectralSubspace_insert_zero (Ω := Ioi 0) hker, Ioi_insert, ← compl_Iio]
  exact hA.pointSpectralSubspace_sup_compl_eq_top _

end LinearMap.IsSymmetric

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- A real bilinear form with a self-adjoint Riesz operator is negative definite on the negative
spectral subspace of that operator. -/
theorem apply_self_neg_of_mem_pointSpectralSubspace_Iio
    (hB : IsSelfAdjoint (continuousLinearMapOfBilin B)) {u : E}
    (hu : u ∈ Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Iio 0))
    (hu0 : u ≠ 0) : B u u < 0 := by
  simpa [continuousLinearMapOfBilin_apply] using
    hB.isSymmetric.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio hu hu0

/-- A real bilinear form with a self-adjoint Riesz operator is positive definite on the positive
spectral subspace of that operator. -/
theorem apply_self_pos_of_mem_pointSpectralSubspace_Ioi
    (hB : IsSelfAdjoint (continuousLinearMapOfBilin B)) {u : E}
    (hu : u ∈ Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Ioi 0))
    (hu0 : u ≠ 0) : 0 < B u u := by
  simpa [continuousLinearMapOfBilin_apply] using
    hB.isSymmetric.re_inner_apply_self_pos_of_mem_pointSpectralSubspace_Ioi hu hu0

end InnerProductSpace
