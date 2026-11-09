/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Spectral subspaces of a symmetric operator and the inertia of its form

Let `A` be a symmetric operator on a finite-dimensional inner product space. Its quadratic form
`x ↦ re ⟪A x, x⟫` is negative definite on the negative spectral subspace
`A.pointSpectralSubspace (Iio 0)`, positive definite on the positive spectral subspace
`A.pointSpectralSubspace (Ioi 0)` and positive semidefinite on `A.pointSpectralSubspace (Ici 0)`,
the orthogonal complement of the negative spectral subspace. Over `ℝ` this identifies the
indices of inertia of the form with the dimensions of the spectral subspaces: the negative index
`sigNeg` is the dimension of the negative spectral subspace, and the positive index `sigPos` is
the dimension of the positive one.

Together with the smooth dependence of the spectral projections on an invertible self-adjoint
operator (`TauCeti.Analysis.InnerProductSpace.Spectral.Projection`), this splits a smooth family of
nondegenerate symmetric bilinear forms into smooth families of negative and positive definite
subspaces of the dimensions prescribed by Sylvester's law of inertia.

## Main results

* `LinearMap.IsSymmetric.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio`,
  `LinearMap.IsSymmetric.re_inner_apply_self_pos_of_mem_pointSpectralSubspace_Ioi`: the form is
  negative definite on the negative spectral subspace and positive definite on the positive one.
* `LinearMap.IsSymmetric.re_inner_apply_self_nonneg_of_mem_pointSpectralSubspace_Ici`: the form is
  positive semidefinite on the spectral subspace of the nonnegative eigenvalues.
* `LinearMap.IsSymmetric.sigNeg_eq_finrank_pointSpectralSubspace_Iio`,
  `LinearMap.IsSymmetric.sigPos_eq_finrank_pointSpectralSubspace_Ioi`: the negative and positive
  indices of inertia of the form are the dimensions of the negative and positive spectral
  subspaces.
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

end LinearMap.IsSymmetric

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Module.End ℝ E} {Q : QuadraticForm ℝ E}

/-- **The negative index of inertia is the dimension of the negative spectral subspace.** If `Q`
is the quadratic form `x ↦ ⟪A x, x⟫` of a symmetric operator `A`, then `sigNeg Q` is the
dimension of `A.pointSpectralSubspace (Iio 0)`. -/
theorem sigNeg_eq_finrank_pointSpectralSubspace_Iio (hA : A.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ) :
    sigNeg Q = Module.finrank ℝ (A.pointSpectralSubspace (Iio 0)) := by
  set U := A.pointSpectralSubspace (Iio 0)
  refine le_antisymm ?_ (le_sigNeg_of_negDef Q fun x hx0 ↦ ?_)
  · -- `Q` is positive semidefinite on `Uᗮ`, so a negative definite subspace meets it trivially.
    have hle := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := Uᗮ) fun x hx ↦ by
      rw [hA.orthogonal_pointSpectralSubspace, compl_Iio] at hx
      simpa [hQ] using hA.re_inner_apply_self_nonneg_of_mem_pointSpectralSubspace_Ici hx
    rw [sigPos_neg] at hle
    have := U.finrank_add_finrank_orthogonal
    omega
  · have h := hA.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio x.2
      (by simpa using hx0)
    simpa [hQ] using h

/-- **The positive index of inertia is the dimension of the positive spectral subspace.** If `Q`
is the quadratic form `x ↦ ⟪A x, x⟫` of a symmetric operator `A`, then `sigPos Q` is the
dimension of `A.pointSpectralSubspace (Ioi 0)`. -/
theorem sigPos_eq_finrank_pointSpectralSubspace_Ioi (hA : A.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ) :
    sigPos Q = Module.finrank ℝ (A.pointSpectralSubspace (Ioi 0)) := by
  have hA' : (-A).IsSymmetric := fun y z ↦ by simp [hA y z]
  have h := hA'.sigNeg_eq_finrank_pointSpectralSubspace_Iio (Q := -Q) fun x ↦ by
    simp [hQ]
  rwa [sigNeg_neg, Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero] at h

end LinearMap.IsSymmetric
