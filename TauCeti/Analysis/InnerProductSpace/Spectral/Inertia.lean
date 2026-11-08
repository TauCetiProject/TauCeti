/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Spectral subspaces of a symmetric bilinear form and its indices of inertia

Let `B` be a symmetric bounded bilinear form on a finite-dimensional real inner product space `V`,
and let `B♯ = InnerProductSpace.continuousLinearMapOfBilin B` be its Riesz operator, characterized
by `⟪B♯ u, v⟫ = B u v`. The operator `B♯` is symmetric, so `V` is the orthogonal direct sum of its
eigenspaces. The point-spectral subspaces `Module.End.pointSpectralSubspace B♯ (Iio 0)` and
`Module.End.pointSpectralSubspace B♯ (Ioi 0)`, spanned by the eigenvectors of `B♯` with negative,
respectively positive, eigenvalues, split `B` into its negative and positive parts:

* `B` is negative definite on the first and positive definite on the second;
* point-spectral subspaces selected by disjoint sets of eigenvalues are orthogonal for `B` as well
  as for the inner product;
* the dimensions of the two subspaces are the negative and positive indices of inertia of `B`.

The subspaces depend on the inner product, but their dimensions do not, by Sylvester's law of
inertia. This is the linear algebra behind the negative and positive normal spaces of a Morse–Bott
critical submanifold, where `B` is the normal Hessian and the inner product is a metric.

## Main results

* `InnerProductSpace.apply_eq_zero_of_mem_pointSpectralSubspace`: point-spectral subspaces for
  disjoint sets of eigenvalues are `B`-orthogonal.
* `InnerProductSpace.apply_self_neg_of_mem_pointSpectralSubspace_Iio` and
  `InnerProductSpace.apply_self_pos_of_mem_pointSpectralSubspace_Ioi`: `B` is negative definite
  on the negative and positive definite on the positive point-spectral subspace.
* `InnerProductSpace.apply_self_nonneg_of_mem_pointSpectralSubspace_Ici`: `B` is positive
  semidefinite on the nonnegative point-spectral subspace.
* `InnerProductSpace.finrank_pointSpectralSubspace_Iio_zero` and
  `InnerProductSpace.finrank_pointSpectralSubspace_Ioi_zero`: their dimensions are the indices of
  inertia `sigNeg` and `sigPos` of `B`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 4.5.8 (Sylvester's law of inertia).
-/

public section

open Module Module.End Set
open scoped InnerProductSpace

namespace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Point-spectral subspaces of the Riesz operator of a symmetric form `B`, selected by disjoint
sets of eigenvalues, are orthogonal for `B`. -/
theorem apply_eq_zero_of_mem_pointSpectralSubspace (hB : ∀ u v, B u v = B v u) {Ω Ω' : Set ℝ}
    (h : Disjoint Ω Ω') {u v : V}
    (hu : u ∈ pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) Ω)
    (hv : v ∈ pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) Ω') :
    B u v = 0 := by
  have hBu : continuousLinearMapOfBilin B u ∈
      pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) Ω :=
    map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hu)
  rw [← continuousLinearMapOfBilin_apply]
  exact ((isSymmetric_continuousLinearMapOfBilin hB).isOrtho_pointSpectralSubspace h).inner_eq
    hBu hv

variable [FiniteDimensional ℝ V]

/-- A symmetric form is negative definite on the point-spectral subspace of its Riesz operator
spanned by the eigenvectors with negative eigenvalues. -/
theorem apply_self_neg_of_mem_pointSpectralSubspace_Iio (hB : ∀ u v, B u v = B v u) {v : V}
    (hv : v ∈ pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Iio 0))
    (hv0 : v ≠ 0) : B v v < 0 := by
  set A : Module.End ℝ V := (continuousLinearMapOfBilin B : V →ₗ[ℝ] V)
  set U := pointSpectralSubspace A (Iio 0)
  -- The eigenvalues of `A` on `U` form a finite subset of `(-∞, 0)`, so they are bounded above by
  -- some `a < 0`.
  obtain ⟨a, ha, hUa⟩ : ∃ a : ℝ, a < 0 ∧ A.PointSpectrumIn U (Iic a) := by
    have hfin := finite_restrictedPointSpectrum A U
    have hneg : A.restrictedPointSpectrum U ⊆ Iio 0 :=
      pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp
        (pointSpectrumIn_pointSpectralSubspace A _)
    simp only [pointSpectrumIn_iff_restrictedPointSpectrum_subset]
    rcases (A.restrictedPointSpectrum U).eq_empty_or_nonempty with he | hne
    · exact ⟨-1, by norm_num, by simp [he]⟩
    · refine ⟨hfin.toFinset.max' (hfin.toFinset_nonempty.mpr hne),
        hneg (hfin.mem_toFinset.mp (Finset.max'_mem _ _)), fun μ hμ ↦ ?_⟩
      exact Finset.le_max' _ _ (hfin.mem_toFinset.mpr hμ)
  have hle := (isSymmetric_continuousLinearMapOfBilin hB).re_inner_apply_self_le_of_pointSpectrumIn
    (fun x hx ↦ map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hx)) hUa hv
  simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe,
    continuousLinearMapOfBilin_apply] at hle
  have : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

/-- A symmetric form is positive definite on the point-spectral subspace of its Riesz operator
spanned by the eigenvectors with positive eigenvalues. -/
theorem apply_self_pos_of_mem_pointSpectralSubspace_Ioi (hB : ∀ u v, B u v = B v u) {v : V}
    (hv : v ∈ pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Ioi 0))
    (hv0 : v ≠ 0) : 0 < B v v := by
  have hneg : ∀ u w, (-B) u w = (-B) w u := fun u w ↦ by simp [hB u w]
  have hv' : v ∈ pointSpectralSubspace (continuousLinearMapOfBilin (-B) : V →ₗ[ℝ] V) (Iio 0) := by
    rw [continuousLinearMapOfBilin_neg, ContinuousLinearMap.toLinearMap_neg,
      pointSpectralSubspace_neg, neg_Iio, neg_zero]
    exact hv
  simpa using apply_self_neg_of_mem_pointSpectralSubspace_Iio hneg hv' hv0

/-- A symmetric form is positive semidefinite on the point-spectral subspace of its Riesz operator
spanned by the eigenvectors with nonnegative eigenvalues. -/
theorem apply_self_nonneg_of_mem_pointSpectralSubspace_Ici (hB : ∀ u v, B u v = B v u)
    {v : V} (hv : v ∈ pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Ici 0)) :
    0 ≤ B v v := by
  have hle := (isSymmetric_continuousLinearMapOfBilin hB).le_re_inner_apply_self_of_pointSpectrumIn
    (fun x hx ↦ map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hx))
    (pointSpectrumIn_pointSpectralSubspace _ _) hv
  simpa only [zero_mul, RCLike.re_to_real, ContinuousLinearMap.coe_coe,
    continuousLinearMapOfBilin_apply] using hle

/-- **The negative index of inertia is the number of negative eigenvalues.** The point-spectral
subspace of the Riesz operator of a symmetric form `B` spanned by the eigenvectors with negative
eigenvalues has dimension `sigNeg B`. -/
theorem finrank_pointSpectralSubspace_Iio_zero (hB : ∀ u v, B u v = B v u) :
    finrank ℝ (pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Iio 0)) =
      sigNeg B.toBilinForm.toQuadraticMap := by
  have hA := isSymmetric_continuousLinearMapOfBilin hB
  refine le_antisymm (le_sigNeg_of_negDef _ fun v hv ↦ ?_) ?_
  · -- The negative point-spectral subspace is negative definite.
    simpa using apply_self_neg_of_mem_pointSpectralSubspace_Iio hB v.2
      (by simpa using hv)
  · -- A negative-definite subspace meets the nonnegative point-spectral subspace trivially.
    have hsum := QuadraticForm.sigPos_add_finrank_le_of_nonpos
      (Q := -B.toBilinForm.toQuadraticMap)
      (V := pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Ici 0)) fun v hv ↦ by
        simpa using apply_self_nonneg_of_mem_pointSpectralSubspace_Ici hB hv
    have hcompl := Submodule.finrank_add_finrank_orthogonal
      (pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Iio 0))
    rw [hA.orthogonal_pointSpectralSubspace, compl_Iio] at hcompl
    rw [sigPos_neg] at hsum
    omega

/-- **The positive index of inertia is the number of positive eigenvalues.** The point-spectral
subspace of the Riesz operator of a symmetric form `B` spanned by the eigenvectors with positive
eigenvalues has dimension `sigPos B`. -/
theorem finrank_pointSpectralSubspace_Ioi_zero (hB : ∀ u v, B u v = B v u) :
    finrank ℝ (pointSpectralSubspace (continuousLinearMapOfBilin B : V →ₗ[ℝ] V) (Ioi 0)) =
      sigPos B.toBilinForm.toQuadraticMap := by
  have hneg : ∀ u w, (-B) u w = (-B) w u := fun u w ↦ by simp [hB u w]
  have h := finrank_pointSpectralSubspace_Iio_zero hneg
  rw [continuousLinearMapOfBilin_neg, ContinuousLinearMap.toLinearMap_neg,
    pointSpectralSubspace_neg, neg_Iio, neg_zero] at h
  have hQ : (-B).toBilinForm.toQuadraticMap = -B.toBilinForm.toQuadraticMap := by
    ext v
    simp
  rw [h, ← sigNeg_neg, hQ]

end InnerProductSpace
