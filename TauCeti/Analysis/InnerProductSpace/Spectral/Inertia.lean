/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.Frame
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature

/-!
# The index of inertia of a symmetric form and the spectrum of its Riesz operator

On a finite-dimensional real inner product space, a symmetric bilinear form `B` is represented by
the self-adjoint Riesz operator `continuousLinearMapOfBilin B`, with `⟪B♯ v, w⟫ = B v w`. In an
orthonormal eigenbasis of that operator the form is diagonal, with the eigenvalues as weights, so
by Sylvester's law of inertia (`LinearMap.IsSymmetric.sigNeg_eq_finrank_pointSpectralSubspace`)
its negative index of inertia `sigNeg` is the number of negative eigenvalues counted with
multiplicity: the dimension of the negative point-spectral subspace of the Riesz operator
(`InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`). Likewise its
positive index of inertia `sigPos` is the dimension of the positive point-spectral subspace
(`InnerProductSpace.finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`). Negating the
form exchanges the two spectral subspaces
(`InnerProductSpace.pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg`).

The spectral subspaces depend on the inner product, but they are natural for isometries: pulling
the form back along a linear isometry equivalence pulls them back
(`InnerProductSpace.pointSpectralSubspace_continuousLinearMapOfBilin_bilinearComp`), so in the
coordinates of an orthonormal basis they are the spectral subspaces of the form in coordinates
(`InnerProductSpace.pointSpectralSubspace_continuousLinearMapOfBilin_eq_map_synthesisMap`).

Their dimensions do not depend on the inner product. This identifies, for
instance, the ranks of the negative and positive spectral subbundles of a field of symmetric forms
with the index and coindex of the form.

The quadratic form `x ↦ re ⟪A x, x⟫` of a symmetric operator `A` on a
finite-dimensional inner product space is negative definite on the negative spectral subspace
`A.pointSpectralSubspace (Iio 0)`, positive definite on the positive spectral subspace
`A.pointSpectralSubspace (Ioi 0)`, positive semidefinite on `A.pointSpectralSubspace (Ici 0)` and
negative semidefinite on `A.pointSpectralSubspace (Iic 0)`. When `A` is injective the negative and
positive spectral subspaces are complementary. For the Riesz operator `B♯` of a real bilinear form
`B`, the form `B` itself is negative definite on the negative spectral subspace of `B♯` and positive
definite on the positive one. Together with the smooth dependence of the spectral projections on
an invertible self-adjoint operator (`TauCeti.Analysis.InnerProductSpace.Spectral.Projection`),
this splits a smooth family of nondegenerate symmetric bilinear forms into smooth families of
negative and positive definite subspaces of the dimensions prescribed by Sylvester's law of
inertia.

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

## References

* J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is
  reducible by real orthogonal substitutions to the form of a sum of positive and negative
  squares*, Philosophical Magazine (4) 4 (1852), 138–142.
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

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Negating a real bilinear form exchanges the negative and positive spectral subspaces of its
Riesz operator. -/
theorem pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg [CompleteSpace W]
    (B : W →L[ℝ] W →L[ℝ] ℝ) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (-B)).toLinearMap (Iio 0) =
      Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Ioi 0) := by
  rw [continuousLinearMapOfBilin_neg, ContinuousLinearMap.toLinearMap_neg,
    Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero]

/-- Pulling a real bilinear form back along a linear isometry equivalence `e` pulls the
point-spectral subspaces of its Riesz operator back along `e`. -/
theorem pointSpectralSubspace_continuousLinearMapOfBilin_bilinearComp [CompleteSpace W]
    {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [CompleteSpace W']
    (e : W' ≃ₗᵢ[ℝ] W) (B : W →L[ℝ] W →L[ℝ] ℝ) (Ω : Set ℝ) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin
        (B.bilinearComp (e : W' →L[ℝ] W) (e : W' →L[ℝ] W))).toLinearMap Ω =
      (Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap Ω).map
        (e.symm : W →ₗ[ℝ] W') := by
  have hconj : (continuousLinearMapOfBilin
      (B.bilinearComp (e : W' →L[ℝ] W) (e : W' →L[ℝ] W))).toLinearMap =
        e.symm.toLinearEquiv.conj (continuousLinearMapOfBilin B).toLinearMap := by
    rw [ContinuousLinearMap.continuousLinearMapOfBilin_bilinearComp]
    ext u
    simp [LinearEquiv.conj_apply]
  rw [hconj, Module.End.pointSpectralSubspace_conj]
  -- The two coercions of `e.symm` to a linear map agree by definition.
  rfl

/-- Read through the synthesis map of an orthonormal basis, the point-spectral subspaces of the
Riesz operator of a real bilinear form are the images of those of the form in coordinates. -/
theorem pointSpectralSubspace_continuousLinearMapOfBilin_eq_map_synthesisMap [CompleteSpace W]
    {ι : Type*} [Fintype ι] (B : W →L[ℝ] W →L[ℝ] ℝ) {v : ι → W} (hon : Orthonormal ℝ v)
    (hsp : ⊤ ≤ Submodule.span ℝ (range v)) (Ω : Set ℝ) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap Ω =
      (Module.End.pointSpectralSubspace (continuousLinearMapOfBilin
        (B.bilinearComp (TauCeti.synthesisMap ℝ v).toContinuousLinearMap
          (TauCeti.synthesisMap ℝ v).toContinuousLinearMap)).toLinearMap Ω).map
        (TauCeti.synthesisMap ℝ v) := by
  set b := OrthonormalBasis.mk hon hsp
  -- The synthesis map of `v` is the inverse coordinate map of the orthonormal basis `b`.
  have hv : TauCeti.synthesisMap ℝ v = b.repr.symm.toLinearMap := by
    rw [← OrthonormalBasis.synthesisMap_eq_repr_symm, OrthonormalBasis.coe_mk]
  have hS : (TauCeti.synthesisMap ℝ v).toContinuousLinearMap =
      (b.repr.symm : EuclideanSpace ℝ ι →L[ℝ] W) := by
    ext u
    simp [hv]
  rw [hS, pointSpectralSubspace_continuousLinearMapOfBilin_bilinearComp, ← Submodule.map_comp]
  convert (Submodule.map_id _).symm
  ext w
  simp [hv]

variable [FiniteDimensional ℝ W]

/-- **Sylvester's law of inertia, spectrally.** The negative index of inertia of a symmetric real
bilinear form on a finite-dimensional inner product space is the dimension of the negative
spectral subspace of its Riesz operator. -/
theorem finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ v w, B v w = B w v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin B).toLinearMap (Iio 0)) =
      sigNeg B.toBilinForm.toQuadraticMap :=
  (isSelfAdjoint_continuousLinearMapOfBilin hB).isSymmetric
    |>.sigNeg_eq_finrank_pointSpectralSubspace
      (fun v ↦ by simp [continuousLinearMapOfBilin_apply]) |>.symm

/-- **Sylvester's law of inertia, spectrally, positive part.** The positive index of inertia of a
symmetric real bilinear form on a finite-dimensional inner product space is the dimension of the
positive spectral subspace of its Riesz operator. -/
theorem finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ v w, B v w = B w v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin B).toLinearMap (Ioi 0)) =
      sigPos B.toBilinForm.toQuadraticMap :=
  (isSelfAdjoint_continuousLinearMapOfBilin hB).isSymmetric
    |>.sigPos_eq_finrank_pointSpectralSubspace
      (fun v ↦ by simp [continuousLinearMapOfBilin_apply]) |>.symm

/-- A real bilinear form with a self-adjoint Riesz operator is negative definite on the negative
spectral subspace of that operator. -/
theorem apply_self_neg_of_mem_pointSpectralSubspace_Iio
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : IsSelfAdjoint (continuousLinearMapOfBilin B)) {u : W}
    (hu : u ∈ Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Iio 0))
    (hu0 : u ≠ 0) : B u u < 0 := by
  simpa [continuousLinearMapOfBilin_apply] using
    hB.isSymmetric.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio hu hu0

/-- A real bilinear form with a self-adjoint Riesz operator is positive definite on the positive
spectral subspace of that operator. -/
theorem apply_self_pos_of_mem_pointSpectralSubspace_Ioi
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : IsSelfAdjoint (continuousLinearMapOfBilin B)) {u : W}
    (hu : u ∈ Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Ioi 0))
    (hu0 : u ≠ 0) : 0 < B u u := by
  simpa [continuousLinearMapOfBilin_apply] using
    hB.isSymmetric.re_inner_apply_self_pos_of_mem_pointSpectralSubspace_Ioi hu hu0

end InnerProductSpace
