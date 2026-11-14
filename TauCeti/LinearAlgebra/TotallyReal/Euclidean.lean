/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.LinearAlgebra.Matrix.OfReal
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Analysis.Matrix.Cayley

/-!
# The real subspace of `ℂⁿ` and its images under matrices

The real subspace `ℝⁿ ⊆ ℂⁿ` of vectors with real coordinates (`TauCeti.realSubspace`) is maximal
totally real. Its image `M ℝⁿ` under a complex matrix (`Matrix.realImage`) is the real span of the
columns of `M`. For invertible `M` it is again maximal totally real, and it only depends on `M` up
to right multiplication by an invertible real matrix: two invertible matrices with the same image
of `ℝⁿ` differ by such a matrix, which is orthogonal when both have columns orthonormal for the
real inner product `Re ⟪·, ·⟫`. For unitary `M` it is moreover isotropic for the standard
symplectic form `Im ⟪·, ·⟫` of `ℂⁿ`, hence Lagrangian.

For a real matrix `S`, the image of `ℝⁿ` under `S + i` is the subspace `{S y + i y | y ∈ ℝⁿ}`. It
meets `ℝⁿ` only in `0` and determines `S`, and for symmetric `S` it is Lagrangian. Every
Lagrangian subspace transverse to `ℝⁿ` arises in this way, as the graph of a symmetric matrix over
`i ℝⁿ` (McDuff–Salamon, Section 2.3), although that surjectivity is not needed and not proved here.

## Main declarations

* `TauCeti.realSubspace`: the real subspace `ℝⁿ ⊆ ℂⁿ`, which is maximal totally real
  (`TauCeti.isMaximalTotallyReal_realSubspace`). It is the orthogonal complement of `i ℝⁿ` for
  the real inner product `Re ⟪·, ·⟫`
  (`TauCeti.forall_re_inner_I_smul_eq_zero_iff_mem_realSubspace`).
* `Matrix.realImage`: the image `M ℝⁿ` of `ℝⁿ` under a complex matrix `M`, maximal totally real
  for invertible `M` (`Matrix.isMaximalTotallyReal_realImage`).
* `Matrix.realImage_mul_map_ofReal`, `Matrix.exists_eq_mul_map_ofReal`: `M ℝⁿ` determines an
  invertible `M` up to right multiplication by an invertible real matrix; in particular a nonzero
  real scalar does not change it (`Matrix.realImage_smul`).
* `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal`: for frames orthonormal for `Re ⟪·, ·⟫`,
  that real matrix is orthogonal.
* `Matrix.GeneralLinearGroup.realImage_ofEuclideanCLE`: the image of `ℝⁿ` under the matrix of a
  continuous linear automorphism of `ℂⁿ` is its image under the automorphism.
* `TauCeti.im_inner_eq_zero_of_mem_realImage`: the subspace `U ℝⁿ` is isotropic for
  `Im ⟪·, ·⟫` when `U` is unitary.
* `Matrix.lagrangianChartFrame`: the complex matrix `S + i` of a real matrix `S`, invertible for
  symmetric `S` (`Matrix.det_lagrangianChartFrame_ne_zero`).
* `Matrix.lagrangianChart`: the subspace `{S y + i y | y ∈ ℝⁿ}`, with its membership criterion
  (`Matrix.mem_lagrangianChart`). It meets `ℝⁿ` only in `0`
  (`Matrix.lagrangianChart_inf_realSubspace`) and determines `S` (`Matrix.lagrangianChart_inj`).
  For symmetric `S` it is maximal totally real (`Matrix.isMaximalTotallyReal_lagrangianChart`) and
  isotropic for `Im ⟪·, ·⟫` (`Matrix.im_inner_eq_zero_of_mem_lagrangianChart`), hence Lagrangian.
* `Matrix.lagrangianChartCLE`: for symmetric `S`, the automorphism `S + i` of `ℂⁿ`, mapping `ℝⁿ`
  onto the chart subspace (`Matrix.map_lagrangianChartCLE`) and continuous in `S`
  (`Matrix.continuous_lagrangianChartCLE`).
* `Matrix.lagrangianChart_smul_one`: the chart subspace of a scalar matrix `s` is the rotation
  `e^{iα} ℝⁿ` of `ℝⁿ` by the angle `α = π / 2 - arctan s` of `s + i`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the open cell of Lagrangians transverse to a fixed one as symmetric
  matrices).
-/

public section

noncomputable section

namespace TauCeti

variable (n : Type*)

/-- The real subspace `ℝⁿ ⊆ ℂⁿ` of vectors with real coordinates. -/
def realSubspace : Submodule ℝ (EuclideanSpace ℂ n) where
  carrier := {v | ∀ i, (v i).im = 0}
  add_mem' {v w} hv hw i := by simp [hv i, hw i]
  zero_mem' _ := by simp
  smul_mem' c v hv i := by simp [hv i]

variable {n}

/-- A vector lies in `ℝⁿ` exactly when all its coordinates are real. -/
@[simp]
theorem mem_realSubspace {v : EuclideanSpace ℂ n} : v ∈ realSubspace n ↔ ∀ i, (v i).im = 0 :=
  Iff.rfl

/-- The real subspace `ℝⁿ` is maximal totally real in `ℂⁿ`: every vector is uniquely the sum of
a real vector and `i` times a real vector. -/
theorem isMaximalTotallyReal_realSubspace :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ)
      (realSubspace n) := by
  rw [isMaximalTotallyReal_iff]
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨w, hw, rfl⟩
    ext i
    have h1 := hv i
    have h2 := hw i
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, PiLp.smul_apply,
      smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add] at h1 ⊢
    apply Complex.ext <;> simp [h1, h2]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let re : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ ((v i).re : ℂ)
    let im : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ ((v i).im : ℂ)
    refine Submodule.mem_sup.2 ⟨re, fun _ ↦ by simp [re], _, ⟨im, fun _ ↦ by simp [im], rfl⟩, ?_⟩
    ext i
    apply Complex.ext <;> simp [re, im]

open scoped InnerProductSpace in
/-- For the real subspace `ℝⁿ ⊆ ℂⁿ`, a vector `w` satisfies `Re ⟪i v, w⟫ = 0` for all `v ∈ ℝⁿ`
exactly when `w ∈ ℝⁿ`: the orthogonal complement of `i ℝⁿ` for `Re ⟪·, ·⟫` is `ℝⁿ`. -/
theorem forall_re_inner_I_smul_eq_zero_iff_mem_realSubspace [Fintype n]
    {w : EuclideanSpace ℂ n} :
    (∀ v ∈ realSubspace n, (⟪Complex.I • v, w⟫_ℂ).re = 0) ↔ w ∈ realSubspace n := by
  classical
  refine ⟨fun h ↦ mem_realSubspace.2 fun i ↦ ?_, fun hw v hv ↦ ?_⟩
  · have := h (EuclideanSpace.single i 1) <| mem_realSubspace.2 fun j ↦ by
      by_cases hj : j = i <;> simp [hj]
    simpa [inner_smul_left, EuclideanSpace.inner_single_left] using this
  · simp [inner_smul_left, PiLp.inner_apply, Complex.im_sum, Complex.mul_im,
      mem_realSubspace.1 hv _, mem_realSubspace.1 hw _]

end TauCeti

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The image `M ℝⁿ` of the real subspace `ℝⁿ ⊆ ℂⁿ` under a complex matrix `M`, the real span of
the columns of `M`. -/
def realImage (M : Matrix n n ℂ) : Submodule ℝ (EuclideanSpace ℂ n) :=
  (realSubspace n).map
    (((toEuclideanCLM (𝕜 := ℂ) M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ)

/-- The vectors of `M ℝⁿ` are the images under `M` of the real vectors. -/
theorem mem_realImage {M : Matrix n n ℂ} {v : EuclideanSpace ℂ n} :
    v ∈ M.realImage ↔ ∃ x ∈ realSubspace n, toEuclideanCLM (𝕜 := ℂ) M x = v := by
  simp [realImage]

/-- The image of `ℝⁿ` under an invertible matrix is its image under the continuous linear
equivalence of the matrix. -/
theorem realImage_eq_map_toEuclideanCLE {M : Matrix n n ℂ} (hM : M.det ≠ 0) :
    M.realImage = (realSubspace n).map
      (((M.toEuclideanCLE hM).toLinearEquiv :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) := by
  rw [realImage]
  congr 1
  ext v
  simp

/-- The image of `ℝⁿ` under an invertible matrix is maximal totally real. -/
theorem isMaximalTotallyReal_realImage {M : Matrix n n ℂ} (hM : M.det ≠ 0) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ)
      M.realImage := by
  rw [realImage_eq_map_toEuclideanCLE hM]
  exact isMaximalTotallyReal_realSubspace.map_linearEquiv _

/-- A real matrix maps `ℝⁿ` into itself. -/
theorem realImage_map_ofReal_le (N : Matrix n n ℝ) :
    (N.map ((↑) : ℝ → ℂ)).realImage ≤ realSubspace n := by
  rintro _ ⟨v, hv, rfl⟩ i
  simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
    toEuclideanCLM_apply_apply, map_apply, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  simp [(mem_realSubspace.1 hv)]

/-- The image of `ℝⁿ` under a product is the image under the left factor of its image under the
right factor. -/
theorem realImage_mul (M N : Matrix n n ℂ) :
    (M * N).realImage = N.realImage.map
      (((toEuclideanCLM (𝕜 := ℂ) M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) := by
  rw [realImage, realImage, ← Submodule.map_comp]
  congr 1
  ext v
  simp [map_mul]

/-- An invertible real matrix maps `ℝⁿ` onto itself. -/
@[simp]
theorem realImage_map_ofReal {N : Matrix n n ℝ} (hN : IsUnit N) :
    (N.map ((↑) : ℝ → ℂ)).realImage = realSubspace n := by
  refine le_antisymm (realImage_map_ofReal_le N) fun v hv ↦ ?_
  have hmul : N.map ((↑) : ℝ → ℂ) * N⁻¹.map ((↑) : ℝ → ℂ) = 1 :=
    (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans
      ((congrArg _ (mul_nonsing_inv N ((isUnit_iff_isUnit_det _).1 hN))).trans (map_one _))
  have h := congrArg (fun M : Matrix n n ℂ ↦ toEuclideanCLM (𝕜 := ℂ) M v) hmul
  simp only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] at h
  refine ⟨_, realImage_map_ofReal_le N⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  simpa using h

/-- Multiplying on the right by an invertible real matrix does not change `M ℝⁿ`. -/
@[simp]
theorem realImage_mul_map_ofReal (M : Matrix n n ℂ) {N : Matrix n n ℝ} (hN : IsUnit N) :
    (M * N.map ((↑) : ℝ → ℂ)).realImage = M.realImage := by
  rw [realImage_mul, realImage_map_ofReal hN, realImage]

/-- Multiplying by a nonzero real scalar does not change `M ℝⁿ`. -/
@[simp]
theorem realImage_smul (M : Matrix n n ℂ) {r : ℝ} (hr : r ≠ 0) :
    (r • M).realImage = M.realImage := by
  have h : r • M = M * (r • (1 : Matrix n n ℝ)).map ((↑) : ℝ → ℂ) := by
    rw [Matrix.map_smul _ _ (by simp), Matrix.map_one _ (by simp) (by simp), mul_smul_comm, mul_one]
  rw [h, realImage_mul_map_ofReal _ ((isUnit_iff_isUnit_det _).2 (by simp [hr]))]

/-- Two invertible complex matrices with the same image of `ℝⁿ` differ by a real matrix on the
right. -/
theorem exists_eq_mul_map_ofReal {M M' : GL n ℂ}
    (h : (M : Matrix n n ℂ).realImage = (M' : Matrix n n ℂ).realImage) :
    ∃ O : Matrix n n ℝ, (M' : Matrix n n ℂ) = M * O.map ((↑) : ℝ → ℂ) := by
  set X : Matrix n n ℂ := ((M⁻¹ : GL n ℂ) : Matrix n n ℂ) * M'
  have hX : ∀ i j, (X i j).im = 0 := by
    intro i j
    let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
    have he : e ∈ realSubspace n := fun k ↦ by
      by_cases hk : k = j <;> simp [e, PiLp.single_apply, hk]
    have hmem : toEuclideanCLM (𝕜 := ℂ) (M' : Matrix n n ℂ) e ∈ (M : Matrix n n ℂ).realImage :=
      h ▸ mem_realImage.2 ⟨e, he, rfl⟩
    obtain ⟨w, hw, hwe⟩ := mem_realImage.1 hmem
    have hXe : toEuclideanCLM (𝕜 := ℂ) X e = w := by
      rw [map_mul, mul_apply_eq_comp, ← hwe, ← mul_apply_eq_comp, ← map_mul, Units.inv_mul,
        map_one, one_apply_eq_self]
    have := congrArg (fun u : EuclideanSpace ℂ n ↦ u i) hXe
    simp only [toEuclideanCLM_apply_apply, e, PiLp.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    rw [this]
    exact hw i
  refine ⟨X.map Complex.re, ?_⟩
  have hX' : (X.map Complex.re).map ((↑) : ℝ → ℂ) = X := by
    ext i j
    apply Complex.ext <;> simp [hX i j]
  rw [hX', ← mul_assoc, Units.mul_inv, one_mul]

/-- Two invertible complex matrices with the same image of `ℝⁿ`, whose columns are orthonormal for
the real inner product `Re ⟪·, ·⟫`, differ by a real orthogonal matrix on the right. -/
theorem exists_mem_orthogonalGroup_eq_mul_map_ofReal {M M' : GL n ℂ}
    (h : (M : Matrix n n ℂ).realImage = (M' : Matrix n n ℂ).realImage)
    (hM : ((M : Matrix n n ℂ)ᴴ * M).map Complex.re = 1)
    (hM' : ((M' : Matrix n n ℂ)ᴴ * M').map Complex.re = 1) :
    ∃ O ∈ orthogonalGroup n ℝ, (M' : Matrix n n ℂ) = M * O.map ((↑) : ℝ → ℂ) := by
  obtain ⟨O, hO⟩ := exists_eq_mul_map_ofReal h
  refine ⟨O, (mem_orthogonalGroup_iff' n ℝ).2 ?_, hO⟩
  have := map_re_conjTranspose_mul_self_mul_map_ofReal (M : Matrix n n ℂ) O
  rwa [← hO, hM', hM, mul_one, eq_comm] at this

/-- The image of `ℝⁿ` under the matrix of a continuous linear automorphism of `ℂⁿ` is its image
under the automorphism. -/
theorem GeneralLinearGroup.realImage_ofEuclideanCLE
    (D : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n) :
    (GeneralLinearGroup.ofEuclideanCLE D : Matrix n n ℂ).realImage =
      (realSubspace n).map ((D.toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] _).restrictScalars ℝ) := by
  rw [realImage_eq_map_toEuclideanCLE (GeneralLinearGroup.ofEuclideanCLE D).det_ne_zero,
    GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE]

end Matrix

namespace TauCeti

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The image of `ℝⁿ` under a unitary matrix is isotropic for the standard symplectic form
`Im ⟪·, ·⟫` of `ℂⁿ`; being maximal totally real, it is a Lagrangian subspace. -/
theorem im_inner_eq_zero_of_mem_realImage {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    {v w : EuclideanSpace ℂ n} (hv : v ∈ U.realImage) (hw : w ∈ U.realImage) :
    (inner ℂ v w).im = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_realImage.1 hv
  obtain ⟨y, hy, rfl⟩ := mem_realImage.1 hw
  simp only [mem_unitaryGroup_iff_inner_toEuclideanCLM.1 hU x y, PiLp.inner_apply,
    Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  simp [Complex.mul_im, (mem_realSubspace.1 hx) i, (mem_realSubspace.1 hy) i]

end TauCeti

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex matrix `S + i` of a real matrix `S`. It maps `ℝⁿ` onto the subspace
`{S y + i y | y ∈ ℝⁿ}`, and it is invertible when `S` is symmetric. -/
def lagrangianChartFrame (S : Matrix n n ℝ) : Matrix n n ℂ :=
  S.map ((↑) : ℝ → ℂ) + Complex.I • 1

omit [Fintype n] in
/-- The complex matrix `S + i` is `S` cast to `ℂ` plus `i` times the identity. -/
theorem lagrangianChartFrame_def (S : Matrix n n ℝ) :
    S.lagrangianChartFrame = S.map ((↑) : ℝ → ℂ) + Complex.I • 1 :=
  (rfl)

omit [Fintype n] in
/-- The entries of `S + i`. -/
theorem lagrangianChartFrame_apply (S : Matrix n n ℝ) (i j : n) :
    S.lagrangianChartFrame i j = S i j + Complex.I * (1 : Matrix n n ℂ) i j := by
  simp [lagrangianChartFrame]

/-- `(S + i) (S - i) = S² + 1`. -/
theorem lagrangianChartFrame_mul (S : Matrix n n ℝ) :
    S.lagrangianChartFrame * (S.map ((↑) : ℝ → ℂ) - Complex.I • 1) =
      (S * S + 1).map ((↑) : ℝ → ℂ) := by
  have h : (S * S).map ((↑) : ℝ → ℂ) = S.map (↑) * S.map (↑) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [lagrangianChartFrame, Matrix.map_add _ Complex.ofReal_add, h,
    Matrix.map_one _ (by simp) (by simp)]
  simp [add_mul, mul_sub, smul_smul]
  abel

/-- For a symmetric real matrix `S`, the matrix `S + i = i (1 - i S)` is invertible, as `1 - i S`
is for the Hermitian matrix `S`. -/
theorem det_lagrangianChartFrame_ne_zero {S : Matrix n n ℝ} (hS : S.IsSymm) :
    S.lagrangianChartFrame.det ≠ 0 := by
  have h : S.lagrangianChartFrame = Complex.I • (1 - Complex.I • S.map ((↑) : ℝ → ℂ)) := by
    rw [lagrangianChartFrame, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add,
      add_comm]
  rw [h, det_smul]
  exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
    (isHermitian_iff_isSymm.2 hS).map_ofReal.isUnit_det_one_sub_I_smul.ne_zero

/-- The subspace `{S y + i y | y ∈ ℝⁿ}` of `ℂⁿ`, the image of `ℝⁿ` under `S + i`. For symmetric
`S` it is a Lagrangian subspace transverse to `ℝⁿ`. -/
def lagrangianChart (S : Matrix n n ℝ) : Submodule ℝ (EuclideanSpace ℂ n) :=
  S.lagrangianChartFrame.realImage

/-- The subspace `{S y + i y | y ∈ ℝⁿ}` is the image of `ℝⁿ` under `S + i`. -/
theorem lagrangianChart_def (S : Matrix n n ℝ) :
    S.lagrangianChart = S.lagrangianChartFrame.realImage :=
  (rfl)

/-- The coordinates of `(S + i) x`. -/
private theorem lagrangianChartFrame_mulVec_apply (S : Matrix n n ℝ) (x : n → ℂ) (i : n) :
    (S.lagrangianChartFrame *ᵥ x) i = ∑ j, (S i j : ℂ) * x j + Complex.I * x i := by
  simp [lagrangianChartFrame, mulVec, dotProduct, add_mul, Finset.sum_add_distrib,
    Matrix.one_apply]

/-- A vector lies in `{S y + i y | y ∈ ℝⁿ}` exactly when its real part is `S` applied to its
imaginary part. -/
theorem mem_lagrangianChart {S : Matrix n n ℝ} {v : EuclideanSpace ℂ n} :
    v ∈ S.lagrangianChart ↔ ∀ i, (v i).re = ∑ j, S i j * (v j).im := by
  rw [lagrangianChart, mem_realImage]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp [lagrangianChartFrame_mulVec_apply, Complex.re_sum, Complex.im_sum,
      mem_realSubspace.1 hx]
  · intro hv
    let y : EuclideanSpace ℂ n := WithLp.toLp 2 fun j ↦ ((v j).im : ℂ)
    refine ⟨y, mem_realSubspace.2 fun _ ↦ by simp [y], ?_⟩
    ext i
    apply Complex.ext
    · simp [lagrangianChartFrame_mulVec_apply, y, hv i, Complex.re_sum]
    · simp [lagrangianChartFrame_mulVec_apply, y, Complex.im_sum]

/-- The subspace `{S y + i y | y ∈ ℝⁿ}` meets `ℝⁿ` only in `0`. -/
theorem lagrangianChart_inf_realSubspace (S : Matrix n n ℝ) :
    S.lagrangianChart ⊓ realSubspace n = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v ⟨hv, hv'⟩ ↦ ?_
  have him := mem_realSubspace.1 hv'
  ext i
  apply Complex.ext
  · simp [mem_lagrangianChart.1 hv i, him]
  · simp [him i]

/-- The subspace `{S y + i y | y ∈ ℝⁿ}` determines `S`. -/
theorem lagrangianChart_injective :
    Function.Injective (lagrangianChart : Matrix n n ℝ → Submodule ℝ (EuclideanSpace ℂ n)) := by
  intro S T h
  ext i j
  -- Test both subspaces on the vector `S eⱼ + i eⱼ`.
  let v : EuclideanSpace ℂ n :=
    WithLp.toLp 2 fun k ↦ (S k j : ℂ) + Complex.I * (if k = j then 1 else 0)
  have hv : v ∈ S.lagrangianChart := mem_lagrangianChart.2 fun k ↦ by
    simp [v, apply_ite]
  have := (mem_lagrangianChart.1 (h ▸ hv)) i
  simpa [v, apply_ite] using this

/-- Two chart subspaces `{S y + i y | y ∈ ℝⁿ}` agree exactly when the matrices agree. -/
@[simp]
theorem lagrangianChart_inj {S T : Matrix n n ℝ} : S.lagrangianChart = T.lagrangianChart ↔ S = T :=
  lagrangianChart_injective.eq_iff

/-- For symmetric `S`, the subspace `{S y + i y | y ∈ ℝⁿ}` is isotropic for the standard symplectic
form `Im ⟪·, ·⟫` of `ℂⁿ`; being maximal totally real, it is Lagrangian. -/
theorem im_inner_eq_zero_of_mem_lagrangianChart {S : Matrix n n ℝ} (hS : S.IsSymm)
    {v w : EuclideanSpace ℂ n} (hv : v ∈ S.lagrangianChart) (hw : w ∈ S.lagrangianChart) :
    (inner ℂ v w).im = 0 := by
  have hv' := mem_lagrangianChart.1 hv
  have hw' := mem_lagrangianChart.1 hw
  simp only [PiLp.inner_apply, Complex.im_sum, RCLike.inner_apply, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, hv', hw', Finset.sum_mul, Finset.mul_sum]
  -- The two double sums agree by the symmetry of `S`.
  have key : ∑ x, ∑ i, (w x).im * (S x i * (v i).im) =
      ∑ x, ∑ i, S x i * (w i).im * (v x).im := by
    have := hS.dotProduct_mulVec_comm (x := fun i ↦ (w i).im) (y := fun i ↦ (v i).im)
    simp only [dotProduct, mulVec, Finset.mul_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  simp only [Finset.sum_add_distrib, key, mul_neg, Finset.sum_neg_distrib, neg_add_cancel]

/-- For symmetric `S`, the subspace `{S y + i y | y ∈ ℝⁿ}` is maximal totally real. -/
theorem isMaximalTotallyReal_lagrangianChart {S : Matrix n n ℝ} (hS : S.IsSymm) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ)
      S.lagrangianChart :=
  isMaximalTotallyReal_realImage (det_lagrangianChartFrame_ne_zero hS)

/-- For symmetric `S`, the continuous linear automorphism `S + i` of `ℂⁿ`. It maps `ℝⁿ` onto
`{S y + i y | y ∈ ℝⁿ}` (`Matrix.map_lagrangianChartCLE`). -/
def lagrangianChartCLE {S : Matrix n n ℝ} (hS : S.IsSymm) :
    EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n :=
  S.lagrangianChartFrame.toEuclideanCLE (det_lagrangianChartFrame_ne_zero hS)

/-- The automorphism `S + i` maps `ℝⁿ` onto `{S y + i y | y ∈ ℝⁿ}`. -/
@[simp]
theorem map_lagrangianChartCLE {S : Matrix n n ℝ} (hS : S.IsSymm) :
    (realSubspace n).map (((lagrangianChartCLE hS).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) = S.lagrangianChart :=
  (realImage_eq_map_toEuclideanCLE _).symm

/-- The automorphism `S + i` acts as the matrix `S + i`. -/
@[simp]
theorem lagrangianChartCLE_apply {S : Matrix n n ℝ} (hS : S.IsSymm) (x : EuclideanSpace ℂ n) :
    lagrangianChartCLE hS x = S.lagrangianChartFrame.toEuclideanLin x :=
  toEuclideanCLE_apply _ _ x

/-- The automorphism `S + i`, as a continuous linear map, is the continuous linear map of the
matrix `S + i`. -/
@[simp]
theorem coe_lagrangianChartCLE {S : Matrix n n ℝ} (hS : S.IsSymm) :
    (lagrangianChartCLE hS : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) =
      toEuclideanCLM (𝕜 := ℂ) S.lagrangianChartFrame :=
  coe_toEuclideanCLE _ _

/-- The automorphisms `S x + i` of `ℂⁿ` depend continuously on a continuous family `S x` of
symmetric real matrices. -/
theorem continuous_lagrangianChartCLE {X : Type*} [TopologicalSpace X] {S : X → Matrix n n ℝ}
    (hS : Continuous S) (hS' : ∀ x, (S x).IsSymm) :
    Continuous fun x ↦
      (lagrangianChartCLE (hS' x) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
  simp only [coe_lagrangianChartCLE, lagrangianChartFrame_def]
  exact continuous_toEuclideanCLM.comp
    ((hS.matrix_map Complex.continuous_ofReal).add continuous_const)

omit [Fintype n] in
/-- The complex matrix `S + i` of a scalar matrix `s` is the scalar `s + i`. -/
theorem lagrangianChartFrame_smul_one (s : ℝ) :
    (s • (1 : Matrix n n ℝ)).lagrangianChartFrame = ((s : ℂ) + Complex.I) • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [lagrangianChartFrame, hij]

/-- For a nonzero scalar `z`, the rotated subspace `z ℝⁿ` is maximal totally real. -/
theorem isMaximalTotallyReal_realImage_smul_one {z : ℂ} (hz : z ≠ 0) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ)
      (z • (1 : Matrix n n ℂ)).realImage :=
  isMaximalTotallyReal_realImage (by simp [hz])

open Real in
/-- The chart subspace `{s y + i y | y ∈ ℝⁿ}` of a scalar matrix is the rotation `e^{iα} ℝⁿ` of
`ℝⁿ` by the angle `α = π / 2 - arctan s ∈ (0, π)` of `s + i`. -/
theorem lagrangianChart_smul_one (s : ℝ) :
    (s • (1 : Matrix n n ℝ)).lagrangianChart =
      (Complex.exp ((π / 2 - arctan s : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realImage := by
  have hpolar : (s : ℂ) + Complex.I =
      (√(1 + s ^ 2) : ℂ) * Complex.exp ((π / 2 - arctan s : ℝ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_pi_div_two_sub,
      sin_pi_div_two_sub, sin_arctan, cos_arctan]
    have h : √(1 + s ^ 2) ≠ 0 := by positivity
    apply Complex.ext <;> simp <;> field_simp
  rw [lagrangianChart_def, lagrangianChartFrame_smul_one, hpolar,
    ← smul_smul, Complex.coe_smul, realImage_smul _ (by positivity)]

open Real in
/-- The chart subspace of `1` is `e^{iπ/4} ℝⁿ`. -/
theorem lagrangianChart_one :
    (1 : Matrix n n ℝ).lagrangianChart =
      (Complex.exp ((π / 4 : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realImage := by
  rw [← one_smul ℝ (1 : Matrix n n ℝ), lagrangianChart_smul_one, arctan_one,
    show π / 2 - π / 4 = π / 4 by ring]

open Real in
/-- The chart subspace of `-1` is `e^{-iπ/4} ℝⁿ`. -/
theorem lagrangianChart_neg_one :
    (-1 : Matrix n n ℝ).lagrangianChart =
      (Complex.exp ((-(π / 4) : ℝ) * Complex.I) • (1 : Matrix n n ℂ)).realImage := by
  -- The angle of `-1 + i` is `3π/4`, and `e^{3πi/4} = -e^{-πi/4}`.
  have h : Complex.exp ((π / 2 - -(π / 4) : ℝ) * Complex.I) =
      ((-1 : ℝ) : ℂ) * Complex.exp ((-(π / 4) : ℝ) * Complex.I) := by
    rw [show π / 2 - -(π / 4) = -(π / 4) + π by ring, Complex.ofReal_add, add_mul, Complex.exp_add,
      Complex.exp_pi_mul_I]
    push_cast
    ring
  rw [← neg_one_smul ℝ (1 : Matrix n n ℝ), lagrangianChart_smul_one, arctan_neg, arctan_one, h,
    ← smul_smul, Complex.coe_smul, realImage_smul _ (by norm_num)]

end Matrix
