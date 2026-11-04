/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.LinearAlgebra.Matrix.OfReal
public import TauCeti.LinearAlgebra.TotallyReal.Complex

/-!
# The real subspace of `ℂⁿ` and its images under matrices

The real subspace `ℝⁿ ⊆ ℂⁿ` of vectors with real coordinates (`TauCeti.realSubspace`) is maximal
totally real. Its image `M ℝⁿ` under a complex matrix (`Matrix.realImage`) is the real span of the
columns of `M`. For invertible `M` it is again maximal totally real, and it only depends on `M` up
to right multiplication by an invertible real matrix: two invertible matrices with the same image
of `ℝⁿ` differ by such a matrix.

## Main declarations

* `TauCeti.realSubspace`: the real subspace `ℝⁿ ⊆ ℂⁿ`, which is maximal totally real
  (`TauCeti.isMaximalTotallyReal_realSubspace`).
* `Matrix.realImage`: the image `M ℝⁿ` of `ℝⁿ` under a complex matrix `M`, maximal totally real
  for invertible `M` (`Matrix.isMaximalTotallyReal_realImage`).
* `Matrix.realImage_mul_map_ofReal`, `Matrix.exists_eq_mul_map_ofReal`: `M ℝⁿ` determines an
  invertible `M` up to right multiplication by an invertible real matrix.
-/

public section

noncomputable section

namespace TauCeti

variable (n : Type*)

/-- The real subspace `ℝⁿ ⊆ ℂⁿ` of vectors with real coordinates. -/
def realSubspace : Submodule ℝ (EuclideanSpace ℂ n) where
  carrier := {v | ∀ i, (v i).im = 0}
  add_mem' {v w} hv hw i := by simp [hv i, hw i]
  zero_mem' i := by simp
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
    refine Submodule.mem_sup.2 ⟨re, fun i ↦ by simp [re], _, ⟨im, fun i ↦ by simp [im], rfl⟩, ?_⟩
    ext i
    apply Complex.ext <;> simp [re, im]

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
theorem realImage_map_ofReal {N : Matrix n n ℝ} (hN : IsUnit N) :
    (N.map ((↑) : ℝ → ℂ)).realImage = realSubspace n := by
  refine le_antisymm (realImage_map_ofReal_le N) fun v hv ↦ ?_
  have hmul : N.map ((↑) : ℝ → ℂ) * N⁻¹.map ((↑) : ℝ → ℂ) = 1 := by
    rw [← map_ofReal_mul, mul_nonsing_inv N ((isUnit_iff_isUnit_det _).1 hN), map_ofReal_one]
  have h := congrArg (fun M : Matrix n n ℂ ↦ toEuclideanCLM (𝕜 := ℂ) M v) hmul
  simp only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] at h
  refine ⟨_, realImage_map_ofReal_le N⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  simpa using h

/-- Multiplying on the right by an invertible real matrix does not change `M ℝⁿ`. -/
theorem realImage_mul_map_ofReal (M : Matrix n n ℂ) {N : Matrix n n ℝ} (hN : IsUnit N) :
    (M * N.map ((↑) : ℝ → ℂ)).realImage = M.realImage := by
  rw [realImage_mul, realImage_map_ofReal hN, realImage]

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

end Matrix
