/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Continuous linear maps are harmonic

On a finite-dimensional real inner product space `E`, the second derivative of a continuous linear
map `ℓ : E →L[ℝ] F` vanishes, so its Laplacian vanishes and `ℓ` is harmonic everywhere. Together
with Mathlib's `InnerProductSpace.harmonicOnNhd_const` and `InnerProductSpace.HarmonicOnNhd.add`,
this makes every affine function, such as `x ↦ 1 + ⟪e, x⟫`, harmonic. Affine functions are the
basic test cases of the maximum principles and of Harnack's inequality.

## Main declarations

* `ContinuousLinearMap.laplacian_eq_zero`: the Laplacian of a continuous linear map vanishes.
* `ContinuousLinearMap.harmonicAt`, `ContinuousLinearMap.harmonicOnNhd`: a continuous linear map
  is harmonic at every point.
-/

public section

open InnerProductSpace Laplacian

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian of a continuous linear map vanishes. -/
@[simp]
theorem laplacian_eq_zero (ℓ : E →L[ℝ] F) : Δ (ℓ : E → F) = 0 := by
  have h : fderiv ℝ (ℓ : E → F) = fun _ ↦ ℓ := funext fun _ ↦ ℓ.fderiv
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply, h]

/-- A continuous linear map is harmonic at every point. -/
theorem harmonicAt (ℓ : E →L[ℝ] F) (x : E) : HarmonicAt (ℓ : E → F) x :=
  ⟨ℓ.contDiff.contDiffAt, by simp⟩

/-- A continuous linear map is harmonic on a neighbourhood of every set. -/
theorem harmonicOnNhd (ℓ : E →L[ℝ] F) (s : Set E) : HarmonicOnNhd (ℓ : E → F) s :=
  fun x _ ↦ ℓ.harmonicAt x

end ContinuousLinearMap
