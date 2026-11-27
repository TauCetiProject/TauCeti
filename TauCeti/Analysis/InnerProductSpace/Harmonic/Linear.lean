/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Continuous linear maps are harmonic

On a finite-dimensional real inner product space `E`, the Laplacian of a continuous linear map
`ℓ : E →L[ℝ] F` vanishes (`ContinuousLinearMap.laplacian`), so `ℓ` is harmonic everywhere. Together
with Mathlib's `InnerProductSpace.harmonicOnNhd_const` and `InnerProductSpace.HarmonicOnNhd.add`,
this makes every affine function, such as `x ↦ 1 + ⟪e, x⟫`, harmonic. Affine functions are the
basic test cases of the maximum principles and of Harnack's inequality.

## Main declarations

* `ContinuousLinearMap.harmonicAt`, `ContinuousLinearMap.harmonicOnNhd`: a continuous linear map
  is harmonic at every point.
-/

public section

open InnerProductSpace Laplacian

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map is harmonic at every point. -/
theorem harmonicAt (ℓ : E →L[ℝ] F) (x : E) : HarmonicAt (ℓ : E → F) x :=
  ⟨ℓ.contDiff.contDiffAt, by rw [ℓ.laplacian]⟩

/-- A continuous linear map is harmonic on a neighbourhood of every set. -/
theorem harmonicOnNhd (ℓ : E →L[ℝ] F) (s : Set E) : HarmonicOnNhd (ℓ : E → F) s :=
  fun x _ ↦ ℓ.harmonicAt x

end ContinuousLinearMap
