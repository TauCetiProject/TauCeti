/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Totally real subspaces of complex modules

This file gives an elementary example of a totally real real subspace of a complex module. In
particular, choosing one complex vector in each coordinate produces a totally real subspace of a
product of copies of `ℂ`.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- **The real span of vectors, one in each coordinate, is totally real.** The image of the
real-linear map `τ ↦ (τ i • v i)ᵢ` from `ι → ℝ` to `ι → ℂ` meets its image under multiplication by
`i` only in `0`. -/
theorem isTotallyReal_range_pi_smulRight {v : ι → ℂ} :
    IsTotallyReal ((LinearMap.lsmul ℂ (ι → ℂ) Complex.I).restrictScalars ℝ)
      (LinearMap.range (LinearMap.pi fun i => (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight
        (v i))) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ ⟨τ, rfl⟩ ⟨_, ⟨σ, rfl⟩, hσ⟩
  funext i
  have h := congrFun hσ i
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.pi_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply, Complex.real_smul,
    smul_eq_mul] at h ⊢
  by_cases hi : v i = 0
  · simp [hi]
  · have h' : (σ i : ℂ) * Complex.I = τ i := mul_right_cancel₀ hi (by rw [← h]; ring)
    have hτ : τ i = 0 := by simpa using (congrArg Complex.re h').symm
    simp [hτ]

end TauCeti
