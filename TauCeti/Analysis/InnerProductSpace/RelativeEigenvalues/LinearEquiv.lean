/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Sorted

/-!
# Relative eigenvalues under a linear change of variables

Relative eigenvalues do not depend on coordinates: for a linear equivalence `B` of `E`, the
forms `h(B ·, B ·)` and `a(B ·, B ·)` have the same eigenvalue vectors as `h` and `a`
(`TauCeti.isRelEigenvalueVector_comp_linearEquiv_iff`), hence the same sorted eigenvalue vector
(`TauCeti.relEigenvalueVector_comp_linearEquiv`). An `h`-orthonormal family diagonalizing `a` is
carried to one for the pulled-back forms by `B⁻¹`.
-/

public section

open Module

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Eigenvalue vectors are invariant under a linear change of variables.** -/
theorem isRelEigenvalueVector_comp_linearEquiv_iff (B : E ≃ₗ[𝕜] E) {h a : E → E → 𝕜}
    {μ : Fin (finrank 𝕜 E) → ℝ} :
    IsRelEigenvalueVector (fun u v ↦ h (B u) (B v)) (fun u v ↦ a (B u) (B v)) μ ↔
      IsRelEigenvalueVector h a μ := by
  simp only [isRelEigenvalueVector_def]
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨fun i ↦ B (b i), hb⟩, fun ⟨b, hb⟩ ↦ ⟨fun i ↦ B.symm (b i), ?_⟩⟩
  simpa only [LinearEquiv.apply_symm_apply] using hb

open Classical in
/-- **The sorted eigenvalue vector is invariant under a linear change of variables**:
`λ_{h(B ·, B ·)}[a(B ·, B ·)] = λ_h[a]`. -/
theorem relEigenvalueVector_comp_linearEquiv (B : E ≃ₗ[𝕜] E) (h a : E → E → 𝕜) :
    relEigenvalueVector (fun u v ↦ h (B u) (B v)) (fun u v ↦ a (B u) (B v)) =
      relEigenvalueVector h a := by
  simp only [relEigenvalueVector_def, isRelEigenvalueVector_comp_linearEquiv_iff]

end TauCeti
