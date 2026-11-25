/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.DdbarHermitianForm

/-!
# Examples: eigenvalues of `i∂∂bar |z|²` relative to a Hermitian metric

On a complex inner product space `V` with the standard Hermitian metric `h = ⟪·, ·⟫`, the Hermitian
form of `i∂∂bar |z|²` is `2·h` (`TauCeti.ddbarHermitianForm_zero_form_norm_sq`). So its eigenvalue
vectors relative to `h` are exactly `2e = (2, …, 2)`, the normalization witness
`λ[i∂∂bar |z|²] = 2e`. Doubling the metric halves the eigenvalues: relative to `2·h` the same form
has the eigenvalue vector `e`, and no other.
-/

public section

open Complex Module TauCeti
open scoped Manifold

namespace TauCeti.DdbarHermitianFormExamples

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **`λ[i∂∂bar |z|²] = 2e`, and doubling the metric halves the eigenvalues.** Relative to the
standard metric `h`, the Hermitian form of `i∂∂bar |z|²` has the eigenvalue vector `(2, …, 2)` and
no other. Relative to `2·h`, the same form `2·h` has the eigenvalue vector `e` and no other. -/
example (x : V) :
    (∀ μ : Fin (finrank ℂ V) → ℝ, IsRelEigenvalueVector (fun u v : V ↦ inner ℂ u v)
      (ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x) μ ↔
        μ = fun _ ↦ 2) ∧
    ∀ μ : Fin (finrank ℂ V) → ℝ, IsRelEigenvalueVector (fun u v : V ↦ 2 * inner ℂ u v)
      (ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x) μ ↔ μ = 1 := by
  have hh : (innerₛₗ ℂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ).IsSymm := ⟨fun u v ↦ inner_conj_symm v u⟩
  have hpos (v : V) (hv : v ≠ 0) : 0 < RCLike.re (innerₛₗ ℂ v v) := by
    simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv
  have hh₂ : ((2 : ℂ) • innerₛₗ ℂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ).IsSymm :=
    ⟨fun u v ↦ by simp [← hh.eq u v, map_ofNat]⟩
  have hpos₂ (v : V) (hv : v ≠ 0) : 0 < RCLike.re (((2 : ℂ) • innerₛₗ ℂ) v v) := by
    simpa using mul_pos two_pos (hpos v hv)
  rw [funext₂ (ddbarHermitianForm_zero_form_norm_sq x)]
  exact ⟨fun μ ↦ by simpa using isRelEigenvalueVector_smul_self_iff hh hpos 2 (μ := μ),
    fun μ ↦ by simpa using isRelEigenvalueVector_self_iff hh₂ hpos₂ (μ := μ)⟩

end TauCeti.DdbarHermitianFormExamples
