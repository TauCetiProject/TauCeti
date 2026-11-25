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

/-- **`λ[i∂∂bar |z|²] = 2e`.** Relative to the standard metric, the Hermitian form of
`i∂∂bar |z|²` has the eigenvalue vector `(2, …, 2)` and no other. -/
example (x : V) {μ : Fin (finrank ℂ V) → ℝ} :
    IsRelEigenvalueVector (fun u v : V ↦ inner ℂ u v)
      (ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x) μ ↔
      μ = fun _ ↦ 2 := by
  have hform : ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x =
      fun u v ↦ ((2 : ℝ) : ℂ) * innerₛₗ ℂ u v := by
    ext u v
    rw [ddbarHermitianForm_zero_form_norm_sq, innerₛₗ_apply_apply, ofReal_ofNat]
  have hh : (innerₛₗ ℂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ).IsSymm := ⟨fun u v ↦ inner_conj_symm v u⟩
  have hpos (v : V) (hv : v ≠ 0) : 0 < RCLike.re (innerₛₗ ℂ v v) := by
    simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv
  rw [hform, show (fun u v : V ↦ inner ℂ u v) = fun u v ↦ innerₛₗ ℂ u v by
    ext u v; rw [innerₛₗ_apply_apply]]
  exact isRelEigenvalueVector_smul_self_iff hh hpos 2

/-- **Doubling the metric halves the eigenvalues.** Relative to `2·h`, the Hermitian form
`2·h` of `i∂∂bar |z|²` has the eigenvalue vector `e` and no other. -/
example (x : V) {μ : Fin (finrank ℂ V) → ℝ} :
    IsRelEigenvalueVector (fun u v : V ↦ 2 * inner ℂ u v)
      (ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x) μ ↔ μ = 1 := by
  have hform : ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x =
      fun u v ↦ ((2 : ℂ) • innerₛₗ ℂ) u v := by
    ext u v
    rw [ddbarHermitianForm_zero_form_norm_sq, LinearMap.smul_apply, LinearMap.smul_apply,
      innerₛₗ_apply_apply, smul_eq_mul]
  have hh : ((2 : ℂ) • innerₛₗ ℂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ).IsSymm :=
    ⟨fun u v ↦ by simp [inner_conj_symm, map_ofNat]⟩
  have hpos (v : V) (hv : v ≠ 0) : 0 < RCLike.re (((2 : ℂ) • innerₛₗ ℂ) v v) := by
    simpa [← Complex.ofReal_pow] using pow_pos (norm_pos_iff.2 hv) 2
  rw [hform, show (fun u v : V ↦ 2 * inner ℂ u v) = fun u v ↦ ((2 : ℂ) • innerₛₗ ℂ) u v by
    ext u v; simp]
  exact isRelEigenvalueVector_self_iff hh hpos

end TauCeti.DdbarHermitianFormExamples
