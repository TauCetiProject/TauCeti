/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Sorted
public import TauCeti.Geometry.Manifold.Complex.DdbarHermitianForm

/-!
# Eigenvalue functions and the complex Laplacian on a Hermitian manifold

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)` with a Hermitian metric `κ`, a smooth two-form
compatible with multiplication by `i`, whose Hermitian form at `x` is the inner product `h_x`
(`TauCeti.twoFormHermitianForm`). For a real two-form `α` and a real function `φ`, the
**eigenvalue function** `x ↦ λ_κ[α + i ∂∂bar φ](x)` (`TauCeti.relEigenvalueFunction`) is the
decreasingly sorted eigenvalue vector of the Hermitian form
`H_{α + i ∂∂bar φ}(x) = H_α(x) + 2·L_φ(x)` (`TauCeti.ddbarHermitianForm`) relative to `h_x`
(`TauCeti.relEigenvalueVector`). With `φ = 0` it is `λ_κ[α]`, and with `α = 0` it is
`λ_κ[i ∂∂bar φ]`. The **complex Laplacian** of `φ` (`TauCeti.complexLaplacian`) is
`Δ_κ φ = Σ_j λ_j[i ∂∂bar φ]`.

## Main definitions

* `TauCeti.relEigenvalueFunction E κ α φ x`: the eigenvalue vector `λ_κ[α + i ∂∂bar φ](x)`.
* `TauCeti.complexLaplacian E κ φ x`: the complex Laplacian `Δ_κ φ(x)`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.isRelEigenvalueVector_relEigenvalueFunction`: where `α` has
  type (1,1) and `φ` is `C²`, `λ_κ[α + i ∂∂bar φ](x)` is an eigenvalue vector of
  `H_{α + i ∂∂bar φ}(x)` relative to `h_x`.
* `TauCeti.SmoothTwoForm.Compatible.relEigenvalueFunction_self`: `λ_κ[κ] = e`.
* `TauCeti.SmoothTwoForm.Compatible.relEigenvalueFunction_add_smul`:
  `λ_κ[α + t·κ + i ∂∂bar φ] = λ_κ[α + i ∂∂bar φ] + t·e`.
* `TauCeti.SmoothTwoForm.Compatible.complexLaplacian_const`: `Δ_κ c = 0` for a constant `c`.
* `TauCeti.SmoothTwoForm.Compatible.complexLaplacian_eq_two_mul_sum`: `Δ_κ φ = 2·tr_h L_φ`, that is
  `Δ_κ φ(x) = 2·Σ_j Re L_φ(x)(b_j, b_j)` for any `h_x`-orthonormal basis `b`.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), Section 2.
-/

public section

open Complex Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

variable (E) in
/-- The **eigenvalue function** `λ_κ[α + i ∂∂bar φ](x)`: the decreasingly sorted eigenvalue vector
of the Hermitian form `H_{α + i ∂∂bar φ}(x)` relative to the Hermitian form `h_x` of `κ`. -/
def relEigenvalueFunction (κ : SmoothTwoForm 𝓘(ℝ, E) X) (α : RoughForm 𝓘(ℝ, E) X ℝ 2)
    (φ : X → ℝ) (x : X) : Fin (finrank ℂ E) → ℝ :=
  relEigenvalueVector (twoFormHermitianForm E κ.val x) (ddbarHermitianForm E α φ x)

variable (E) in
/-- The **complex Laplacian** `Δ_κ φ(x) = Σ_j λ_j[i ∂∂bar φ](x)` relative to the Hermitian
metric `κ`. -/
def complexLaplacian (κ : SmoothTwoForm 𝓘(ℝ, E) X) (φ : X → ℝ) (x : X) : ℝ :=
  ∑ j, relEigenvalueFunction E κ 0 φ x j

/-- Unfolding lemma for `relEigenvalueFunction`. -/
theorem relEigenvalueFunction_def (κ : SmoothTwoForm 𝓘(ℝ, E) X) (α : RoughForm 𝓘(ℝ, E) X ℝ 2)
    (φ : X → ℝ) (x : X) : relEigenvalueFunction E κ α φ x =
      relEigenvalueVector (twoFormHermitianForm E κ.val x) (ddbarHermitianForm E α φ x) :=
  (rfl)

/-- Unfolding lemma for `complexLaplacian`. -/
theorem complexLaplacian_def (κ : SmoothTwoForm 𝓘(ℝ, E) X) (φ : X → ℝ) (x : X) :
    complexLaplacian E κ φ x = ∑ j, relEigenvalueFunction E κ 0 φ x j :=
  (rfl)

/-- The eigenvalue function is sorted decreasingly. -/
theorem antitone_relEigenvalueFunction (κ : SmoothTwoForm 𝓘(ℝ, E) X)
    (α : RoughForm 𝓘(ℝ, E) X ℝ 2) (φ : X → ℝ) (x : X) :
    Antitone (relEigenvalueFunction E κ α φ x) :=
  antitone_relEigenvalueVector _ _

namespace SmoothTwoForm

variable {κ : SmoothTwoForm 𝓘(ℝ, E) X}
  {α : RoughForm 𝓘(ℝ, E) X ℝ 2} {φ : X → ℝ} {x : X}

variable (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X))
include hκ

/-- **The eigenvalue function is an eigenvalue vector.** Where `α` has type (1,1) and `φ` is `C²`,
`λ_κ[α + i ∂∂bar φ](x)` is an eigenvalue vector of `H_{α + i ∂∂bar φ}(x)` relative to `h_x`. -/
theorem Compatible.isRelEigenvalueVector_relEigenvalueFunction
    (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v])
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x) :
    IsRelEigenvalueVector (twoFormHermitianForm E κ.val x) (ddbarHermitianForm E α φ x)
      (relEigenvalueFunction E κ α φ x) := by
  rw [relEigenvalueFunction_def, ← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x),
    ← coe_ddbarSesqForm hα]
  exact isRelEigenvalueVector_relEigenvalueVector (hκ.invariant.isSymm_twoFormSesqForm x)
    (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x) (isSymm_ddbarSesqForm hα hφ)

/-- **`λ_κ[κ] = e`.** -/
theorem Compatible.relEigenvalueFunction_self (x : X) :
    relEigenvalueFunction E κ κ.val 0 x = 1 := by
  rw [relEigenvalueFunction_def, ddbarHermitianForm_zero,
    ← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x)]
  exact relEigenvalueVector_self (hκ.invariant.isSymm_twoFormSesqForm x)
    (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x)

/-- **Shifting by the metric shifts the eigenvalues**: where `α` has type (1,1) and `φ` is `C²`,
`λ_κ[α + t·κ + i ∂∂bar φ] = λ_κ[α + i ∂∂bar φ] + t·e`. -/
theorem Compatible.relEigenvalueFunction_add_smul
    (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v])
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x) (t : ℝ) :
    relEigenvalueFunction E κ (α + t • κ.val) φ x =
      relEigenvalueFunction E κ α φ x + fun _ ↦ t := by
  have hform : ddbarHermitianForm E (α + t • κ.val) φ x =
      fun u v ↦ (ddbarSesqForm E φ hα + (t : ℂ) •
        twoFormSesqForm E κ.val x (hκ.invariant.apply_I_smul_I_smul x)) u v := by
    ext u v
    simp [ddbarHermitianForm_add_form, twoFormHermitianForm_smul, RCLike.real_smul_eq_coe_mul]
  rw [relEigenvalueFunction_def, relEigenvalueFunction_def, hform,
    ← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x), ← coe_ddbarSesqForm hα]
  exact relEigenvalueVector_add_smul_self (hκ.invariant.isSymm_twoFormSesqForm x)
    (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x) (isSymm_ddbarSesqForm hα hφ) t

/-- **The complex Laplacian of a constant vanishes.** -/
theorem Compatible.complexLaplacian_const (c : ℝ) (x : X) :
    complexLaplacian E κ (fun _ ↦ c) x = 0 := by
  have h0 : ddbarHermitianForm E 0 (fun _ ↦ c) x = ((0 : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) · ·) := by
    ext u v
    simp
  rw [complexLaplacian_def]
  simp only [relEigenvalueFunction_def, h0]
  rw [← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x),
    relEigenvalueVector_zero (hκ.invariant.isSymm_twoFormSesqForm x)
      (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x)]
  simp

/-- **The complex Laplacian is twice the trace of the Levi form**: if `φ` is `C²` at `x`, then
`Δ_κ φ(x) = 2·Σ_j Re L_φ(x)(b_j, b_j)` for any family `b` orthonormal for `h_x`. -/
theorem Compatible.complexLaplacian_eq_two_mul_sum (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x)
    (b : Fin (finrank ℂ E) → E)
    (hb : ∀ i j, twoFormHermitianForm E κ.val x (b i) (b j) = if i = j then 1 else 0) :
    complexLaplacian E κ φ x = 2 * ∑ j, (manifoldLeviForm E φ x (b j) (b j)).re := by
  have h0 : ∀ u v : E, (0 : RoughForm 𝓘(ℝ, E) X ℝ 2) x ![I • u, I • v] =
      (0 : RoughForm 𝓘(ℝ, E) X ℝ 2) x ![u, v] := fun _ _ ↦ by simp
  rw [complexLaplacian_def]
  simp only [relEigenvalueFunction_def,
    ← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x), ← coe_ddbarSesqForm h0]
  rw [sum_relEigenvalueVector_eq_sum_re_apply (hκ.invariant.isSymm_twoFormSesqForm x)
    (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x) (isSymm_ddbarSesqForm h0 hφ) b
    (fun i j ↦ by rw [twoFormSesqForm_apply]; exact hb i j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ddbarSesqForm_apply, ddbarHermitianForm_zero_form]
  simp

end SmoothTwoForm

end TauCeti
