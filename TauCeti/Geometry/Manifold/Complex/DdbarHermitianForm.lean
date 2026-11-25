/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Vector
public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Complex.TwoFormHermitianForm

/-!
# The Hermitian form of `α + i ∂∂bar φ` on a complex manifold

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)`, so that every tangent space is `E` and
multiplication by `i` is its almost complex structure `J`. For a real two-form `α` on the
underlying real manifold, `TauCeti.twoFormHermitianForm E α x` is the Hermitian form
`H_α(u, v) = α(u, J v) + i·α(u, v)` of `α` at `x`
(`TauCeti.Geometry.Manifold.Complex.TwoFormHermitianForm`). For a Hermitian metric `ω`, a smooth
two-form compatible with `J`, it is the Hermitian inner product `h` of `ω`.

For a real function `φ`, the real (1,1)-form `i ∂∂bar φ` has Hermitian form `2·L_φ`, where `L_φ`
is the Levi form `TauCeti.manifoldLeviForm E φ x`; with this normalization
`i ∂∂bar |z|² = i Σ dz_j ∧ dzbar_j` on `ℂⁿ`. So `TauCeti.ddbarHermitianForm E α φ x`, defined as
`H_α(x) + 2·L_φ(x)`, is the Hermitian form of `α + i ∂∂bar φ` at `x`. The eigenvalues of this
form relative to `h` (`TauCeti.IsRelEigenvalueVector`) are the eigenvalues `λ_ω[α + i ∂∂bar φ]`
that a complex Hessian equation prescribes a symmetric function of.

## Main definitions

* `TauCeti.ddbarHermitianForm E α φ x`: the Hermitian form `H_α + 2·L_φ` of `α + i ∂∂bar φ`.
* `TauCeti.ddbarSesqForm`: the same form as a sesquilinear form, when `α` has type (1,1) at `x`.

## Main results

* `TauCeti.ddbarHermitianForm_sub_twoFormHermitianForm`, `TauCeti.ddbarHermitianForm_const`,
  `TauCeti.ddbarHermitianForm_add`: `H_{α + i ∂∂bar φ} - H_α = 2·L_φ`, which vanishes for constant
  `φ` and is additive in `φ`.
* `TauCeti.isSymm_ddbarSesqForm`: if `α` has type (1,1) at `x` and `φ` is `C²` at `x`, the
  form `H_{α + i ∂∂bar φ}(x)` is a Hermitian sesquilinear form (`TauCeti.ddbarSesqForm`).
* `TauCeti.ddbarHermitianForm_add_form`: `H_{α + i ∂∂bar φ}` is additive in `α`.
* `TauCeti.SmoothTwoForm.Compatible.exists_isRelEigenvalueVector_ddbarHermitianForm`: relative to
  a Hermitian metric, `α + i ∂∂bar φ` has a decreasingly sorted eigenvalue vector at `x`, unique
  by `TauCeti.IsRelEigenvalueVector.eq_of_antitone`.
* `TauCeti.SmoothTwoForm.Compatible.isRelEigenvalueVector_self_iff`: `λ_ω[ω] = e`.
* `TauCeti.ddbarHermitianForm_zero_form_norm_sq`: on a complex inner product space,
  `H_{i ∂∂bar |z|²} = 2·h`.
* `TauCeti.re_ddbarHermitianForm_zero_form_apply_self_nonpos_of_isLocalMax`: at a local maximum of
  a `C²` function `φ`, the form `H_{i ∂∂bar φ}` is negative semidefinite.

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
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

section Forms

variable {α : RoughForm 𝓘(ℝ, E) X ℝ 2} {φ ψ : X → ℝ} {x : X}

variable (E) in
/-- The Hermitian form `H_{α + i ∂∂bar φ} = H_α + 2·L_φ` of the real (1,1)-form `α + i ∂∂bar φ`
at `x`, where `L_φ` is the Levi form of `φ` (`TauCeti.manifoldLeviForm`). -/
def ddbarHermitianForm (α : RoughForm 𝓘(ℝ, E) X ℝ 2) (φ : X → ℝ) (x : X) (u v : E) : ℂ :=
  twoFormHermitianForm E α x u v + 2 * manifoldLeviForm E φ x u v

/-- Unfolding lemma for `ddbarHermitianForm`. -/
theorem ddbarHermitianForm_def (u v : E) :
    ddbarHermitianForm E α φ x u v =
      twoFormHermitianForm E α x u v + 2 * manifoldLeviForm E φ x u v :=
  (rfl)

/-- `H_{α + i ∂∂bar φ} - H_α = 2·L_φ`. -/
theorem ddbarHermitianForm_sub_twoFormHermitianForm (u v : E) :
    ddbarHermitianForm E α φ x u v - twoFormHermitianForm E α x u v =
      2 * manifoldLeviForm E φ x u v := by
  rw [ddbarHermitianForm_def, add_sub_cancel_left]

/-- For a constant function `φ`, `H_{α + i ∂∂bar φ} = H_α`. -/
@[simp]
theorem ddbarHermitianForm_const (c : ℝ) :
    ddbarHermitianForm E α (fun _ ↦ c) x = twoFormHermitianForm E α x := by
  ext u v
  simp [ddbarHermitianForm_def]

/-- For `φ = 0`, `H_{α + i ∂∂bar φ} = H_α`. -/
@[simp]
theorem ddbarHermitianForm_zero : ddbarHermitianForm E α 0 x = twoFormHermitianForm E α x :=
  ddbarHermitianForm_const 0

/-- `H_{(α + β) + i ∂∂bar φ} = H_{α + i ∂∂bar φ} + H_β`. -/
theorem ddbarHermitianForm_add_form (β : RoughForm 𝓘(ℝ, E) X ℝ 2) (u v : E) :
    ddbarHermitianForm E (α + β) φ x u v =
      ddbarHermitianForm E α φ x u v + twoFormHermitianForm E β x u v := by
  rw [ddbarHermitianForm_def, ddbarHermitianForm_def, twoFormHermitianForm_add]
  ring

/-- **The sum rule**: `H_{α + i ∂∂bar (φ + ψ)} = H_{α + i ∂∂bar φ} + 2·L_ψ` at a point where `φ`
and `ψ` are `C²`. -/
theorem ddbarHermitianForm_add (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x)
    (hψ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ψ x) (u v : E) :
    ddbarHermitianForm E α (φ + ψ) x u v =
      ddbarHermitianForm E α φ x u v + 2 * manifoldLeviForm E ψ x u v := by
  simp only [ddbarHermitianForm_def, manifoldLeviForm_add hφ hψ, LinearMap.add_apply]
  ring

/-- For the zero form, `H_{i ∂∂bar φ} = 2·L_φ`. -/
@[simp]
theorem ddbarHermitianForm_zero_form (u v : E) :
    ddbarHermitianForm E 0 φ x u v = 2 * manifoldLeviForm E φ x u v := by
  rw [ddbarHermitianForm_def, twoFormHermitianForm_zero, zero_add]

variable (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v])

variable (E φ) in
/-- If `α(x)` has type (1,1), the form `H_{α + i ∂∂bar φ}(x)` as a sesquilinear form, conjugate
linear in the first slot. -/
def ddbarSesqForm : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ :=
  twoFormSesqForm E α x hα + (2 : ℂ) • manifoldLeviForm E φ x

/-- The sesquilinear form `ddbarSesqForm` evaluates as `H_{α + i ∂∂bar φ}`. -/
@[simp]
theorem ddbarSesqForm_apply (u v : E) :
    ddbarSesqForm E φ hα u v = ddbarHermitianForm E α φ x u v := by
  simp [ddbarSesqForm, ddbarHermitianForm_def]

/-- The function underlying `ddbarSesqForm` is `H_{α + i ∂∂bar φ}`. -/
theorem coe_ddbarSesqForm :
    (fun u v ↦ ddbarSesqForm E φ hα u v) = ddbarHermitianForm E α φ x :=
  funext fun u ↦ funext fun v ↦ ddbarSesqForm_apply hα u v

/-- **`H_{α + i ∂∂bar φ}(x)` is Hermitian** if `α(x)` has type (1,1) and `φ` is `C²` at `x`. -/
theorem isSymm_ddbarSesqForm (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x) :
    (ddbarSesqForm E φ hα).IsSymm := by
  rw [ddbarSesqForm, two_smul]
  exact (isSymm_twoFormSesqForm hα).add
    ((isSymm_manifoldLeviForm hφ).add (isSymm_manifoldLeviForm hφ))

/-- **The sign at a local maximum.** If `φ` is `C²` at a local maximum `x`, then
`H_{i ∂∂bar φ}(x)` is negative semidefinite. -/
theorem re_ddbarHermitianForm_zero_form_apply_self_nonpos_of_isLocalMax
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x) (hmax : IsLocalMax φ x) (v : E) :
    (ddbarHermitianForm E 0 φ x v v).re ≤ 0 := by
  have h := re_manifoldLeviForm_apply_self_nonpos_of_isLocalMax hφ hmax v
  rw [ddbarHermitianForm_zero_form, show ((2 : ℂ) * manifoldLeviForm E φ x v v).re =
    2 * (manifoldLeviForm E φ x v v).re by simp]
  linarith

end Forms

section NormSq

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **The normalization of `i ∂∂bar`.** On a complex inner product space `V` with Hermitian inner
product `h = ⟪·, ·⟫`, `H_{i ∂∂bar |z|²} = 2·h`, that is, `i ∂∂bar |z|² = i Σ dz_j ∧ dzbar_j`. -/
theorem ddbarHermitianForm_zero_form_norm_sq (x u v : V) :
    ddbarHermitianForm V (0 : RoughForm 𝓘(ℝ, V) V ℝ 2) (fun z ↦ ‖z‖ ^ 2) x u v =
      2 * inner ℂ u v := by
  rw [ddbarHermitianForm_zero_form, manifoldLeviForm_eq_leviForm, leviForm_norm_sq,
    innerₛₗ_apply_apply]

end NormSq

namespace SmoothTwoForm

variable [IsManifold 𝓘(ℂ, E) ∞ X] {κ : SmoothTwoForm 𝓘(ℝ, E) X}

variable (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X))
include hκ

/-- **Eigenvalues relative to a Hermitian metric.** If `α(x)` has type (1,1) and `φ` is `C²` at
`x`, then `α + i ∂∂bar φ` has a decreasingly sorted eigenvalue vector at `x` relative to the
Hermitian metric `κ`; it is unique by `IsRelEigenvalueVector.eq_of_antitone`. -/
theorem Compatible.exists_isRelEigenvalueVector_ddbarHermitianForm
    {α : RoughForm 𝓘(ℝ, E) X ℝ 2} {φ : X → ℝ} {x : X}
    (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v])
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x) :
    ∃ μ, Antitone μ ∧
      IsRelEigenvalueVector (twoFormHermitianForm E κ.val x) (ddbarHermitianForm E α φ x) μ := by
  rw [← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x), ← coe_ddbarSesqForm hα]
  exact exists_isRelEigenvalueVector (hκ.invariant.isSymm_twoFormSesqForm x)
    (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x) (isSymm_ddbarSesqForm hα hφ)

/-- **`λ_κ[κ] = e`.** Relative to itself, a Hermitian metric has the eigenvalue vector
`e = (1, …, 1)`, and no other. -/
theorem Compatible.isRelEigenvalueVector_self_iff (x : X)
    {μ : Fin (finrank ℂ E) → ℝ} :
    IsRelEigenvalueVector (twoFormHermitianForm E κ.val x) (twoFormHermitianForm E κ.val x) μ ↔
      μ = 1 := by
  rw [← coe_twoFormSesqForm (hκ.invariant.apply_I_smul_I_smul x)]
  exact TauCeti.isRelEigenvalueVector_self_iff (hκ.invariant.isSymm_twoFormSesqForm x)
    fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x

end SmoothTwoForm

end TauCeti
