/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Continuity
import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.LinearEquiv
import TauCeti.Geometry.Manifold.Complex.LeviForm
import TauCeti.Geometry.Manifold.Complex.TwoFormHermitianForm.Continuity
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Continuity of the eigenvalue function on a Hermitian manifold

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)` with a Hermitian metric `κ`. For a continuous
real two-form `α` of type (1,1) and a function `φ` that is `C²` at `x₀`, the eigenvalue function
`x ↦ λ_κ[α + i ∂∂bar φ](x)` (`TauCeti.relEigenvalueFunction`) is continuous at `x₀`
(`TauCeti.SmoothTwoForm.Compatible.continuousAt_relEigenvalueFunction`). In particular
`λ_κ[α]` is continuous for every continuous real (1,1)-form `α`.

The forms at `x` act on the tangent space at `x`, which is `E` read in the chart at `x`. To compare
them with the forms at `x₀` we read them in the chart at `x₀`, through the tangent coordinate
change `B x` from the chart at `x₀` to the chart at `x`, which is complex linear since the atlas is
holomorphic. Relative eigenvalues do not change under the complex linear equivalence `B x`
(`TauCeti.relEigenvalueVector_comp_linearEquiv`). In these coordinates:

* the Hermitian forms `H_κ(x)` and `H_α(x)` converge
  (`TauCeti.IsSmoothForm.tendsto_twoFormHermitianForm_tangentCoordChange`), by continuity of the
  forms evaluated along converging tangent vectors;
* the Levi form of `φ` converges (`TauCeti.tendsto_manifoldLeviForm_tangentCoordChange`): it is
  the Levi form of the coordinate expression of `φ` in the chart at `x₀`, which is continuous
  because it is built from the second derivative of a `C²` function.

The sorted eigenvalue vector depends continuously on the pair of forms at a positive definite
reference form (`TauCeti.tendsto_relEigenvalueVector`), which concludes.
-/

public section

open Complex Filter Module Topology Bundle
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

namespace SmoothTwoForm

/-- **Continuity of the eigenvalue function.** Let `κ` be a Hermitian metric on a complex manifold,
`α` a continuous real two-form of type (1,1) and `φ` a function that is `C²` at `x₀`. Then the
eigenvalue function `x ↦ λ_κ[α + i ∂∂bar φ](x)` is continuous at `x₀`. -/
theorem Compatible.continuousAt_relEigenvalueFunction {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X))
    {α : RoughForm 𝓘(ℝ, E) X ℝ 2} (hαc : IsSmoothForm 𝓘(ℝ, E) 0 α)
    (hα : ∀ x (u v : E), α x ![I • u, I • v] = α x ![u, v]) {φ : X → ℝ} {x₀ : X}
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x₀) :
    ContinuousAt (relEigenvalueFunction E κ α φ) x₀ := by
  set B : X → E →L[ℂ] E := fun x ↦ tangentCoordChange 𝓘(ℂ, E) x₀ x x
  have hκx (x : X) := hκ.invariant.apply_I_smul_I_smul x
  -- The forms at `x`, read in the chart at `x₀`.
  set H : X → E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ := fun x ↦
    ((twoFormSesqForm E κ.val x (hκx x)).comp (B x : E →ₗ[ℂ] E)).compl₂ (B x : E →ₗ[ℂ] E)
  set A : X → E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ := fun x ↦
    ((ddbarSesqForm E φ (hα x)).comp (B x : E →ₗ[ℂ] E)).compl₂ (B x : E →ₗ[ℂ] E)
  have hH (x : X) (u v : E) : H x u v = twoFormHermitianForm E κ.val x (B x u) (B x v) := by
    simp [H]
  have hA (x : X) (u v : E) : A x u v = ddbarHermitianForm E α φ x (B x u) (B x v) := by
    simp [A]
  have hsrc : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt E x₀).source :=
    (chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)
  have hφx : ∀ᶠ x in 𝓝 x₀, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφ
  -- Through the equivalence `B x`, the eigenvalue function is that of the forms `H x`, `A x`.
  have heq : ∀ᶠ x in 𝓝 x₀, relEigenvalueVector (H x · ·) (A x · ·) =
      relEigenvalueFunction E κ α φ x := by
    filter_upwards [hsrc] with x hx
    simp only [hH, hA, relEigenvalueFunction_def]
    -- `B x` is the coordinate change between the complex tangent trivializations.
    set e := (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).coordChangeL ℂ
      (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x) x
    have hB : (e : E →L[ℂ] E) = B x :=
      (tangentBundleCore 𝓘(ℂ, E) X).trivializationAt_coordChangeL ⟨hx, mem_chart_source E x⟩
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe, hB] using
      relEigenvalueVector_comp_linearEquiv e.toLinearEquiv (twoFormHermitianForm E κ.val x)
        (ddbarHermitianForm E α φ x)
  have hlim : Tendsto (fun x ↦ relEigenvalueVector (H x · ·) (A x · ·)) (𝓝 x₀)
      (𝓝 (relEigenvalueVector (twoFormSesqForm E κ.val x₀ (hκx x₀) · ·)
        (ddbarSesqForm E φ (hα x₀) · ·))) := by
    refine tendsto_relEigenvalueVector (Eventually.of_forall fun x ↦ ?_)
      (hφx.mono fun x hx ↦ ?_) (fun _ ↦ hκ.re_twoFormSesqForm_apply_self_pos x₀) (fun u v ↦ ?_)
      (fun u v ↦ ?_)
    · refine LinearMap.isSymm_def.2 fun u v ↦ ?_
      simp only [H, LinearMap.compl₂_apply, LinearMap.comp_apply]
      exact LinearMap.isSymm_def.1 (hκ.invariant.isSymm_twoFormSesqForm x) _ _
    · refine LinearMap.isSymm_def.2 fun u v ↦ ?_
      simp only [A, LinearMap.compl₂_apply, LinearMap.comp_apply]
      exact LinearMap.isSymm_def.1 (isSymm_ddbarSesqForm (hα x) hx) _ _
    · simp only [hH, twoFormSesqForm_apply]
      exact (κ.isSmoothForm.of_le (by simp)).tendsto_twoFormHermitianForm_tangentCoordChange x₀ u v
    · simp only [hA, ddbarSesqForm_apply, ddbarHermitianForm_def]
      exact (hαc.tendsto_twoFormHermitianForm_tangentCoordChange x₀ u v).add
        ((tendsto_manifoldLeviForm_tangentCoordChange hφ u v).const_mul 2)
  have h₀ : relEigenvalueVector (twoFormSesqForm E κ.val x₀ (hκx x₀) · ·)
      (ddbarSesqForm E φ (hα x₀) · ·) = relEigenvalueFunction E κ α φ x₀ := by
    rw [relEigenvalueFunction_def, coe_twoFormSesqForm, coe_ddbarSesqForm]
  rw [ContinuousAt, ← h₀]
  exact hlim.congr' heq

/-- **Continuity of `λ_κ[α]`** for a continuous real (1,1)-form `α`. -/
theorem Compatible.continuous_relEigenvalueFunction_zero {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X))
    {α : RoughForm 𝓘(ℝ, E) X ℝ 2} (hαc : IsSmoothForm 𝓘(ℝ, E) 0 α)
    (hα : ∀ x (u v : E), α x ![I • u, I • v] = α x ![u, v]) :
    Continuous (relEigenvalueFunction E κ α 0) :=
  continuous_iff_continuousAt.2 fun _ ↦
    hκ.continuousAt_relEigenvalueFunction hαc hα contMDiffAt_const

/-- **Continuity of the complex Laplacian** `Δ_κ φ = Σ_j λ_j[i ∂∂bar φ]` at a point where `φ` is
`C²`. -/
theorem Compatible.continuousAt_complexLaplacian {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X)) {φ : X → ℝ}
    {x₀ : X} (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x₀) :
    ContinuousAt (complexLaplacian E κ φ) x₀ := by
  have h := hκ.continuousAt_relEigenvalueFunction (IsSmoothForm.zero 0)
    (fun _ _ _ ↦ by simp) hφ
  have hfun : complexLaplacian E κ φ = fun x ↦ ∑ j, relEigenvalueFunction E κ 0 φ x j :=
    funext (complexLaplacian_def κ φ)
  rw [hfun]
  exact tendsto_finsetSum _ fun j _ ↦ ((continuous_apply j).continuousAt.comp h).tendsto

end SmoothTwoForm

end TauCeti
