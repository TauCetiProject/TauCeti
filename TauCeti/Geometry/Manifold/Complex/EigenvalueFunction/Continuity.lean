/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Continuity
import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.LinearEquiv
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.VectorBundle.Trivialization

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

* the Hermitian forms `H_κ(x)` and `H_α(x)` converge, by continuity of the forms evaluated along
  converging tangent vectors (`TauCeti.IsSmoothForm.tendsto_apply`);
* the Levi form of `φ` at `x` is the Levi form at the chart image of `x` of the coordinate
  expression of `φ` in the chart at `x₀` (`TauCeti.leviForm_comp_symm_apply_of_mem_maximalAtlas`),
  which is continuous because it is built from the second derivative of a `C²` function.

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

/-- The real tangent coordinate changes of a complex manifold are the complex ones. -/
theorem tangentCoordChange_real_eq_complex {x y z : X}
    (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) (v : E) :
    tangentCoordChange 𝓘(ℝ, E) x y z v = tangentCoordChange 𝓘(ℂ, E) x y z v := by
  simpa only [modelWithCornersSelf_restrictScalars, ContinuousLinearMap.coe_restrictScalars'] using
    congrArg (fun L : E →L[ℝ] E ↦ L v) (𝓘(ℂ, E).tangentCoordChange_restrictScalars ℝ h)

/-- On the chart at `x₀`, the complex tangent coordinate change from the chart at `x` back to the
chart at `x₀` undoes the one from the chart at `x₀` to the chart at `x`. -/
theorem tangentCoordChange_tangentCoordChange_self {x₀ x : X}
    (hx : x ∈ (chartAt E x₀).source) (v : E) :
    tangentCoordChange 𝓘(ℂ, E) x x₀ x (tangentCoordChange 𝓘(ℂ, E) x₀ x x v) = v := by
  rw [tangentCoordChange_comp (I := 𝓘(ℂ, E)) ⟨⟨by simpa using hx, by simp⟩, by simpa using hx⟩,
    tangentCoordChange_self (I := 𝓘(ℂ, E)) (by simpa using hx)]

/-- On the chart at `x₀`, the complex tangent coordinate change from the chart at `x₀` to the
chart at `x` undoes the one from the chart at `x` to the chart at `x₀`. -/
theorem tangentCoordChange_tangentCoordChange_self' {x₀ x : X}
    (hx : x ∈ (chartAt E x₀).source) (v : E) :
    tangentCoordChange 𝓘(ℂ, E) x₀ x x (tangentCoordChange 𝓘(ℂ, E) x x₀ x v) = v := by
  rw [tangentCoordChange_comp (I := 𝓘(ℂ, E)) ⟨⟨by simp, by simpa using hx⟩, by simp⟩,
    tangentCoordChange_self (I := 𝓘(ℂ, E)) (by simp)]

/-- On the chart at `x₀`, the complex tangent coordinate change from the chart at `x₀` to the
chart at `x`, as a linear equivalence. -/
def tangentCoordChangeEquiv {x₀ x : X} (hx : x ∈ (chartAt E x₀).source) : E ≃ₗ[ℂ] E where
  toFun := tangentCoordChange 𝓘(ℂ, E) x₀ x x
  invFun := tangentCoordChange 𝓘(ℂ, E) x x₀ x
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := tangentCoordChange_tangentCoordChange_self hx
  right_inv := tangentCoordChange_tangentCoordChange_self' hx

/-- **Tangent vectors with constant coordinates in the chart at `x₀`** converge in the tangent
bundle: `(x, B x u) → (x₀, u)` as `x → x₀`, where `B x` is the tangent coordinate change from the
chart at `x₀` to the chart at `x`. -/
theorem tendsto_mk_tangentCoordChange (x₀ : X) (u : E) :
    Tendsto (fun x ↦ (⟨x, tangentCoordChange 𝓘(ℂ, E) x₀ x x u⟩ : TangentBundle 𝓘(ℝ, E) X))
      (𝓝 x₀) (𝓝 ⟨x₀, u⟩) := by
  set T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
  have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x₀
  have hcoord {x : X} (hx : x ∈ (chartAt E x₀).source) (v : E) :
      T.continuousLinearMapAt ℝ x v = tangentCoordChange 𝓘(ℂ, E) x x₀ x v := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
      ← tangentCoordChange_real_eq_complex ⟨mem_chart_source E x, hx⟩]
    rfl
  refine (T.tendsto_mk_nhds_mk_iff ℝ hx₀).2 ⟨tendsto_id, ?_⟩
  rw [hcoord (mem_chart_source E x₀), tangentCoordChange_self (I := 𝓘(ℂ, E)) (by simp)]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with x hx
  rw [hcoord hx, tangentCoordChange_tangentCoordChange_self hx]

/-- **The Hermitian form of a continuous two-form, read in the chart at `x₀`, is continuous at
`x₀`**: `H_α(x)(B x u, B x v) → H_α(x₀)(u, v)`. -/
theorem IsSmoothForm.tendsto_twoFormHermitianForm_tangentCoordChange
    {α : RoughForm 𝓘(ℝ, E) X ℝ 2} (hα : IsSmoothForm 𝓘(ℝ, E) 0 α) (x₀ : X) (u v : E) :
    Tendsto (fun x ↦ twoFormHermitianForm E α x (tangentCoordChange 𝓘(ℂ, E) x₀ x x u)
      (tangentCoordChange 𝓘(ℂ, E) x₀ x x v)) (𝓝 x₀) (𝓝 (twoFormHermitianForm E α x₀ u v)) := by
  have hvec (w w' : E) : ∀ j, Tendsto (fun x ↦ (⟨x, ![tangentCoordChange 𝓘(ℂ, E) x₀ x x w,
      tangentCoordChange 𝓘(ℂ, E) x₀ x x w'] j⟩ : TangentBundle 𝓘(ℝ, E) X)) (𝓝 x₀)
      (𝓝 ⟨x₀, ![w, w'] j⟩) := by
    intro j
    fin_cases j
    · exact tendsto_mk_tangentCoordChange x₀ w
    · exact tendsto_mk_tangentCoordChange x₀ w'
  have hre := hα.tendsto_apply tendsto_id (hvec u (I • v))
  have him := hα.tendsto_apply tendsto_id (hvec u v)
  simp only [map_smul, id] at hre
  simp only [twoFormHermitianForm_def, Complex.mk_eq_add_mul_I]
  exact ((continuous_ofReal.tendsto _).comp hre).add
    (((continuous_ofReal.tendsto _).comp him).mul_const I)

/-- **The Levi form, read in the chart at `x₀`, is continuous at `x₀`** for a function that is
`C²` at `x₀`: `L_φ(x)(B x u, B x v) → L_φ(x₀)(u, v)`. -/
theorem tendsto_manifoldLeviForm_tangentCoordChange {φ : X → ℝ} {x₀ : X}
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x₀) (u v : E) :
    Tendsto (fun x ↦ manifoldLeviForm E φ x (tangentCoordChange 𝓘(ℂ, E) x₀ x x u)
      (tangentCoordChange 𝓘(ℂ, E) x₀ x x v)) (𝓝 x₀) (𝓝 (manifoldLeviForm E φ x₀ u v)) := by
  set e := chartAt E x₀
  set f := φ ∘ e.symm
  -- In the chart at `x₀`, the Levi form is that of the coordinate expression `f`.
  have hL : ∀ᶠ x in 𝓝 x₀, manifoldLeviForm E φ x (tangentCoordChange 𝓘(ℂ, E) x₀ x x u)
      (tangentCoordChange 𝓘(ℂ, E) x₀ x x v) = leviForm f (e x) u v := by
    filter_upwards [e.open_source.mem_nhds (mem_chart_source E x₀),
      (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφ] with x hx hφx
    have hD : ∀ w, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x (tangentCoordChange 𝓘(ℂ, E) x₀ x x w) = w :=
      fun w ↦ by
        rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℂ, E)) hx]
        exact tangentCoordChange_tangentCoordChange_self hx w
    have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 X := IsManifold.chart_mem_maximalAtlas x₀
    rw [← leviForm_comp_symm_apply_of_mem_maximalAtlas he hx hφx, hD, hD]
  -- The Levi form of the `C²` function `f` is continuous, as its second derivative is.
  have hf : ContDiffAt ℝ 2 f (e x₀) := hφ.contDiffAt_comp_chartAt_symm
  have hD2 : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (e x₀) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have he : ContinuousAt e x₀ := e.continuousAt (mem_chart_source E x₀)
  have hc : ContinuousAt (fun z ↦ leviForm f z u v) (e x₀) := by
    have hre : ContinuousAt (fun z ↦ (leviForm f z u v).re) (e x₀) := by
      simp only [re_leviForm_apply]
      exact ((hD2.clm_apply continuousAt_const).clm_apply continuousAt_const |>.add
        ((hD2.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const _
    have him : ContinuousAt (fun z ↦ (leviForm f z u v).im) (e x₀) := by
      simp only [im_leviForm_apply]
      exact ((hD2.clm_apply continuousAt_const).clm_apply continuousAt_const |>.sub
        ((hD2.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const _
    have h := (continuous_ofReal.continuousAt.comp hre).add
      ((continuous_ofReal.continuousAt.comp him).mul
      (continuousAt_const : ContinuousAt (fun _ : E ↦ I) (e x₀)))
    have hfun : (fun z ↦ leviForm f z u v) =
        fun z ↦ ((leviForm f z u v).re : ℂ) + (leviForm f z u v).im * I :=
      funext fun z ↦ (Complex.re_add_im _).symm
    rw [hfun]
    exact h
  rw [manifoldLeviForm_def]
  exact (hc.tendsto.comp he.tendsto).congr' (hL.mono fun x hx ↦ hx.symm)

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
    simp only [hH, hA]
    rw [relEigenvalueFunction_def]
    exact relEigenvalueVector_comp_linearEquiv (tangentCoordChangeEquiv hx)
      (twoFormHermitianForm E κ.val x) (ddbarHermitianForm E α φ x)
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
