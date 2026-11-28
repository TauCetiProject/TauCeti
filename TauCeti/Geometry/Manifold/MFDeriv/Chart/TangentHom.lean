/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Coordinate expressions of tangent-space homomorphisms along a map

For manifolds `X` and `M` modelled on `J : ModelWithCorners 𝕜 E H'` and
`I : ModelWithCorners 𝕜 F H`, `TauCeti.chartTangentHom J I φ ψ u du` reads a section
`du : ∀ x, TangentSpace J x →L[𝕜] TangentSpace I (u x)` along `u : X → M` in charts `φ` and `ψ` as
`E → E →L[𝕜] F`.

## Main declarations

* `TauCeti.chartTangentHom`: coordinate expression of `du` in charts `φ` and `ψ`, agreeing in
  preferred charts with `ContinuousLinearMap.inCoordinates`
  (`TauCeti.chartTangentHom_chartAt_eq_inCoordinates`).
* `TauCeti.chartTangentHom_comp_fderiv_transition`, `TauCeti.fderiv_extend_comp_chartTangentHom`:
  source and target chart-transition laws for `chartTangentHom`.
-/

public section

open Bundle Filter Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section ChartTangentHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {J : ModelWithCorners 𝕜 E H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H'' : Type*} [TopologicalSpace H''] {I' : ModelWithCorners 𝕜 F' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

section Linear

variable (φ : OpenPartialHomeomorph X H') (ψ : OpenPartialHomeomorph M H) (u : X → M)
  (du du₁ du₂ : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) (z : E)

variable (J I) in
/-- Coordinate expression of `du` along `u : X → M` in charts `φ` (via `J`) and `ψ` (via `I`). -/
def chartTangentHom : E →L[𝕜] F :=
  mvfderiv I (ψ.extend I) (u ((φ.extend J).symm z)) ∘L du ((φ.extend J).symm z) ∘L
    (mfderivWithin 𝓘(𝕜, E) J (φ.extend J).symm (range J) z ∘L
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm.toContinuousLinearMap)

/-- Unfolding `chartTangentHom` at `z ∈ E`. -/
theorem chartTangentHom_apply : chartTangentHom J I φ ψ u du z =
    mvfderiv I (ψ.extend I) (u ((φ.extend J).symm z)) ∘L du ((φ.extend J).symm z) ∘L
      (mfderivWithin 𝓘(𝕜, E) J (φ.extend J).symm (range J) z ∘L
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm.toContinuousLinearMap) := by rfl

/-- At zero, `chartTangentHom` vanishes. -/
@[simp] theorem chartTangentHom_zero : chartTangentHom J I φ ψ u (fun _ ↦ 0) z = 0 := by
  rw [chartTangentHom, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- `chartTangentHom` preserves addition in `du`. -/
@[simp] theorem chartTangentHom_add : chartTangentHom J I φ ψ u (fun x ↦ du₁ x + du₂ x) z =
    chartTangentHom J I φ ψ u du₁ z + chartTangentHom J I φ ψ u du₂ z := by
  simp only [chartTangentHom, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

/-- `chartTangentHom` preserves negation in `du`. -/
@[simp] theorem chartTangentHom_neg :
    chartTangentHom J I φ ψ u (fun x ↦ -du x) z = -chartTangentHom J I φ ψ u du z := by
  simp only [chartTangentHom, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg]

/-- `chartTangentHom` preserves subtraction in `du`. -/
@[simp] theorem chartTangentHom_sub : chartTangentHom J I φ ψ u (fun x ↦ du₁ x - du₂ x) z =
    chartTangentHom J I φ ψ u du₁ z - chartTangentHom J I φ ψ u du₂ z := by
  simp only [chartTangentHom, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- `chartTangentHom` commutes with `𝕜`-scalar multiplication in `du`. -/
@[simp] theorem chartTangentHom_smul (c : 𝕜) :
    chartTangentHom J I φ ψ u (fun x ↦ c • du x) z = c • chartTangentHom J I φ ψ u du z := by
  simp only [chartTangentHom, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end Linear

variable {φ φ' : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H} {u : X → M}

/-- `chartTangentHom` depends at `z` only on `du ((φ.extend J).symm z)`. -/
theorem chartTangentHom_congr {du du' : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)}
    {z : E} (h : du ((φ.extend J).symm z) = du' ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u du z = chartTangentHom J I φ ψ u du' z := by
  simp only [chartTangentHom, h]

/-- Pointwise congruence of `chartTangentHom` across maps agreeing up to `tangentSpaceCast`. -/
theorem chartTangentHom_congr_map {u' : X → M}
    {du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)}
    {du' : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u' x)} {z : E}
    (hu : u ((φ.extend J).symm z) = u' ((φ.extend J).symm z))
    (hdu : (tangentSpaceCast I (u ((φ.extend J).symm z))
        (u' ((φ.extend J).symm z))).toContinuousLinearMap.comp (du ((φ.extend J).symm z)) =
      du' ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u du z = chartTangentHom J I φ ψ u' du' z := by
  ext v; exact apply_eq_of_tangentSpaceCast (fun y ↦ mvfderiv I (ψ.extend I) y) hu
    (DFunLike.congr_fun hdu _)

/-- `chartTangentHom` of `mfderiv J I u` equals `fderiv 𝕜 (ψ.extend I ∘ u ∘ (φ.extend J).symm)`. -/
theorem chartTangentHom_mfderiv (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {z : E} (hz : z ∈ interior (φ.extend J).target)
    (hy : u ((φ.extend J).symm z) ∈ ψ.source)
    (hdu : MDifferentiableAt J I u ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u (fun x ↦ mfderiv J I u x) z =
      fderiv 𝕜 (ψ.extend I ∘ u ∘ (φ.extend J).symm) z := by
  have hdφ := φ.mdifferentiableAt_extend_symm_of_mem_interior one_ne_zero hφ hz
  have hmv := mvfderiv_comp z ((ψ.contMDiffAt_extend hψ hy).mdifferentiableAt one_ne_zero)
    (hdu.comp z hdφ)
  rw [mfderiv_comp z hdu hdφ, mvfderiv_eq_fderiv] at hmv
  rw [chartTangentHom, φ.mfderivWithin_extend_symm_of_mem_interior hz]; ext v
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using
      (DFunLike.congr_fun hmv ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm v)).symm

/-- Pointwise injectivity equivalence of `chartTangentHom` in `C¹` charts `φ` and `ψ`. -/
theorem chartTangentHom_eq_iff (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M)
    {du₁ du₂ : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)} {z : E}
    (hz : z ∈ (φ.extend J).target) (hy : u ((φ.extend J).symm z) ∈ ψ.source) :
    chartTangentHom J I φ ψ u du₁ z = chartTangentHom J I φ ψ u du₂ z ↔
      du₁ ((φ.extend J).symm z) = du₂ ((φ.extend J).symm z) := by
  refine ⟨fun h ↦ ?_, chartTangentHom_congr⟩
  rcases isInvertible_mfderivWithin_extend_symm hφ hz with ⟨L₁, hL₁⟩
  rcases isInvertible_mfderiv_extend hψ hy with ⟨L₂, hL₂⟩
  ext ξ
  refine (L₂.trans (NormedSpace.fromTangentSpace (𝕜 := 𝕜)
    (ψ.extend I (u ((φ.extend J).symm z))))).injective ?_
  simpa only [chartTangentHom, mvfderiv, ← hL₁, ← hL₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply] using
      DFunLike.congr_fun h ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) z) (L₁.symm ξ))

/-- In preferred charts, `chartTangentHom` agrees with `ContinuousLinearMap.inCoordinates`. -/
theorem chartTangentHom_chartAt_eq_inCoordinates [IsManifold J 1 X] [IsManifold I 1 M]
    (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) {x₀ x : X} {y₀ : M}
    (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
    chartTangentHom J I (chartAt H' x₀) (chartAt H y₀) u du (extChartAt J x₀ x) =
      ContinuousLinearMap.inCoordinates E (TangentSpace J) F (TangentSpace I)
        x₀ x y₀ (u x) (du x) := by
  -- Index `inTangentCoordinates_eq_mfderiv_comp` by `Bool` to decouple `(x₀, y₀)` from `(x, u x)`.
  let f : Bool → X := fun b ↦ bif b then x else x₀
  let g : Bool → M := fun b ↦ bif b then u x else y₀
  let ϕ : ∀ b : Bool, TangentSpace J (f b) →L[𝕜] TangentSpace I (g b) :=
    fun b ↦ match b with | false => 0 | true => du x
  have hcoord := inTangentCoordinates_eq_mfderiv_comp (I := J) (I' := I)
    (f := f) (g := g) (ϕ := ϕ) (x₀ := false) (x := true) hx hy
  dsimp only [inTangentCoordinates, f, g, ϕ, Bool.cond_true, Bool.cond_false] at hcoord
  -- Transport `du x'` along `((chartAt H' x₀).extend J).symm (extChartAt J x₀ x) = x`.
  have hchart : ∀ x' : X, x' = x →
      mvfderiv I ((chartAt H y₀).extend I) (u x') ∘L du x' ∘L
        (mfderivWithin 𝓘(𝕜, E) J ((chartAt H' x₀).extend J).symm (range J) (extChartAt J x₀ x) ∘L
          (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (extChartAt J x₀ x)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.inCoordinates E (TangentSpace J) F (TangentSpace I)
        x₀ x y₀ (u x) (du x) := by rintro _ rfl; exact hcoord.symm
  exact hchart _ ((extChartAt J x₀).left_inv (by simpa only [extChartAt_source] using hx))

/-- Pointwise injectivity equivalence of `chartTangentHom` in preferred charts at `x₀` and `y₀`. -/
theorem chartTangentHom_chartAt_eq_iff [IsManifold J 1 X] [IsManifold I 1 M]
    {du₁ du₂ : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)} {x₀ x : X} {y₀ : M}
    (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
    chartTangentHom J I (chartAt H' x₀) (chartAt H y₀) u du₁ (extChartAt J x₀ x) =
        chartTangentHom J I (chartAt H' x₀) (chartAt H y₀) u du₂ (extChartAt J x₀ x) ↔
      du₁ x = du₂ x := by
  have hx' : x ∈ (extChartAt J x₀).source := by simpa only [extChartAt_source] using hx
  have hleft : ((chartAt H' x₀).extend J).symm (extChartAt J x₀ x) = x :=
    (extChartAt J x₀).left_inv hx'
  rw [chartTangentHom_eq_iff (IsManifold.chart_mem_maximalAtlas x₀)
    (IsManifold.chart_mem_maximalAtlas y₀) ((extChartAt J x₀).map_source hx')
    (by rwa [hleft]), hleft]

/-- On `E` and `F` with identity charts, `chartTangentHom` conjugates `du` by `fromTangentSpace`. -/
@[simp] theorem chartTangentHom_refl {u : E → F}
    (du : ∀ z : E, TangentSpace 𝓘(𝕜, E) z →L[𝕜] TangentSpace 𝓘(𝕜, F) (u z)) (z : E) :
    chartTangentHom 𝓘(𝕜, E) 𝓘(𝕜, F) (OpenPartialHomeomorph.refl E) (OpenPartialHomeomorph.refl F)
        u du z =
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (u z)).toContinuousLinearMap ∘L du z ∘L
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm.toContinuousLinearMap := by
  have hexF : ⇑((OpenPartialHomeomorph.refl F).extend 𝓘(𝕜, F)) = fun y : F ↦ y := by ext; simp
  have hexE : ⇑((OpenPartialHomeomorph.refl E).extend 𝓘(𝕜, E)).symm = id := by ext; simp
  rw [chartTangentHom, hexF, hexE, ModelWithCorners.Boundaryless.range_eq_univ,
    mfderivWithin_univ, mfderiv_id, ContinuousLinearMap.id_comp, mvfderiv_eq_fderiv, fderiv_fun_id]
  ext v; simp

/-- Scaling `z` by `algebraMap 𝕜 D c` in `D` scales `chartTangentHom` by `c⁻¹`. -/
theorem chartTangentHom_mulLeft₀ {D : Type*} [NontriviallyNormedField D] [NormedAlgebra 𝕜 D]
    (ψ : OpenPartialHomeomorph M H) (u : D → M)
    (du : ∀ z : D, TangentSpace 𝓘(𝕜, D) z →L[𝕜] TangentSpace I (u z))
    {c : 𝕜} (hc : algebraMap 𝕜 D c ≠ 0) (w : D) :
    chartTangentHom 𝓘(𝕜, D) I
        (Homeomorph.mulLeft₀ (algebraMap 𝕜 D c) hc).toOpenPartialHomeomorph ψ u du w =
      c⁻¹ • chartTangentHom 𝓘(𝕜, D) I (OpenPartialHomeomorph.refl D) ψ u du
        ((algebraMap 𝕜 D c)⁻¹ * w) := by
  have hsymm : ⇑((Homeomorph.mulLeft₀ (algebraMap 𝕜 D c) hc).toOpenPartialHomeomorph.extend
      𝓘(𝕜, D)).symm = c⁻¹ • (id : D → D) := by
    ext; simp [mfld_simps, Homeomorph.mulLeft₀_symm_apply, Algebra.smul_def]
  have hrefl : ⇑((OpenPartialHomeomorph.refl D).extend 𝓘(𝕜, D)).symm = id := by ext; simp
  have hcw : (algebraMap 𝕜 D c)⁻¹ * w = c⁻¹ • w := by rw [← map_inv₀, ← Algebra.smul_def]
  rw [hcw, chartTangentHom_apply, chartTangentHom_apply, hsymm, hrefl,
    ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ, mfderivWithin_univ,
    mfderiv_eq_fderiv, ((hasFDerivAt_id w).const_smul c⁻¹).fderiv, mfderiv_id]
  ext v; simp

/-- Source-chart transition law for `chartTangentHom` on an overlap interior. -/
theorem chartTangentHom_comp_fderiv_transition (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X) (ψ : OpenPartialHomeomorph M H)
    (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x))
    {w : E} (hw : w ∈ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source)) :
    (chartTangentHom J I φ ψ u du (φ.extend J ((φ'.extend J).symm w))).comp
        (fderiv 𝕜 (φ.extend J ∘ (φ'.extend J).symm) w) =
      chartTangentHom J I φ' ψ u du w := by
  rw [← Function.comp_apply (f := φ.extend J)]
  set Φ := φ.extend J ∘ (φ'.extend J).symm
  have hwint : w ∈ interior (φ'.extend J).target := interior_mono inter_subset_left hw
  have hwt : w ∈ (φ'.extend J).target := interior_subset hwint
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source :=
    φ'.extend_source (I := J) ▸ (φ'.extend J).map_target hwt
  have hxφ : (φ'.extend J).symm w ∈ φ.source := (interior_subset hw).2
  have hdφ' := φ'.mdifferentiableAt_extend_symm_of_mem_interior one_ne_zero hφ' hwint
  have hΦint : Φ w ∈ interior (φ.extend J).target :=
    ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero hφ' hφ hxφ' hxφ
      (by rwa [(φ'.extend J).right_inv hwt])
  have hev : (φ'.extend J).symm =ᶠ[𝓝 w] (φ.extend J).symm ∘ Φ := by
    filter_upwards [isOpen_interior.mem_nhds hw] with z hz
    simp only [Φ, Function.comp_apply, φ.extend_left_inv (interior_subset hz).2]
  have hmf := hev.mfderiv_eq (I := 𝓘(𝕜, E)) (I' := J)
  rw [mfderiv_comp w (φ.mdifferentiableAt_extend_symm_of_mem_interior one_ne_zero hφ hΦint)
    (((φ.contMDiffAt_extend hφ hxφ).mdifferentiableAt one_ne_zero).comp w hdφ')] at hmf
  ext v
  rw [ContinuousLinearMap.comp_apply, chartTangentHom_apply, chartTangentHom_apply,
    φ.mfderivWithin_extend_symm_of_mem_interior hΦint,
    φ'.mfderivWithin_extend_symm_of_mem_interior hwint]
  have hfd : (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (Φ w)).symm (fderiv 𝕜 Φ w v) =
      mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) Φ w ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) w).symm v) := by
    simp [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hfd]
  exact apply_eq_of_tangentSpaceCast (I := J) (fun x ξ ↦ mvfderiv I (ψ.extend I) (u x) (du x ξ))
    (φ.extend_left_inv hxφ) (DFunLike.congr_fun hmf.symm _)

/-- Target transition / postcomposition law for `chartTangentHom` when `M` is boundaryless. -/
theorem fderiv_extend_comp_chartTangentHom [I.Boundaryless]
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {ψ' : OpenPartialHomeomorph N H''}
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I' 1 N) {f : M → N} {t : Set M}
    (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t)
    (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) {z : E}
    (hy : u ((φ.extend J).symm z) ∈ ψ.source ∩ (t ∩ f ⁻¹' ψ'.source)) :
    (fderiv 𝕜 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
        (ψ.extend I (u ((φ.extend J).symm z)))).comp (chartTangentHom J I φ ψ u du z) =
      chartTangentHom J I' φ ψ' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) z := by
  set y := u ((φ.extend J).symm z)
  set g := ψ'.extend I' ∘ f ∘ (ψ.extend I).symm
  have hO := ψ.isOpen_extend_target_inter_preimage (I := I)
    (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hyO : ψ.extend I y ∈ (ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source) :=
    ⟨(ψ.extend I).map_source (by rw [ψ.extend_source]; exact hy.1),
      by rw [mem_preimage, ψ.extend_left_inv hy.1]; exact hy.2⟩
  have hgd : DifferentiableAt 𝕜 g (ψ.extend I y) :=
    (((ψ.contDiffOn_extend_comp hψ hψ' hf) _ hyO).differentiableWithinAt
      one_ne_zero).differentiableAt (hO.mem_nhds hyO)
  have hev : ψ'.extend I' ∘ f =ᶠ[𝓝 y] g ∘ ψ.extend I := by
    filter_upwards [ψ.open_source.mem_nhds hy.1] with y' hy'
    simp only [g, Function.comp_apply, ψ.extend_left_inv hy']
  have hmv : (fderiv 𝕜 g (ψ.extend I y)).comp (mvfderiv I (ψ.extend I) y) =
      (mvfderiv I' (ψ'.extend I') (f y)).comp (mfderiv I I' f y) := by
    have h1 := mvfderiv_comp y hgd.mdifferentiableAt
      ((ψ.contMDiffAt_extend hψ hy.1).mdifferentiableAt one_ne_zero)
    rw [mvfderiv_eq_fderiv] at h1
    have h2 := mvfderiv_comp y ((ψ'.contMDiffAt_extend hψ' hy.2.2).mdifferentiableAt one_ne_zero)
      (((hf y hy.2.1).contMDiffAt (ht.mem_nhds hy.2.1)).mdifferentiableAt one_ne_zero)
    ext w
    exact (DFunLike.congr_fun h1 w).symm.trans ((apply_eq_of_tangentSpaceCast (I := 𝓘(𝕜, F'))
      (fun p ↦ NormedSpace.fromTangentSpace (𝕜 := 𝕜) p) hev.eq_of_nhds
      (DFunLike.congr_fun hev.symm.mfderiv_eq w).symm).symm.trans (DFunLike.congr_fun h2 w))
  simp only [chartTangentHom_apply, y, Function.comp_apply, ← ContinuousLinearMap.comp_assoc, hmv]

end ChartTangentHom

end TauCeti
