/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Coordinate expressions of tangent-space homomorphisms along a map

For manifolds `X` and `M` modelled on `J : ModelWithCorners 𝕜 E H'` and
`I : ModelWithCorners 𝕜 F H` (possibly with corners), `TauCeti.chartTangentHom J I φ ψ u du` reads
`du : ∀ x, TangentSpace J x →L[𝕜] TangentSpace I (u x)` along `u : X → M` in charts `φ` and `ψ` as
a map `E → E →L[𝕜] F`, agreeing in preferred charts with `ContinuousLinearMap.inCoordinates`
(`TauCeti.chartTangentHom_chartAt_eq_inCoordinates`) and transforming functorially under chart
transitions (`TauCeti.chartTangentHom_comp_fderiv_transition`,
`TauCeti.fderiv_extend_comp_chartTangentHom`).
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

/-- At an interior point of `(φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source`, the Fréchet
derivative of `φ.extend J ∘ (φ'.extend J).symm` between `C^n` (`n ≠ 0`) charts has nonzero `det`. -/
theorem _root_.ModelWithCorners.det_fderiv_extendCoordChange_ne_zero (J : ModelWithCorners 𝕜 E H')
    {n : ℕ∞ω} (hn : n ≠ 0) {φ' φ : OpenPartialHomeomorph X H'}
    (hφ' : φ' ∈ IsManifold.maximalAtlas J n X) (hφ : φ ∈ IsManifold.maximalAtlas J n X)
    {w : E} (hw : w ∈ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source)) :
    (fderiv 𝕜 (φ.extend J ∘ (φ'.extend J).symm) w).det ≠ 0 := by
  have hsrc : (J.extendCoordChange φ' φ).source =
      (φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source := by
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      φ.extend_source]
  rcases J.isInvertible_fderivWithin_extendCoordChange hn hφ' hφ (hsrc ▸ interior_subset hw) with
    ⟨L, hL⟩
  rw [fderivWithin_of_mem_nhds (hsrc ▸ mem_of_superset (isOpen_interior.mem_nhds hw)
    interior_subset)] at hL
  rw [← PartialEquiv.coe_trans, ← hL]
  exact L.toLinearEquiv.isUnit_det'.ne_zero

omit [ChartedSpace H' X] in
/-- Neighborhood membership of `(φ.extend J).target` at `z` and `U` at `(φ.extend J).symm z` places
`z` in `interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U)`. -/
theorem _root_.OpenPartialHomeomorph.mem_interior_extend_target_inter_preimage
    (φ : OpenPartialHomeomorph X H') {U : Set X} {z : E}
    (hzt : (φ.extend J).target ∈ 𝓝 z) (hU : U ∈ 𝓝 ((φ.extend J).symm z)) :
    z ∈ interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U) :=
  mem_interior_iff_mem_nhds.2
    (inter_mem hzt (((φ.continuousOn_extend_symm (I := J)).continuousAt hzt).preimage_mem_nhds hU))

omit [ChartedSpace H' X] in
/-- Extending an open partial homeomorphism into `E` by `𝓘(𝕜, E)` gives `φ.toPartialEquiv`. -/
theorem _root_.OpenPartialHomeomorph.extend_modelWithCornersSelf (φ : OpenPartialHomeomorph X E) :
    φ.extend 𝓘(𝕜, E) = φ.toPartialEquiv := by
  rw [OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]

/-- At any `z ∈ interior (φ.extend J).target` for `φ ∈ maximalAtlas J 1 X`, `(φ.extend J).symm` is
differentiable and its `mfderivWithin` on `range J` equals `mfderiv`. -/
theorem _root_.OpenPartialHomeomorph.mdifferentiableAt_extend_symm_of_mem_interior
    {φ : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X) {z : E}
    (hz : z ∈ interior (φ.extend J).target) :
    MDifferentiableAt 𝓘(𝕜, E) J (φ.extend J).symm z ∧
      mfderivWithin 𝓘(𝕜, E) J (φ.extend J).symm (range J) z =
        mfderiv 𝓘(𝕜, E) J (φ.extend J).symm z :=
  have hznhds := mem_interior_iff_mem_nhds.1 hz
  ⟨(((φ.extend_target' (I := J) ▸ contMDiffOn_extend_symm hφ) z (interior_subset hz)).contMDiffAt
      hznhds).mdifferentiableAt one_ne_zero,
    mfderivWithin_of_mem_nhds (mem_of_superset hznhds φ.extend_target_subset_range)⟩

omit [ChartedSpace H' X] [ChartedSpace H M] in
/-- Continuity of `ψ.extend I ∘ u ∘ (φ.extend J).symm` on subsets of the chart overlap domain. -/
theorem _root_.OpenPartialHomeomorph.continuousOn_extend_comp_symm
    (φ : OpenPartialHomeomorph X H') (ψ : OpenPartialHomeomorph M H) {u : X → M} {s : Set X}
    (hc : ContinuousOn u s)
    {W : Set E} (hW : W ⊆ (φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :
    ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend J).symm) W :=
  ((ψ.continuousOn_extend (I := I)).mono ψ.extend_source.ge).comp
    (hc.comp ((φ.continuousOn_extend_symm (I := J)).mono (hW.trans inter_subset_left))
      fun _ hw ↦ (hW hw).2.1)
    fun _ hw ↦ (hW hw).2.2

/-- When `I` is boundaryless and `f : M → N` is `C¹` on open `t`, the coordinate domain is open in
`F` and `ψ'.extend I' ∘ f ∘ (ψ.extend I).symm` is `C¹` there. -/
theorem _root_.OpenPartialHomeomorph.isOpen_and_contDiffOn_extend_comp [I.Boundaryless]
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M)
    {ψ' : OpenPartialHomeomorph N H''} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' 1 N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t) :
    IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) ∧
      ContDiffOn 𝕜 1 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
        ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
  ⟨(ψ.continuousOn_extend_symm (I := I)).isOpen_inter_preimage (ψ.isOpen_extend_target (I := I))
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source),
    contMDiffOn_iff_contDiffOn.1 ((ψ'.contMDiffOn_extend hψ').comp
      (hf.comp ((ψ.extend_target' (I := I) ▸ contMDiffOn_extend_symm hψ).mono inter_subset_left)
        fun _ hw ↦ hw.2.1) fun _ hw ↦ hw.2.2)⟩

section Linear

variable (φ : OpenPartialHomeomorph X H') (ψ : OpenPartialHomeomorph M H) (u : X → M)
  (du du₁ du₂ : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) (z : E)

variable (J I) in
/-- Coordinate expression of `du : ∀ x, TangentSpace J x →L[𝕜] TangentSpace I (u x)` in charts `φ`
of `X` (through `J`) and `ψ` of `M` (through `I`). -/
def chartTangentHom (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) (z : E) :
    E →L[𝕜] F :=
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
@[simp] theorem chartTangentHom_smul (c : 𝕜)
    (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) (z : E) :
    chartTangentHom J I φ ψ u (fun x ↦ c • du x) z = c • chartTangentHom J I φ ψ u du z := by
  simp only [chartTangentHom, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end Linear

/-- `chartTangentHom` depends at `z` only on `du ((φ.extend J).symm z)`. -/
theorem chartTangentHom_congr {φ : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H}
    {u : X → M} {du du' : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)} {z : E}
    (h : du ((φ.extend J).symm z) = du' ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u du z = chartTangentHom J I φ ψ u du' z := by
  simp only [chartTangentHom, h]

/-- Pointwise congruence of `chartTangentHom` across maps agreeing up to `tangentSpaceCast`. -/
theorem chartTangentHom_congr_map {φ : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H}
    {u u' : X → M} {du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)}
    {du' : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u' x)} {z : E}
    (hu : u ((φ.extend J).symm z) = u' ((φ.extend J).symm z))
    (hdu : (tangentSpaceCast I (u ((φ.extend J).symm z))
        (u' ((φ.extend J).symm z))).toContinuousLinearMap.comp (du ((φ.extend J).symm z)) =
      du' ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u du z = chartTangentHom J I φ ψ u' du' z := by
  have hcast : ∀ (y₁ y₂ : M) (_ : y₁ = y₂)
      (L₁ : TangentSpace J ((φ.extend J).symm z) →L[𝕜] TangentSpace I y₁)
      (L₂ : TangentSpace J ((φ.extend J).symm z) →L[𝕜] TangentSpace I y₂),
      (tangentSpaceCast I y₁ y₂).toContinuousLinearMap.comp L₁ = L₂ →
      (mvfderiv I (ψ.extend I) y₁).comp L₁ = (mvfderiv I (ψ.extend I) y₂).comp L₂ := by
    rintro y _ rfl L₁ _ rfl; rfl
  simp only [chartTangentHom, ← ContinuousLinearMap.comp_assoc, hcast _ _ hu _ _ hdu]

/-- At `z ∈ interior (φ.extend J).target` mapped into `ψ.source`, `chartTangentHom` of
`mfderiv J I u` equals `fderiv 𝕜 (ψ.extend I ∘ u ∘ (φ.extend J).symm) z`. -/
theorem chartTangentHom_mfderiv {φ : OpenPartialHomeomorph X H'}
    (hφ : φ ∈ IsManifold.maximalAtlas J 1 X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {u : X → M} {z : E}
    (hz : z ∈ interior (φ.extend J).target) (hy : u ((φ.extend J).symm z) ∈ ψ.source)
    (hdu : MDifferentiableAt J I u ((φ.extend J).symm z)) :
    chartTangentHom J I φ ψ u (fun x ↦ mfderiv J I u x) z =
      fderiv 𝕜 (ψ.extend I ∘ u ∘ (φ.extend J).symm) z := by
  obtain ⟨hdφ, hmfw⟩ := φ.mdifferentiableAt_extend_symm_of_mem_interior hφ hz
  have hmv := mvfderiv_comp z ((ψ.contMDiffAt_extend hψ hy).mdifferentiableAt one_ne_zero)
    (hdu.comp z hdφ)
  rw [mfderiv_comp z hdu hdφ, mvfderiv_eq_fderiv] at hmv
  rw [chartTangentHom, hmfw]; ext v
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using
      (DFunLike.congr_fun hmv ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm v)).symm

/-- For `C¹` charts `φ` and `ψ`, `chartTangentHom` at `z ∈ (φ.extend J).target` with
`u ((φ.extend J).symm z) ∈ ψ.source` determines `du ((φ.extend J).symm z)`. -/
theorem chartTangentHom_eq_iff {φ : OpenPartialHomeomorph X H'}
    (hφ : φ ∈ IsManifold.maximalAtlas J 1 X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {u : X → M}
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

/-- In preferred charts at `x₀` and `y₀`, `chartTangentHom` agrees with
`ContinuousLinearMap.inCoordinates`. -/
theorem chartTangentHom_chartAt_eq_inCoordinates [IsManifold J 1 X] [IsManifold I 1 M]
    {u : X → M} (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x))
    {x₀ x : X} {y₀ : M} (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
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
  have hchart : ∀ x' : X, x' = x →
      mvfderiv I ((chartAt H y₀).extend I) (u x') ∘L du x' ∘L
        (mfderivWithin 𝓘(𝕜, E) J ((chartAt H' x₀).extend J).symm (range J) (extChartAt J x₀ x) ∘L
          (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (extChartAt J x₀ x)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.inCoordinates E (TangentSpace J) F (TangentSpace I)
        x₀ x y₀ (u x) (du x) := by rintro _ rfl; exact hcoord.symm
  exact hchart _ ((extChartAt J x₀).left_inv (by simpa only [extChartAt_source] using hx))

/-- Pointwise injectivity equivalence of `chartTangentHom` in preferred charts at `x₀` and `y₀`. -/
theorem chartTangentHom_chartAt_eq_iff [IsManifold J 1 X] [IsManifold I 1 M]
    {u : X → M} {du₁ du₂ : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)}
    {x₀ x : X} {y₀ : M} (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
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

/-- On the interior of a source-chart overlap, `chartTangentHom` transforms by precomposition with
`fderiv 𝕜 (φ.extend J ∘ (φ'.extend J).symm)` (neither `J` nor `I` need be boundaryless). -/
theorem chartTangentHom_comp_fderiv_transition
    {φ φ' : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X) (ψ : OpenPartialHomeomorph M H)
    {u : X → M} (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x))
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
  obtain ⟨hdφ', hmfw⟩ := φ'.mdifferentiableAt_extend_symm_of_mem_interior hφ' hwint
  have hΦint : Φ w ∈ interior (φ.extend J).target :=
    ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero hφ' hφ hxφ' hxφ
      (by rwa [(φ'.extend J).right_inv hwt])
  obtain ⟨hdφ, hmfΦ⟩ := φ.mdifferentiableAt_extend_symm_of_mem_interior hφ hΦint
  have hev : (φ'.extend J).symm =ᶠ[𝓝 w] (φ.extend J).symm ∘ Φ := by
    filter_upwards [isOpen_interior.mem_nhds hw] with z hz
    simp only [Φ, Function.comp_apply, φ.extend_left_inv (interior_subset hz).2]
  have hmf := hev.mfderiv_eq (I := 𝓘(𝕜, E)) (I' := J)
  rw [mfderiv_comp w hdφ (((φ.contMDiffAt_extend hφ hxφ).mdifferentiableAt one_ne_zero).comp w
    hdφ')] at hmf
  have hcast : ∀ (x₁ x₂ : X), x₁ = x₂ → ∀ (ξ₁ : TangentSpace J x₁) (ξ₂ : TangentSpace J x₂),
      tangentSpaceCast J x₁ x₂ ξ₁ = ξ₂ →
      mvfderiv I (ψ.extend I) (u x₁) (du x₁ ξ₁) = mvfderiv I (ψ.extend I) (u x₂) (du x₂ ξ₂) := by
    rintro x _ rfl ξ₁ _ rfl; rfl
  ext v; rw [ContinuousLinearMap.comp_apply, chartTangentHom_apply, chartTangentHom_apply, hmfΦ,
    hmfw]
  have hfd : (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (Φ w)).symm (fderiv 𝕜 Φ w v) =
      mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) Φ w ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) w).symm v) := by
    simp [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hfd]
  exact hcast _ _ (φ.extend_left_inv hxφ) _ _ (DFunLike.congr_fun hmf.symm _)

/-- When `M` is boundaryless, postcomposing `chartTangentHom` in chart `ψ` with
`fderiv 𝕜 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)` yields `chartTangentHom` of `(mfderiv f).comp du`
in chart `ψ'` (`N` may have corners). -/
theorem fderiv_extend_comp_chartTangentHom [I.Boundaryless]
    {φ : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {ψ' : OpenPartialHomeomorph N H''}
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I' 1 N) {f : M → N} {t : Set M}
    (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t) {u : X → M}
    (du : ∀ x : X, TangentSpace J x →L[𝕜] TangentSpace I (u x)) {z : E}
    (hy : u ((φ.extend J).symm z) ∈ ψ.source ∩ (t ∩ f ⁻¹' ψ'.source)) :
    (fderiv 𝕜 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
        (ψ.extend I (u ((φ.extend J).symm z)))).comp (chartTangentHom J I φ ψ u du z) =
      chartTangentHom J I' φ ψ' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) z := by
  set y := u ((φ.extend J).symm z)
  set g := ψ'.extend I' ∘ f ∘ (ψ.extend I).symm
  obtain ⟨hO, hg⟩ := ψ.isOpen_and_contDiffOn_extend_comp hψ hψ' hf ht
  have hyO : ψ.extend I y ∈ (ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source) :=
    ⟨(ψ.extend I).map_source (by rw [ψ.extend_source]; exact hy.1),
      by rw [mem_preimage, ψ.extend_left_inv hy.1]; exact hy.2⟩
  have hgd : DifferentiableAt 𝕜 g (ψ.extend I y) :=
    ((hg _ hyO).differentiableWithinAt one_ne_zero).differentiableAt (hO.mem_nhds hyO)
  have hev : ψ'.extend I' ∘ f =ᶠ[𝓝 y] g ∘ ψ.extend I := by
    filter_upwards [ψ.open_source.mem_nhds hy.1] with y' hy'
    simp only [g, Function.comp_apply, ψ.extend_left_inv hy']
  have hmv : (fderiv 𝕜 g (ψ.extend I y)).comp (mvfderiv I (ψ.extend I) y) =
      (mvfderiv I' (ψ'.extend I') (f y)).comp (mfderiv I I' f y) := by
    have h1 := mvfderiv_comp y hgd.mdifferentiableAt
      ((ψ.contMDiffAt_extend hψ hy.1).mdifferentiableAt one_ne_zero)
    rw [mvfderiv_eq_fderiv] at h1
    have hcast : ∀ (w₁ w₂ : F') (_ : w₁ = w₂)
        (L₁ : TangentSpace I y →L[𝕜] TangentSpace 𝓘(𝕜, F') w₁)
        (L₂ : TangentSpace I y →L[𝕜] TangentSpace 𝓘(𝕜, F') w₂),
        L₁ = (tangentSpaceCast 𝓘(𝕜, F') w₂ w₁).toContinuousLinearMap.comp L₂ →
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) w₁).toContinuousLinearMap.comp L₁ =
          (NormedSpace.fromTangentSpace (𝕜 := 𝕜) w₂).toContinuousLinearMap.comp L₂ := by
      rintro w _ rfl _ L₂ rfl; rfl
    exact h1.symm.trans ((hcast _ _ hev.symm.eq_of_nhds _ _ hev.symm.mfderiv_eq).trans
      (mvfderiv_comp y ((ψ'.contMDiffAt_extend hψ' hy.2.2).mdifferentiableAt one_ne_zero)
        (((hf y hy.2.1).contMDiffAt (ht.mem_nhds hy.2.1)).mdifferentiableAt one_ne_zero)))
  simp only [chartTangentHom_apply, y, Function.comp_apply, ← ContinuousLinearMap.comp_assoc, hmv]

end ChartTangentHom

end TauCeti
