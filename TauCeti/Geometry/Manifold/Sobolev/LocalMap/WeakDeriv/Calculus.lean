/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas

/-!
# Chart independence, chain rules, and existence of the weak differential

Building on `TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Basic`, this file proves the
chart calculus and global existence theorems for weak differentials of local Sobolev maps
`u : X → M` from a Riemann surface (with or without boundary) into a smooth manifold `M`:

* **Chart independence** (`TauCeti.hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas`,
  `TauCeti.hasWeakMFDerivOn_iff_of_subset_maximalAtlas`, `TauCeti.hasWeakMFDerivOn_iff_atlas`,
  `TauCeti.hasWeakMFDerivOn_iff_chartAt`,
  `TauCeti.hasWeakMFDerivOnBordered_iff_of_subset_maximalAtlas`):
  when `M` is boundaryless and its model space `F` is complete, testing weak derivatives in any
  covering subfamilies of the source and target maximal atlases suffices, including on bordered
  Riemann surfaces.
* **Weak chain rules** (`TauCeti.HasWeakMFDerivOnGroupoid.contMDiffOn_comp`,
  `ContMDiff.comp_hasWeakMFDeriv`, `Diffeomorph.hasWeakMFDerivOn_comp_iff`,
  `Diffeomorph.comp_hasWeakMFDerivOn`): postcomposing with a `C¹` map `f : M → N` from a
  boundaryless smooth manifold `M` into a (possibly cornered) manifold `N` composes the weak
  differential with `mfderiv I I' f (u x)`, and precomposing with a biholomorphism of surfaces
  pulls the weak differential back along `mfderiv`.
* **Global existence and first-order Sobolev characterization**
  (`TauCeti.MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid`,
  `TauCeti.MemWkpLocMapOn.exists_hasWeakMFDerivOn`,
  `TauCeti.MemWkpLocMap.exists_hasWeakMFDeriv`,
  `TauCeti.MemWkpLocMapOnBordered.exists_hasWeakMFDerivOnBordered`,
  `TauCeti.memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn`): on a Lindelöf surface `X` (with or
  without boundary), every local Sobolev map of order `1` into a boundaryless smooth manifold `M`
  admits a global weak differential `du`, constructed locally in preferred chart pairs and glued on
  a countable subcover using almost-everywhere uniqueness.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 3.1.
-/

public section

open Bundle Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

/-! ### Changing charts and postcomposing with differentiable maps -/

section Transitions

variable {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {I' : ModelWithCorners ℝ F' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

/-- Transporting a tangent vector along a basepoint equality `x₁ = x₂` via `tangentSpaceCast`
preserves `mvfderiv I (ψ.extend I) (u x) (du x ·)`. -/
private theorem mvfderiv_du_eq_of_tangentSpaceCast
    {ψ : OpenPartialHomeomorph M H} {u : X → M}
    {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {x₁ x₂ : X} (hx : x₁ = x₂) {ξ₁ : TangentSpace J x₁} {ξ₂ : TangentSpace J x₂}
    (hξ : tangentSpaceCast J x₁ x₂ ξ₁ = ξ₂) :
    mvfderiv I (ψ.extend I) (u x₁) (du x₁ ξ₁) = mvfderiv I (ψ.extend I) (u x₂) (du x₂ ξ₂) := by
  cases hx; exact congrArg (fun ξ ↦ mvfderiv I (ψ.extend I) (u x₁) (du x₁ ξ)) hξ

/-- On the interior of a source-chart overlap, `chartTangentHom` transforms by precomposition with
the Fréchet derivative of the chart transition `φ.extend J ∘ (φ'.extend J).symm`. Neither `J` nor
`I` need be boundaryless. -/
private theorem chartTangentHom_comp_fderiv_transition
    {φ φ' : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X) (ψ : OpenPartialHomeomorph M H)
    {u : X → M} (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x))
    {w : ℂ} (hw : w ∈ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source)) :
    (chartTangentHom J I φ ψ u du (φ.extend J ((φ'.extend J).symm w))).comp
        (fderiv ℝ (φ.extend J ∘ (φ'.extend J).symm) w) =
      chartTangentHom J I φ' ψ u du w := by
  let Φ := φ.extend J ∘ (φ'.extend J).symm
  change (chartTangentHom J I φ ψ u du (Φ w)).comp (fderiv ℝ Φ w) =
    chartTangentHom J I φ' ψ u du w
  have hwt : w ∈ (φ'.extend J).target := (interior_subset hw).1
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source := by
    rw [← φ'.extend_source (I := J)]; exact (φ'.extend J).map_target hwt
  have hxφ : (φ'.extend J).symm w ∈ φ.source := (interior_subset hw).2
  have hΦint : Φ w ∈ interior (φ.extend J).target :=
    ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero hφ' hφ hxφ' hxφ
      (by rw [(φ'.extend J).right_inv hwt]; exact interior_mono inter_subset_left hw)
  have hwR : range J ∈ 𝓝 w := Filter.mem_of_superset (isOpen_interior.mem_nhds hw)
    (interior_subset.trans (inter_subset_left.trans φ'.extend_target_subset_range))
  have hΦR : range J ∈ 𝓝 (Φ w) := Filter.mem_of_superset (isOpen_interior.mem_nhds hΦint)
    (interior_subset.trans φ.extend_target_subset_range)
  have hsymm' : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ'.extend J).symm (φ'.extend J).target := by
    rw [φ'.extend_target']; exact contMDiffOn_extend_symm hφ'
  have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ.extend J).symm (φ.extend J).target := by
    rw [φ.extend_target']; exact contMDiffOn_extend_symm hφ
  have hdΦ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Φ w :=
    ((φ.contMDiffAt_extend hφ hxφ).comp w ((hsymm' w hwt).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hw)
        (interior_subset.trans inter_subset_left)))).mdifferentiableAt one_ne_zero
  have hdφsymm : MDifferentiableAt 𝓘(ℝ, ℂ) J (φ.extend J).symm (Φ w) :=
    ((hsymm (Φ w) (interior_subset hΦint)).contMDiffAt
      (mem_interior_iff_mem_nhds.1 hΦint)).mdifferentiableAt one_ne_zero
  have hev : (φ'.extend J).symm =ᶠ[𝓝 w] (φ.extend J).symm ∘ Φ := by
    filter_upwards [isOpen_interior.mem_nhds hw] with z hz
    simp only [Φ, Function.comp_apply, (φ.extend J).left_inv
      (by rw [φ.extend_source]; exact (interior_subset hz).2)]
  have hmf := hev.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := J)
  rw [mfderiv_comp w hdφsymm hdΦ] at hmf
  have hleft : (φ.extend J).symm (Φ w) = (φ'.extend J).symm w :=
    (φ.extend J).left_inv (by rw [φ.extend_source]; exact hxφ)
  have hfd : ∀ v : ℂ, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Φ w)).symm (fderiv ℝ Φ w v) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Φ w ((NormedSpace.fromTangentSpace (𝕜 := ℝ) w).symm v) := by
    intro v; rw [mfderiv_eq_fderiv]; rfl
  ext v
  rw [ContinuousLinearMap.comp_apply, chartTangentHom_apply, chartTangentHom_apply,
    mfderivWithin_of_mem_nhds hΦR, mfderivWithin_of_mem_nhds hwR]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hfd v]
  exact mvfderiv_du_eq_of_tangentSpaceCast hleft (DFunLike.congr_fun hmf.symm _)

/-- The Fréchet derivative of a `C¹` chart transition `φ.extend J ∘ (φ'.extend J).symm` has
nonvanishing determinant at every interior point of the overlap domain. -/
private theorem det_fderiv_chart_transition_ne_zero
    {φ φ' : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X)
    {w : ℂ} (hw : w ∈ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source)) :
    (fderiv ℝ (φ.extend J ∘ (φ'.extend J).symm) w).det ≠ 0 := by
  set Φ := φ.extend J ∘ (φ'.extend J).symm
  set Ψ := φ'.extend J ∘ (φ.extend J).symm
  have hwt : w ∈ (φ'.extend J).target := (interior_subset hw).1
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source := by
    rw [← φ'.extend_source (I := J)]; exact (φ'.extend J).map_target hwt
  have hxφ : (φ'.extend J).symm w ∈ φ.source := (interior_subset hw).2
  have hΦint : Φ w ∈ interior (φ.extend J).target :=
    ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero hφ' hφ hxφ' hxφ
      (by rw [(φ'.extend J).right_inv hwt]; exact interior_mono inter_subset_left hw)
  have hsymm' : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ'.extend J).symm (φ'.extend J).target := by
    rw [φ'.extend_target']; exact contMDiffOn_extend_symm hφ'
  have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ.extend J).symm (φ.extend J).target := by
    rw [φ.extend_target']; exact contMDiffOn_extend_symm hφ
  have hΨd : DifferentiableAt ℝ Ψ (Φ w) := by
    have hc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 Ψ (Φ w) :=
      (φ'.contMDiffAt_extend hφ' (by
        simp only [Φ, Function.comp_apply,
          (φ.extend J).left_inv (by rw [φ.extend_source]; exact hxφ)]; exact hxφ')).comp (Φ w)
        ((hsymm (Φ w) (interior_subset hΦint)).contMDiffAt (mem_interior_iff_mem_nhds.1 hΦint))
    exact mdifferentiableAt_iff_differentiableAt.1 (hc.mdifferentiableAt one_ne_zero)
  have hΦd : DifferentiableAt ℝ Φ w := by
    have hc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 Φ w :=
      (φ.contMDiffAt_extend hφ hxφ).comp w ((hsymm' w hwt).contMDiffAt
        (Filter.mem_of_superset (isOpen_interior.mem_nhds hw)
          (interior_subset.trans inter_subset_left)))
    exact mdifferentiableAt_iff_differentiableAt.1 (hc.mdifferentiableAt one_ne_zero)
  have hid : Ψ ∘ Φ =ᶠ[𝓝 w] (fun z : ℂ ↦ z) := by
    filter_upwards [isOpen_interior.mem_nhds hw] with z hz
    simp only [Φ, Ψ, Function.comp_apply,
      (φ.extend J).left_inv (by rw [φ.extend_source]; exact (interior_subset hz).2),
      (φ'.extend J).right_inv (interior_subset hz).1]
  have hcomp : (fderiv ℝ Ψ (Φ w)).comp (fderiv ℝ Φ w) = ContinuousLinearMap.id ℝ ℂ := by
    rw [← fderiv_comp w hΨd hΦd, hid.fderiv_eq, fderiv_fun_id]
  intro h0
  have hmul := map_mul LinearMap.det (fderiv ℝ Ψ (Φ w) : ℂ →ₗ[ℝ] ℂ) (fderiv ℝ Φ w : ℂ →ₗ[ℝ] ℂ)
  change ((fderiv ℝ Ψ (Φ w)).comp (fderiv ℝ Φ w)).det =
    (fderiv ℝ Ψ (Φ w)).det * (fderiv ℝ Φ w).det at hmul
  rw [hcomp, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, h0, mul_zero]
    at hmul
  exact one_ne_zero hmul

/-- Precomposing a planar weak derivative with a chart transition `φ.extend J ∘ (φ'.extend J).symm`
on an open subset `W` of the interior overlap domain. -/
private theorem hasWeakFDerivOn_comp_chart_transition
    {φ φ' : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X) (ψ : OpenPartialHomeomorph M H)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {U W : Opens ℂ}
    (hU : HasWeakFDerivOn volume U (ψ.extend I ∘ u ∘ (φ.extend J).symm)
      (chartTangentHom J I φ ψ u du))
    (hW : (W : Set ℂ) ⊆ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source))
    (hmaps : MapsTo (φ.extend J ∘ (φ'.extend J).symm) W U) :
    HasWeakFDerivOn volume W (ψ.extend I ∘ u ∘ (φ'.extend J).symm)
      (chartTangentHom J I φ' ψ u du) := by
  set Φ := φ.extend J ∘ (φ'.extend J).symm
  have hsymm' : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ'.extend J).symm (φ'.extend J).target := by
    rw [φ'.extend_target']; exact contMDiffOn_extend_symm hφ'
  have hΦ : ContDiffOn ℝ 1 Φ W := contMDiffOn_iff_contDiffOn.1
    ((φ.contMDiffOn_extend hφ).comp
      (hsymm'.mono (hW.trans (interior_subset.trans inter_subset_left)))
      fun _ hz ↦ (interior_subset (hW hz)).2)
  have hinj : InjOn Φ W := fun z₁ hz₁ z₂ hz₂ heq ↦ by
    have h1 := congrArg (φ.extend J).symm heq
    dsimp only [Φ, Function.comp_apply] at h1
    rw [(φ.extend J).left_inv (by rw [φ.extend_source]; exact (interior_subset (hW hz₁)).2),
      (φ.extend J).left_inv (by rw [φ.extend_source]; exact (interior_subset (hW hz₂)).2)] at h1
    exact ((φ'.extend J).symm.injOn (interior_subset (hW hz₁)).1 (interior_subset (hW hz₂)).1) h1
  have hdet : ∀ w ∈ (W : Set ℂ), (fderiv ℝ Φ w).det ≠ 0 :=
    fun w hw ↦ det_fderiv_chart_transition_ne_zero hφ hφ' (hW hw)
  refine ((hU.comp_contDiffOn_diffeo hΦ hinj hdet hmaps).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    simp only [Φ, Function.comp_apply,
      (φ.extend J).left_inv (by rw [φ.extend_source]; exact (interior_subset (hW hw)).2)]
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    exact chartTangentHom_comp_fderiv_transition hφ hφ' ψ du (hW hw)

/-- Transferring a weak derivative for fixed target chart `ψ` from a covering subfamily `A` of
`C¹` source charts to an arbitrary `C¹` source chart `φ'`. -/
private theorem hasWeakFDerivOn_change_source_chart [CompleteSpace F]
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {s : Set X} (hc : ContinuousOn u s) (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X H')} (hAJ : A ⊆ IsManifold.maximalAtlas J 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {φ' : OpenPartialHomeomorph X H'} (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X)
    (ψ : OpenPartialHomeomorph M H)
    (hAψ : ∀ φ ∈ A, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ'.extend J).symm) (chartTangentHom J I φ' ψ u du) := by
  refine hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨φ, hφA, hxφ⟩ := hAs _ (interior_subset hz).2.1
  set W := Opens.interior ((φ'.extend J).target ∩
    (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source ∩ φ.source))
  have hzW : z ∈ W := by
    have hzt : (φ'.extend J).target ∈ 𝓝 z := Filter.mem_of_superset
      (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
    have hopen : IsOpen (s ∩ u ⁻¹' ψ.source ∩ φ.source) :=
      (hc.isOpen_inter_preimage hs ψ.open_source).inter φ.open_source
    exact mem_interior_iff_mem_nhds.2 (Filter.inter_mem hzt
      ((φ'.continuousOn_extend_symm.continuousAt hzt).preimage_mem_nhds
        (hopen.mem_nhds ⟨(interior_subset hz).2, hxφ⟩)))
  refine ⟨W, hzW, hasWeakFDerivOn_comp_chart_transition (hAJ hφA) hφ' ψ
    (hAψ φ hφA) (interior_mono (inter_subset_inter_right _
      (preimage_mono inter_subset_right))) fun w hw ↦ ?_⟩
  have hwt : w ∈ (φ'.extend J).target := (interior_subset hw).1
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source := by
    rw [← φ'.extend_source (I := J)]; exact (φ'.extend J).map_target hwt
  have hint := ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero
    hφ' (hAJ hφA) hxφ' (interior_subset hw).2.2
    (by rw [(φ'.extend J).right_inv hwt]; exact interior_mono inter_subset_left hw)
  have htnhds : (φ.extend J).target ∈ 𝓝 (φ.extend J ((φ'.extend J).symm w)) :=
    mem_interior_iff_mem_nhds.1 hint
  have hopen : IsOpen (s ∩ u ⁻¹' ψ.source) := hc.isOpen_inter_preimage hs ψ.open_source
  refine mem_interior_iff_mem_nhds.2 (Filter.inter_mem htnhds
    ((φ.continuousOn_extend_symm.continuousAt htnhds).preimage_mem_nhds ?_))
  rw [(φ.extend J).left_inv (by rw [φ.extend_source]; exact (interior_subset hw).2.2)]
  exact hopen.mem_nhds (interior_subset hw).2.1

/-- When `M` is boundaryless, postcomposing `chartTangentHom` in chart `ψ` with the Fréchet
derivative of `ψ'.extend I' ∘ f ∘ (ψ.extend I).symm` produces `chartTangentHom` of
`x ↦ (mfderiv I I' f (u x)).comp (du x)` in chart `ψ'`. Notice `N` (`I'`) may have corners. -/
private theorem fderiv_extend_comp_chartTangentHom [I.Boundaryless]
    {φ : OpenPartialHomeomorph X H'}
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H''} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t)
    {u : X → M} (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x))
    {z : ℂ} (hy : u ((φ.extend J).symm z) ∈ ψ.source ∩ (t ∩ f ⁻¹' ψ'.source)) :
    (fderiv ℝ (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
        (ψ.extend I (u ((φ.extend J).symm z)))).comp (chartTangentHom J I φ ψ u du z) =
      chartTangentHom J I' φ ψ' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) z := by
  set y := u ((φ.extend J).symm z)
  set g := ψ'.extend I' ∘ f ∘ (ψ.extend I).symm
  have hO : IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I 1 (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast le_top)
  have hg : ContDiffOn ℝ 1 g
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    contMDiffOn_iff_contDiffOn.1
      (((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast le_top)).comp
        (hf.comp (hsymm.mono inter_subset_left) fun _ hw ↦ hw.2.1) fun _ hw ↦ hw.2.2)
  have hy_ext : y ∈ (ψ.extend I).source := by rw [ψ.extend_source]; exact hy.1
  have hyO : ψ.extend I y ∈ (ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source) :=
    ⟨(ψ.extend I).map_source hy_ext, by rw [mem_preimage, (ψ.extend I).left_inv hy_ext]; exact hy.2⟩
  have hgd : DifferentiableAt ℝ g (ψ.extend I y) :=
    ((hg _ hyO).differentiableWithinAt one_ne_zero).differentiableAt (hO.mem_nhds hyO)
  have hψd : MDifferentiableAt I 𝓘(ℝ, F) (ψ.extend I) y :=
    (ψ.contMDiffAt_extend (StructureGroupoid.maximalAtlas_mono
      (contDiffGroupoid_le (by exact_mod_cast le_top)) hψ) hy.1).mdifferentiableAt one_ne_zero
  have hfd : MDifferentiableAt I I' f y :=
    ((hf y hy.2.1).contMDiffAt (ht.mem_nhds hy.2.1)).mdifferentiableAt one_ne_zero
  have hψ'd : MDifferentiableAt I' 𝓘(ℝ, F') (ψ'.extend I') (f y) :=
    (ψ'.contMDiffAt_extend (StructureGroupoid.maximalAtlas_mono
      (contDiffGroupoid_le (by exact_mod_cast le_top)) hψ') hy.2.2).mdifferentiableAt one_ne_zero
  have hev : ψ'.extend I' ∘ f =ᶠ[𝓝 y] g ∘ ψ.extend I := by
    filter_upwards [ψ.open_source.mem_nhds hy.1] with y' hy'
    simp only [g, Function.comp_apply,
      (ψ.extend I).left_inv (by rw [ψ.extend_source]; exact hy')]
  have hmv : (fderiv ℝ g (ψ.extend I y)).comp (mvfderiv I (ψ.extend I) y) =
      (mvfderiv I' (ψ'.extend I') (f y)).comp (mfderiv I I' f y) := by
    have h1 := mvfderiv_comp y hgd.mdifferentiableAt hψd
    rw [mvfderiv_eq_fderiv] at h1
    have h2 : mvfderiv I (g ∘ ψ.extend I) y = mvfderiv I (ψ'.extend I' ∘ f) y := by
      simp only [mvfderiv, hev.symm.mfderiv_eq]; rfl
    exact h1.symm.trans (h2.trans (mvfderiv_comp y hψ'd hfd))
  simp only [chartTangentHom_apply, y, Function.comp_apply, ← ContinuousLinearMap.comp_assoc, hmv]

/-- Applying the planar weak chain rule to `ψ'.extend I' ∘ f ∘ (ψ.extend I).symm` on an open set
`W ⊆ ℂ`. -/
private theorem hasWeakFDerivOn_extend_comp [I.Boundaryless] [CompleteSpace F']
    {φ : OpenPartialHomeomorph X H'}
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H''} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {W : Opens ℂ}
    (hW : HasWeakFDerivOn volume W (ψ.extend I ∘ u ∘ (φ.extend J).symm)
      (chartTangentHom J I φ ψ u du))
    (huc : ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend J).symm) W)
    (hmaps : MapsTo (u ∘ (φ.extend J).symm) W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    HasWeakFDerivOn volume W (ψ'.extend I' ∘ (f ∘ u) ∘ (φ.extend J).symm)
      (chartTangentHom J I' φ ψ' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x))) := by
  set g := ψ'.extend I' ∘ f ∘ (ψ.extend I).symm
  set O := (ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)
  have hO : IsOpen O :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I 1 (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast le_top)
  have hg : ContDiffOn ℝ 1 g O := contMDiffOn_iff_contDiffOn.1
    (((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast le_top)).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hw ↦ hw.2.1) fun _ hw ↦ hw.2.2)
  have hmaps' : MapsTo (ψ.extend I ∘ u ∘ (φ.extend J).symm) W O := fun w hw ↦ by
    have hsrc : u ((φ.extend J).symm w) ∈ (ψ.extend I).source := by
      rw [ψ.extend_source]; exact (hmaps hw).1
    refine ⟨(ψ.extend I).map_source hsrc, ?_⟩
    rw [mem_preimage, Function.comp_apply, Function.comp_apply, (ψ.extend I).left_inv hsrc]
    exact (hmaps hw).2
  refine ((hW.contDiffOn_comp huc hO hg hmaps').congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    dsimp only [g, Function.comp_apply]
    rw [(ψ.extend I).left_inv (by rw [ψ.extend_source]; exact (hmaps hw).1)]
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    exact fderiv_extend_comp_chartTangentHom hψ hψ' hf ht du (hmaps hw)

/-! ### Chart independence and the weak chain rule at groupoid generality -/

/-- **Chart independence of the weak differential.** When `M` is boundaryless and `F` is complete,
testing `HasWeakMFDerivOnGroupoid` on an open set `s` reduces to any covering subfamilies
`A ⊆ G.maximalAtlas X` and `B ⊆ IsManifold.maximalAtlas I ∞ M`, including when `X` has
boundary. -/
theorem hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {s : Set X} (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X H')} (hA : A ⊆ G.maximalAtlas X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun φ hφ ψ hψ ↦ h.hasWeakFDerivOn_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2
      ⟨hc, fun φ' hφ' ψ' hψ' ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩⟩
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ (interior_subset hz).2.1
  have h1 := hasWeakFDerivOn_change_source_chart hc hs (hA.trans hG) hAs (hG hφ') ψ
    fun φ hφ ↦ h φ hφ ψ hψB
  set W := Opens.interior ((φ'.extend J).target ∩
    (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source)))
  have hzW : z ∈ W := by
    have hzt : (φ'.extend J).target ∈ 𝓝 z := Filter.mem_of_superset
      (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
    have hopen : IsOpen (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source)) :=
      hc.isOpen_inter_preimage hs (ψ.open_source.inter ψ'.open_source)
    exact mem_interior_iff_mem_nhds.2 (Filter.inter_mem hzt
      ((φ'.continuousOn_extend_symm.continuousAt hzt).preimage_mem_nhds
        (hopen.mem_nhds ⟨(interior_subset hz).2.1, hxψ, (interior_subset hz).2.2⟩)))
  have hWsub : (W : Set ℂ) ⊆
      interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    interior_mono (inter_subset_inter_right _
      (preimage_mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))))
  have huc : ContinuousOn (ψ.extend I ∘ u ∘ (φ'.extend J).symm) W :=
    ((ψ.continuousOn_extend (I := I)).mono ψ.extend_source.ge).comp
      (hc.comp
        (φ'.continuousOn_extend_symm.mono (hWsub.trans (interior_subset.trans inter_subset_left)))
        fun _ hw ↦ (interior_subset (hWsub hw)).2.1)
      fun _ hw ↦ (interior_subset (hWsub hw)).2.2
  have hcomp := hasWeakFDerivOn_extend_comp (hB hψB) hψ' contMDiffOn_id isOpen_univ
    (h1.mono hWsub) huc fun w hw ↦
      ⟨(interior_subset hw).2.2.1, mem_univ _, (interior_subset hw).2.2.2⟩
  refine ⟨W, hzW, hcomp.congr_ae_deriv ?_⟩
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with w _
  exact chartTangentHom_congr (by rw [mfderiv_id, ContinuousLinearMap.id_comp])

/-- **The weak chain rule for maps into manifolds.** Let `M` be boundaryless and smooth. If `u` has
weak differential `du` on an open set `s`, mapping `s` into an open set `t` where `f : M → N` is
`C^n` (`1 ≤ n`), then `f ∘ u` has weak differential `x ↦ (mfderiv I I' f (u x)).comp (du x)` on
`s`. Neither `X` (`J`) nor `N` (`I'`) need be boundaryless. -/
theorem HasWeakMFDerivOnGroupoid.contMDiffOn_comp [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N} {t : Set M}
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s : Set X}
    (hu : HasWeakMFDerivOnGroupoid G J I u du s) (hf : ContMDiffOn I I' n f t) (hn : 1 ≤ n)
    (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    HasWeakMFDerivOnGroupoid G J I' (f ∘ u)
      (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) s := by
  have hc : ContinuousOn (f ∘ u) s := hf.continuousOn.comp hu.continuousOn hst
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨hc, fun φ hφ ψ' hψ' ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩
  let y₀ := u ((φ.extend J).symm z)
  set W := Opens.interior ((φ.extend J).target ∩
    (φ.extend J).symm ⁻¹' (s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source)))
  have hzW : z ∈ W := by
    have hzt : (φ.extend J).target ∈ 𝓝 z := Filter.mem_of_superset
      (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
    have hset : (s ∩ u ⁻¹' (chartAt H y₀).source) ∩ (s ∩ (f ∘ u) ⁻¹' ψ'.source) =
        s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source) := by
      ext x; simp only [mem_inter_iff]; tauto
    have hopen : IsOpen (s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source)) :=
      hset ▸ (hu.continuousOn.isOpen_inter_preimage hs (chartAt H y₀).open_source).inter
        (hc.isOpen_inter_preimage hs ψ'.open_source)
    exact mem_interior_iff_mem_nhds.2 (Filter.inter_mem hzt
      ((φ.continuousOn_extend_symm.continuousAt hzt).preimage_mem_nhds
        (hopen.mem_nhds ⟨(interior_subset hz).2.1, mem_chart_source H y₀,
          (interior_subset hz).2.2⟩)))
  have hWsub : (W : Set ℂ) ⊆
      interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)) :=
    interior_mono (inter_subset_inter_right _
      (preimage_mono (inter_subset_inter_right _ inter_subset_left)))
  have huc : ContinuousOn (extChartAt I y₀ ∘ u ∘ (φ.extend J).symm) W :=
    (((chartAt H y₀).continuousOn_extend (I := I)).mono (chartAt H y₀).extend_source.ge).comp
      (hu.continuousOn.comp
        (φ.continuousOn_extend_symm.mono (hWsub.trans (interior_subset.trans inter_subset_left)))
        fun _ hw ↦ (interior_subset (hWsub hw)).2.1)
      fun _ hw ↦ (interior_subset (hWsub hw)).2.2
  exact ⟨W, hzW, hasWeakFDerivOn_extend_comp (IsManifold.chart_mem_maximalAtlas y₀) hψ'
    (hf.of_le hn) ht
    ((hu.hasWeakFDerivOn_chart hφ (IsManifold.chart_mem_maximalAtlas y₀)).mono hWsub) huc
    fun w hw ↦ ⟨(interior_subset hw).2.2.1, hst (interior_subset hw).2.1,
      (interior_subset hw).2.2.2⟩⟩

/-- Global weak chain rule for postcomposition with a `C^n` (`1 ≤ n`) map `f : M → N`. -/
theorem _root_.ContMDiff.comp_hasWeakMFDerivGroupoid [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N}
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    (hf : ContMDiff I I' n f) (hu : HasWeakMFDerivGroupoid G J I u du) (hn : 1 ≤ n) :
    HasWeakMFDerivGroupoid G J I' (f ∘ u)
      (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) :=
  hasWeakMFDerivOnGroupoid_univ.1 ((hasWeakMFDerivOnGroupoid_univ.2 hu).contMDiffOn_comp
    hf.contMDiffOn hn isOpen_univ isOpen_univ (mapsTo_univ _ _))

/-! ### Existence of a global weak differential -/

/-- Pulling a planar derivative field `D : ℂ → ℂ →L[ℝ] F` in preferred charts `(x₀, y₀)` back to a
family of tangent-space maps `du : ∀ x, TangentSpace J x →L[ℝ] TangentSpace I (u x)`. -/
private def pullbackChartDeriv [IsManifold J 1 X] [IsManifold I 1 M]
    (u : X → M) (x₀ : X) (y₀ : M) (D : ℂ → ℂ →L[ℝ] F) (x : X) :
    TangentSpace J x →L[ℝ] TangentSpace I (u x) :=
  open Classical in
  if hx : x ∈ (trivializationAt ℂ (TangentSpace J) x₀).baseSet then
    if hy : u x ∈ (trivializationAt F (TangentSpace I) y₀).baseSet then
      (((trivializationAt F (TangentSpace I) y₀).continuousLinearEquivAt ℝ (u x) hy).symm :
        F →L[ℝ] TangentSpace I (u x)) ∘L D (extChartAt J x₀ x) ∘L
        ((trivializationAt ℂ (TangentSpace J) x₀).continuousLinearEquivAt ℝ x hx :
          TangentSpace J x →L[ℝ] ℂ)
    else 0
  else 0

/-- On `(chartAt H' x₀).source ∩ u ⁻¹' (chartAt H y₀).source`, `pullbackChartDeriv` recovers `D`
under `chartTangentHom` in the preferred charts `(chartAt H' x₀, chartAt H y₀)`. -/
private theorem chartTangentHom_pullbackChartDeriv [IsManifold J 1 X] [IsManifold I 1 M]
    {u : X → M} {x₀ x : X} {y₀ : M} (D : ℂ → ℂ →L[ℝ] F)
    (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
    chartTangentHom J I (chartAt H' x₀) (chartAt H y₀) u (pullbackChartDeriv u x₀ y₀ D)
        (extChartAt J x₀ x) =
      D (extChartAt J x₀ x) := by
  rw [chartTangentHom_chartAt_eq_inCoordinates _ hx hy]
  have hx' : x ∈ (trivializationAt ℂ (TangentSpace J) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hy' : u x ∈ (trivializationAt F (TangentSpace I) y₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  rw [ContinuousLinearMap.inCoordinates_eq hx' hy']
  ext v
  dsimp only [pullbackChartDeriv]
  simp only [hx', hy', ↓reduceDIte, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- Existence of a weak differential on a single chart-pair neighborhood
`s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)`. -/
private theorem exists_local_hasWeakMFDerivOnGroupoid
    [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} {s : Set X}
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) (x₀ : X) :
    ∃ d : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u d
        (s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  let U₀ := s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)
  have hset : (s ∩ (chartAt H' x₀).source) ∩ (s ∩ u ⁻¹' (chartAt H (u x₀)).source) = U₀ := by
    ext x; simp only [U₀, mem_inter_iff]; tauto
  have hUo : IsOpen U₀ := hset ▸ (hs.inter (chartAt H' x₀).open_source).inter
    (hu.continuousOn.isOpen_inter_preimage hs (chartAt H (u x₀)).open_source)
  obtain ⟨D, hD, -⟩ := (hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas (u x₀))).exists_weakFDeriv
  refine ⟨pullbackChartDeriv u x₀ (u x₀) D,
    (hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG hUo
      (singleton_subset_iff.2 (StructureGroupoid.chart_mem_maximalAtlas G x₀))
      (fun x hx ↦ ⟨_, rfl, hx.2.1⟩)
      (singleton_subset_iff.2 (IsManifold.chart_mem_maximalAtlas (u x₀)))
      (fun x hx ↦ ⟨_, rfl, hx.2.2⟩)).2 ⟨hu.continuousOn.mono inter_subset_left, ?_⟩⟩
  rintro _ rfl _ rfl
  have hsub : interior ((extChartAt J x₀).target ∩
      (extChartAt J x₀).symm ⁻¹' (U₀ ∩ u ⁻¹' (chartAt H (u x₀)).source)) ⊆
    interior ((extChartAt J x₀).target ∩
      (extChartAt J x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H (u x₀)).source)) :=
    interior_mono (inter_subset_inter_right _ (preimage_mono fun _ hx ↦ ⟨hx.1.1, hx.2⟩))
  refine (hD.mono hsub).congr_ae_deriv ?_
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  have hzt : z ∈ (extChartAt J x₀).target := (interior_subset hz).1
  have hzx : (extChartAt J x₀).symm z ∈ (chartAt H' x₀).source := (interior_subset hz).2.1.2.1
  have hzu : u ((extChartAt J x₀).symm z) ∈ (chartAt H (u x₀)).source := (interior_subset hz).2.2
  have heq := chartTangentHom_pullbackChartDeriv (J := J) (I := I) D hzx hzu
  rw [(extChartAt J x₀).right_inv hzt] at heq
  exact heq.symm

/-- **Existence of a global weak differential.** On a Lindelöf surface `X` (with or without
boundary) and an open set `s ⊆ X`, every local Sobolev map `u : X → M` of order `1` into a
boundaryless smooth manifold `M` admits a weak differential `du` on `s`. -/
theorem MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} {s : Set X}
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u du s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ ↦ 0, hasWeakMFDerivOnGroupoid_iff.2 ⟨continuousOn_empty u, fun φ _ ψ _ ↦ ?_⟩⟩
    have hemp : Opens.interior ((φ.extend J).target ∩
        (φ.extend J).symm ⁻¹' (∅ ∩ u ⁻¹' ψ.source)) = ⊥ := Opens.ext (by simp)
    rw [hemp]
    exact hasWeakFDerivOn_iff_locally.2 fun _ hz ↦ False.elim hz
  have : SecondCountableTopology H' := J.secondCountableTopology
  obtain ⟨C, hCcnt, hCcov⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : X ↦ (chartAt H' x).source)
    (fun x ↦ (chartAt H' x).open_source.mem_nhds (mem_chart_source H' x))
  have : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_countable_cover H' hCcov hCcnt
  let U : X → Set X := fun x₀ ↦
    s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)
  have hUo : ∀ x₀, IsOpen (U x₀) := fun x₀ ↦ by
    have hset : (s ∩ (chartAt H' x₀).source) ∩ (s ∩ u ⁻¹' (chartAt H (u x₀)).source) = U x₀ := by
      ext x; simp only [U, mem_inter_iff]; tauto
    exact hset ▸ (hs.inter (chartAt H' x₀).open_source).inter
      (hu.continuousOn.isOpen_inter_preimage hs (chartAt H (u x₀)).open_source)
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable (fun i : s ↦ U i.1) (fun i ↦ hUo i.1)
  have hTs : s = ⋃ i ∈ T, U i.1 := Subset.antisymm
    (fun x hxs ↦ hTcov.symm ▸ mem_iUnion.2
      ⟨⟨x, hxs⟩, hxs, mem_chart_source H' x, mem_chart_source H (u x)⟩)
    (iUnion₂_subset fun _ _ ↦ inter_subset_left)
  obtain ⟨x₁, hx₁s⟩ := hne
  rcases mem_iUnion₂.1 (hTs ▸ hx₁s) with ⟨i₀, hi₀T, -⟩
  have : Nonempty T := ⟨⟨i₀, hi₀T⟩⟩
  have : Countable T := hTcnt.to_subtype
  obtain ⟨q, hqsurj⟩ := exists_surjective_nat T
  choose d hd using fun n : ℕ ↦ exists_local_hasWeakMFDerivOnGroupoid hG hu hs (q n).1.1
  classical
  let du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x) := fun x ↦
    if h : ∃ n : ℕ, x ∈ U (q n).1.1 then d (Nat.find h) x else 0
  have hcov_nat : s = ⋃ n : ℕ, U (q n).1.1 := by
    ext x; rw [Set.ext_iff.1 hTs x]; simp only [mem_iUnion, exists_prop]
    exact ⟨fun ⟨i, hiT, hx⟩ ↦ let ⟨n, hn⟩ := hqsurj ⟨i, hiT⟩; ⟨n, by simpa [hn] using hx⟩,
      fun ⟨n, hx⟩ ↦ ⟨(q n).1, (q n).2, hx⟩⟩
  refine ⟨du, hcov_nat ▸ (hasWeakMFDerivOnGroupoid_iUnion_iff (fun n ↦ hUo (q n).1.1)).2
    fun n ↦ (hd n).congr_of_isNullSet hG ?_⟩
  refine (IsNullSet.iUnion fun k : ℕ ↦ ((hd n).mono inter_subset_left).isNullSet_ne
    ((hUo _).inter (hUo _)) ((hd k).mono inter_subset_right)).mono fun x ⟨hxn, hxne⟩ ↦ ?_
  have hex : ∃ k : ℕ, x ∈ U (q k).1.1 := ⟨n, hxn⟩
  refine mem_iUnion.2 ⟨Nat.find hex, ⟨hxn, Nat.find_spec hex⟩, fun heq ↦ hxne ?_⟩
  simp only [du, hex, ↓reduceDIte, heq]

/-- Global existence of a weak differential for a structure groupoid `G`. -/
theorem MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} (hu : MemWkpLocMapGroupoid G J I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivGroupoid G J I u du := by
  obtain ⟨du, hdu⟩ :=
    (memWkpLocMapOnGroupoid_univ.2 hu).exists_hasWeakMFDerivOnGroupoid hG isOpen_univ
  exact ⟨du, hasWeakMFDerivOnGroupoid_univ.1 hdu⟩

end Transitions

/-! ### Riemann surfaces without boundary -/

section BoundarylessSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {s : Set X}

/-- **Chart independence** on a Riemann surface without boundary: covering subfamilies of the
maximal atlases suffice. -/
theorem hasWeakMFDerivOn_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  have ht : ∀ φ : OpenPartialHomeomorph X ℂ, (φ.extend 𝓘(ℝ, ℂ)).target = φ.target := fun φ ↦ by
    simp [mfld_simps]
  have hs' : ∀ φ : OpenPartialHomeomorph X ℂ, ⇑(φ.extend 𝓘(ℝ, ℂ)).symm = ⇑φ.symm := fun φ ↦ by
    ext z; simp [mfld_simps]
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs hA hAs hB hBs]
  simp only [ht, hs']

/-- Chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDerivOn_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) :=
  hasWeakMFDerivOn_iff_of_subset_maximalAtlas hs IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Global chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  rw [← hasWeakMFDerivOn_univ, hasWeakMFDerivOn_iff_atlas isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: testing the preferred charts `chartAt ℂ x` and `chartAt H y` suffices. -/
theorem hasWeakMFDerivOn_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  rw [hasWeakMFDerivOn_iff_of_subset_maximalAtlas hs (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩)]
  simp only [forall_mem_range, extChartAt]

/-- Global chart independence: testing the preferred charts of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  rw [← hasWeakMFDerivOn_univ, hasWeakMFDerivOn_iff_chartAt isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

/-- On `ℂ` and a Banach space `F`, `HasWeakMFDerivOn 𝓘(ℝ, F)` on an open set `Ω ⊆ ℂ` is equivalent
to continuity on `Ω` together with `HasWeakFDerivOn volume Ω u` for the transported derivative
field. -/
theorem hasWeakMFDerivOn_model_iff [CompleteSpace F] {u : ℂ → F}
    {du : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, F) (u z)} {Ω : Opens ℂ} :
    HasWeakMFDerivOn 𝓘(ℝ, F) u du Ω ↔
      ContinuousOn u Ω ∧ HasWeakFDerivOn volume Ω u
        (fun z ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap ∘L du z ∘L
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) := by
  rw [hasWeakMFDerivOn_iff_chartAt Ω.isOpen]
  have hdom : ∀ (x : ℂ) (y : F),
      Opens.interior ((chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((Ω : Set ℂ) ∩ u ⁻¹' (chartAt F y).source)) = Ω :=
    fun _ _ ↦ Opens.ext (by simp [chartAt_self_eq])
  have hextF : ∀ (x : ℂ) (y : F), extChartAt 𝓘(ℝ, F) y ∘ u ∘ (chartAt ℂ x).symm = u :=
    fun _ _ ↦ by ext z; simp [chartAt_self_eq]
  have hch : ∀ (x : ℂ) (y : F),
      chartTangentHom 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (chartAt ℂ x) (chartAt F y) u du =
        fun z ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap ∘L
          du z ∘L (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap :=
    fun _ _ ↦ funext (chartTangentHom_refl du)
  simp only [hdom, hextF, hch, forall_const]

/-- Weak chain rule on a Riemann surface without boundary. -/
theorem HasWeakMFDerivOn.contMDiffOn_comp [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : HasWeakMFDerivOn I u du s) (hf : ContMDiffOn I I' n f t) (hn : 1 ≤ n)
    (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    HasWeakMFDerivOn I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) s :=
  HasWeakMFDerivOnGroupoid.contMDiffOn_comp hu hf hn hs ht hst

/-- Global weak chain rule on a Riemann surface without boundary. -/
theorem _root_.ContMDiff.comp_hasWeakMFDeriv [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} {f : M → N} (hf : ContMDiff I I' n f) (hu : HasWeakMFDeriv I u du) (hn : 1 ≤ n) :
    HasWeakMFDeriv I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) :=
  hf.comp_hasWeakMFDerivGroupoid hu hn

/-- Postcomposing with a `C^n` (`1 ≤ n`) diffeomorphism of boundaryless targets transforms weak
differentials by `mfderiv I I' e`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOn_comp_iff [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F] [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOn I' (e ∘ u) (fun x ↦ (mfderiv I I' e (u x)).comp (du x)) s ↔
      HasWeakMFDerivOn I u du s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp e.contMDiff.contMDiffOn hn hs isOpen_univ
    (mapsTo_univ _ _)⟩
  have hback :=
    h.contMDiffOn_comp e.symm.contMDiff.contMDiffOn hn hs isOpen_univ (mapsTo_univ _ _)
  have heq_u : e.symm ∘ e ∘ u = u := by ext x; simp
  have hid : ∀ x, (mfderiv I' I e.symm (e (u x))).comp ((mfderiv I I' e (u x)).comp (du x)) =
      (mfderiv I I (e.symm ∘ e) (u x)).comp (du x) := fun x ↦ by
    have hd₁ : MDifferentiableAt I' I e.symm (e (u x)) :=
      (e.symm.contMDiff.of_le hn (e (u x))).mdifferentiableAt one_ne_zero
    have hd₂ : MDifferentiableAt I I' e (u x) :=
      (e.contMDiff.of_le hn (u x)).mdifferentiableAt one_ne_zero
    rw [← ContinuousLinearMap.comp_assoc, ← mfderiv_comp (u x) hd₁ hd₂]
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨(e.symm.continuous.comp_continuousOn h.continuousOn).congr (fun x _ ↦ by simp),
      fun φ hφ ψ hψ ↦ ?_⟩
  have hchart := hback.hasWeakFDerivOn_chart hφ hψ
  have hdom : Opens.interior ((φ.extend 𝓘(ℝ, ℂ)).target ∩
      (φ.extend 𝓘(ℝ, ℂ)).symm ⁻¹' (s ∩ (e.symm ∘ e ∘ u) ⁻¹' ψ.source)) =
    Opens.interior ((φ.extend 𝓘(ℝ, ℂ)).target ∩
      (φ.extend 𝓘(ℝ, ℂ)).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by rw [heq_u]
  rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards with z; simp
  · filter_upwards with z
    let x := (φ.extend 𝓘(ℝ, ℂ)).symm z
    have hev : e.symm ∘ e =ᶠ[𝓝 (u x)] id :=
      Filter.Eventually.of_forall fun y ↦ e.symm_apply_apply y
    have hmf := hev.mfderiv_eq (I := I) (I' := I)
    rw [mfderiv_id] at hmf
    have hcast : ∀ (y₁ y₂ : M), y₁ = y₂ → ∀ (ξ₁ : TangentSpace I y₁) (ξ₂ : TangentSpace I y₂),
        ξ₁ = tangentSpaceCast I y₂ y₁ ξ₂ →
        mvfderiv I (ψ.extend I) y₁ ξ₁ = mvfderiv I (ψ.extend I) y₂ ξ₂ := by
      rintro y _ rfl ξ₁ ξ₂ hξ; exact congrArg _ hξ
    ext v
    rw [chartTangentHom_apply, chartTangentHom_apply]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    refine hcast _ _ (e.symm_apply_apply (u x)) _ _ ?_
    have hidv := DFunLike.congr_fun (hid x)
      ((mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (φ.extend 𝓘(ℝ, ℂ)).symm (range 𝓘(ℝ, ℂ)) z)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap v))
    simp only [ContinuousLinearMap.comp_apply] at hidv
    rw [hidv, hmf]; rfl

/-- Transporting a holomorphic chart `φ` of `Y` along a biholomorphism `e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X`
produces a holomorphic chart of `X`. -/
private theorem trans_mem_maximalAtlas_of_diffeomorph
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n)
    {φ : OpenPartialHomeomorph Y ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 Y) :
    e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X := by
  let φ' := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn φ' ?_ ?_
  · exact (contMDiffOn_of_mem_maximalAtlas hφ).comp
      (e.symm.contMDiff.of_le hn).contMDiffOn fun x hx ↦ hx.2
  · have hsymm : ⇑φ'.symm = e ∘ ⇑φ.symm := by ext w; simp [φ', mfld_simps]
    rw [hsymm]
    exact (e.contMDiff.of_le hn).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono (by simp [φ', mfld_simps]))

/-- Precomposing `u : X → M` with a biholomorphism `e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X` (`1 ≤ n`) pulls a
weak differential `du` on `s` back to `y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)` on
`e ⁻¹' s`. -/
theorem _root_.Diffeomorph.comp_hasWeakMFDerivOn
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n)
    (hu : HasWeakMFDerivOn I u du s) :
    HasWeakMFDerivOn I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) (e ⁻¹' s) := by
  have heR : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 e := by
    have h := (e.contMDiff.of_le hn).restrictScalars ℝ
    rwa [modelWithCornersSelf_restrictScalars] at h
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨hu.continuousOn.comp e.continuous.continuousOn (mapsTo_preimage e s), fun φ hφ ψ hψ ↦ ?_⟩
  let φ' : OpenPartialHomeomorph X ℂ := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ
  have hchart := hu.hasWeakFDerivOn_chart (trans_mem_maximalAtlas_of_diffeomorph e hn hφ) hψ
  have ht' : (φ'.extend 𝓘(ℝ, ℂ)).target = φ.target := by simp [φ', mfld_simps]
  have hs' : ⇑(φ'.extend 𝓘(ℝ, ℂ)).symm = e ∘ ⇑φ.symm := by ext w; simp [φ', mfld_simps]
  have htφ : (φ.extend 𝓘(ℝ, ℂ)).target = φ.target := by simp [mfld_simps]
  have hsφ : ⇑(φ.extend 𝓘(ℝ, ℂ)).symm = ⇑φ.symm := by ext w; simp [mfld_simps]
  have hdom : Opens.interior ((φ'.extend 𝓘(ℝ, ℂ)).target ∩
      (φ'.extend 𝓘(ℝ, ℂ)).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) =
    Opens.interior ((φ.extend 𝓘(ℝ, ℂ)).target ∩
      (φ.extend 𝓘(ℝ, ℂ)).symm ⁻¹' (e ⁻¹' s ∩ (u ∘ e) ⁻¹' ψ.source)) := by
    rw [ht', hs', htφ, hsφ]; rfl
  rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards with z; dsimp only [Function.comp_apply]; rw [congr_fun hs' z, congr_fun hsφ z]
    rfl
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    have hdφ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z :=
      mdifferentiableAt_symm_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ)
        (htφ ▸ (interior_subset hz).1)
    have hcomp : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (φ'.extend 𝓘(ℝ, ℂ)).symm z =
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e ((φ.extend 𝓘(ℝ, ℂ)).symm z)).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (φ.extend 𝓘(ℝ, ℂ)).symm z) := by
      rw [hs', hsφ, mfderiv_comp z ((heR (φ.symm z)).mdifferentiableAt one_ne_zero) hdφ]
    ext v
    rw [chartTangentHom_apply, chartTangentHom_apply, ModelWithCorners.Boundaryless.range_eq_univ,
      mfderivWithin_univ, mfderivWithin_univ]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    refine mvfderiv_du_eq_of_tangentSpaceCast (by rw [congr_fun hs' z, congr_fun hsφ z]; rfl) ?_
    rw [hcomp]; rfl

/-- Global precomposition of a weak differential with a biholomorphism
`e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X`. -/
theorem _root_.Diffeomorph.comp_hasWeakMFDeriv
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n)
    (hu : HasWeakMFDeriv I u du) :
    HasWeakMFDeriv I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) := by
  rw [← hasWeakMFDerivOn_univ] at hu ⊢
  simpa only [preimage_univ] using e.comp_hasWeakMFDerivOn hn hu

/-- **Existence of a weak differential on a Riemann surface without boundary.** On a Lindelöf
Riemann surface `X` and an open set `s ⊆ X`, every map `u ∈ MemWkpLocMapOn I p 1 u s` into a
boundaryless smooth manifold `M` has a weak differential on `s`. -/
theorem MemWkpLocMapOn.exists_hasWeakMFDerivOn
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOn I u du s := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hu hs

/-- **Global existence of a weak differential on a Riemann surface without boundary.** -/
theorem MemWkpLocMap.exists_hasWeakMFDeriv
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    (hu : MemWkpLocMap I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDeriv I u du := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hu

/-- **First-order Sobolev characterization via the weak differential.** On a Lindelöf Riemann
surface `X` and an open set `s ⊆ X`, a map `u : X → M` into a boundaryless smooth manifold lies in
`W^{1,p}_loc` on `s` if and only if it admits a weak differential `du` on `s` whose preferred-chart
expressions lie in `MemLpLoc p`. -/
theorem memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    (hs : IsOpen s) :
    MemWkpLocMapOn I p 1 u s ↔
      ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivOn I u du s ∧ ∀ x : X, ∀ y : M,
          MemLpLoc p
            ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
            (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  have ht : ∀ x : X, ((chartAt ℂ x).extend 𝓘(ℝ, ℂ)).target = (chartAt ℂ x).target := fun x ↦ by
    simp [mfld_simps]
  have hs' : ∀ x : X, ⇑((chartAt ℂ x).extend 𝓘(ℝ, ℂ)).symm = ⇑(chartAt ℂ x).symm := fun x ↦ by
    ext z; simp [mfld_simps]
  constructor
  · intro hu
    obtain ⟨du, hdu⟩ := MemWkpLocMapOn.exists_hasWeakMFDerivOn hu hs
    refine ⟨du, hdu, fun x y ↦ ?_⟩
    have hLp := hdu.memLpLoc_chart hu hs
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y)
    rwa [ht x, hs' x] at hLp
  · rintro ⟨du, hdu, hLp⟩
    refine (memWkpLocMapOn_iff_chartAt le_rfl hs).2 ⟨hdu.continuousOn, fun x y ↦ ?_⟩
    have huc : ContinuousOn (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)) :=
      (chartAt ℂ x).continuousOn_comp_comp_symm
        (((chartAt H y).continuousOn_extend (I := I)).mono (chartAt H y).extend_source.ge)
        hdu.continuousOn
    have hweak := hdu.hasWeakFDerivOn_chart (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y)
    rw [ht x, hs' x] at hweak
    exact memWkpLoc_succ_iff.2 ⟨huc.memLpLoc, _, hweak, memWkpLoc_zero_iff.2 (hLp x y)⟩

end BoundarylessSurface

/-! ### Riemann surfaces with boundary -/

section BorderedSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)}
  {s : Set X}

/-- Chart independence of `HasWeakMFDerivOnBordered` on a Riemann surface with boundary: covering
subfamilies of bordered holomorphic charts of `X` and smooth charts of a boundaryless target `M`
suffice. -/
theorem hasWeakMFDerivOnBordered_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOnBordered I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
        (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas
    (StructureGroupoid.maximalAtlas_mono
      (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
        (contDiffGroupoid_le (by exact_mod_cast le_top))))
    hs hA hAs hB hBs

/-- Weak chain rule on a Riemann surface with boundary for postcomposition with a `C^n` (`1 ≤ n`)
map `f : M → N` from a boundaryless smooth manifold `M`. -/
theorem HasWeakMFDerivOnBordered.contMDiffOn_comp [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : HasWeakMFDerivOnBordered I u du s) (hf : ContMDiffOn I I' n f t) (hn : 1 ≤ n)
    (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    HasWeakMFDerivOnBordered I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) s :=
  HasWeakMFDerivOnGroupoid.contMDiffOn_comp hu hf hn hs ht hst

/-- Global weak chain rule on a Riemann surface with boundary. -/
theorem _root_.ContMDiff.comp_hasWeakMFDerivBordered [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hu : HasWeakMFDerivBordered I u du) (hn : 1 ≤ n) :
    HasWeakMFDerivBordered I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) :=
  hf.comp_hasWeakMFDerivGroupoid hu hn

/-- **Existence of a global weak differential on a Riemann surface with boundary.** On a Lindelöf
bordered Riemann surface `X` and an open set `s ⊆ X`, every map satisfying
`MemWkpLocMapOnBordered I p 1 u s` into a boundaryless smooth manifold `M` admits a weak
differential `du` on `s` (whose coordinate
expressions also satisfy `MemLpLoc p` up to `∂X` by `HasWeakMFDerivOnGroupoid.memLpLoc_chart`). -/
theorem MemWkpLocMapOnBordered.exists_hasWeakMFDerivOnBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless] [CompleteSpace F]
    (hu : MemWkpLocMapOnBordered I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnBordered I u du s :=
  MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    (StructureGroupoid.maximalAtlas_mono
      (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
        (contDiffGroupoid_le (by exact_mod_cast le_top)))) hu hs

/-- **Global existence of a weak differential on a Riemann surface with boundary.** -/
theorem MemWkpLocMapBordered.exists_hasWeakMFDerivBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless] [CompleteSpace F]
    (hu : MemWkpLocMapBordered I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivBordered I u du :=
  MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    (StructureGroupoid.maximalAtlas_mono
      (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
        (contDiffGroupoid_le (by exact_mod_cast le_top)))) hu

end BorderedSurface

end TauCeti
