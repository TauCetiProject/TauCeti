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
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas

/-!
# Chart independence, chain rules, and existence of the weak differential

Building on `TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Basic`, this file proves the
chart calculus and global existence theorems for weak differentials of local Sobolev maps
`u : X → M` from a Riemann surface (with or without boundary) into a smooth manifold `M`:

* **Chart independence** (`TauCeti.hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas`,
  `TauCeti.hasWeakMFDerivOnGroupoid_iff_atlas`, `TauCeti.hasWeakMFDerivOnGroupoid_iff_chartAt`,
  and their boundaryless and bordered specializations): when `M` is boundaryless, testing weak
  derivatives in any covering subfamilies of the source and target maximal atlases—in particular in
  `atlas` or `chartAt`—suffices, including on bordered Riemann surfaces.
* **Weak chain rules** (`TauCeti.HasWeakMFDerivOnGroupoid.contMDiffOn_comp`,
  `ContMDiff.comp_hasWeakMFDerivGroupoid`,
  `Diffeomorph.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff`,
  `Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff`,
  `Diffeomorph.hasWeakMFDerivOn_comp_diffeomorph_iff`,
  `Diffeomorph.hasWeakMFDerivOnBordered_comp_diffeomorph_iff`): postcomposing with a `C¹` map
  `f : M → N` from a boundaryless smooth manifold `M` into a (possibly cornered) manifold `N`
  composes the weak differential with `mfderiv I I' f (u x)` (and gives an equivalence for target
  diffeomorphisms), while precomposing with a biholomorphism pulls the weak differential back along
  `mfderiv`. Because `HasWeakMFDerivOn` and `HasWeakMFDerivOnBordered` are `abbrev`s of
  `HasWeakMFDerivOnGroupoid`, the target postcomposition rules apply to both directly.
* **Global existence and first-order Sobolev characterization**
  (`TauCeti.MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid`,
  `TauCeti.MemWkpLocMapOn.exists_hasWeakMFDerivOn`,
  `TauCeti.MemWkpLocMapOnBordered.exists_hasWeakMFDerivOnBordered`,
  `TauCeti.memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid`,
  `TauCeti.memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn`,
  `TauCeti.memWkpLocMapOnBordered_one_iff_exists_hasWeakMFDerivOnBordered`): on a Lindelöf surface
  `X` (with or without boundary), every local Sobolev map of order `1` into a boundaryless smooth
  manifold `M` admits a global weak differential `du`, constructed locally in preferred chart pairs
  and glued on a countable subcover using almost-everywhere uniqueness.

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

omit [ChartedSpace H' X] in
/-- When `(φ.extend J).target` is a neighborhood of `z` and `U` is a neighborhood of
`(φ.extend J).symm z`, `z` lies in the interior of `(φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U`.
-/
private theorem mem_interior_extend_target_inter_preimage'
    {φ : OpenPartialHomeomorph X H'} {U : Set X} {z : ℂ}
    (hzt : (φ.extend J).target ∈ 𝓝 z) (hU : U ∈ 𝓝 ((φ.extend J).symm z)) :
    z ∈ interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U) :=
  mem_interior_iff_mem_nhds.2
    (inter_mem hzt ((φ.continuousOn_extend_symm.continuousAt hzt).preimage_mem_nhds hU))

omit [ChartedSpace H' X] [ChartedSpace H M] in
/-- If `u` is continuous on an open set `s`, then `s ∩ (U ∩ u ⁻¹' V)` is open for open `U` and `V`.
-/
private theorem isOpen_inter_inter_preimage {u : X → M} {s U : Set X} {V : Set M}
    (hc : ContinuousOn u s) (hs : IsOpen s) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (s ∩ (U ∩ u ⁻¹' V)) := by
  have hset : (s ∩ U) ∩ (s ∩ u ⁻¹' V) = s ∩ (U ∩ u ⁻¹' V) := by
    ext x; simp only [mem_inter_iff]; tauto
  exact hset ▸ (hs.inter hU).inter (hc.isOpen_inter_preimage hs hV)

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
  have hsrc : (W : Set ℂ) ⊆ (J.extendCoordChange φ' φ).source := by
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      φ.extend_source]
    exact hW.trans interior_subset
  have hΦ : ContDiffOn ℝ 1 (φ.extend J ∘ (φ'.extend J).symm) W :=
    (J.contDiffOn_extendCoordChange hφ' hφ).mono hsrc
  have hinj : InjOn (φ.extend J ∘ (φ'.extend J).symm) W :=
    (J.extendCoordChange φ' φ).injOn.mono hsrc
  have hdet : ∀ w ∈ (W : Set ℂ), (fderiv ℝ (φ.extend J ∘ (φ'.extend J).symm) w).det ≠ 0 :=
    fun w hw ↦ J.det_fderiv_extendCoordChange_ne_zero one_ne_zero hφ' hφ (hW hw)
  refine ((hU.comp_contDiffOn_diffeo hΦ hinj hdet hmaps).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    simp only [Function.comp_apply, φ.extend_left_inv (interior_subset (hW hw)).2]
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
  have hzt : (φ'.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  have hzW : z ∈ W := mem_interior_extend_target_inter_preimage' hzt
    (((hc.isOpen_inter_preimage hs ψ.open_source).inter φ.open_source).mem_nhds
      ⟨(interior_subset hz).2, hxφ⟩)
  refine ⟨W, hzW, hasWeakFDerivOn_comp_chart_transition (hAJ hφA) hφ' ψ
    (hAψ φ hφA) (interior_mono (inter_subset_inter_right _
      (preimage_mono inter_subset_right))) fun w hw ↦ ?_⟩
  have hwt : w ∈ (φ'.extend J).target := (interior_subset hw).1
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source := by
    rw [← φ'.extend_source (I := J)]; exact (φ'.extend J).map_target hwt
  have hint := ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero
    hφ' (hAJ hφA) hxφ' (interior_subset hw).2.2
    (by rw [(φ'.extend J).right_inv hwt]; exact interior_mono inter_subset_left hw)
  exact mem_interior_extend_target_inter_preimage' (mem_interior_iff_mem_nhds.1 hint)
    (by
      rw [Function.comp_apply, φ.extend_left_inv (interior_subset hw).2.2]
      exact (hc.isOpen_inter_preimage hs ψ.open_source).mem_nhds (interior_subset hw).2.1)

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
  have hψ'1 : ψ' ∈ IsManifold.maximalAtlas I' 1 N :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by exact_mod_cast le_top)) hψ'
  have hψ1 : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by exact_mod_cast le_top)) hψ
  have hg : ContDiffOn ℝ 1 g O := contMDiffOn_iff_contDiffOn.1
    ((ψ'.contMDiffOn_extend hψ'1).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hw ↦ hw.2.1) fun _ hw ↦ hw.2.2)
  have hmaps' : MapsTo (ψ.extend I ∘ u ∘ (φ.extend J).symm) W O := fun w hw ↦ by
    have hsrc : u ((φ.extend J).symm w) ∈ (ψ.extend I).source := by
      rw [ψ.extend_source]; exact (hmaps hw).1
    exact ⟨(ψ.extend I).map_source hsrc, by
      rw [mem_preimage, Function.comp_apply, Function.comp_apply, (ψ.extend I).left_inv hsrc]
      exact (hmaps hw).2⟩
  refine ((hW.contDiffOn_comp huc hO hg hmaps').congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    have hxψ : u ((φ.extend J).symm w) ∈ ψ.source := (hmaps hw).1
    simp only [g, Function.comp_apply, ψ.extend_left_inv hxψ]
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    exact fderiv_extend_comp_chartTangentHom hψ1 hψ'1 hf ht du (hmaps hw)

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
  -- First change source charts from `A` to `φ'` at a fixed target chart `ψ ∈ B`.
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ (interior_subset hz).2.1
  have h1 := hasWeakFDerivOn_change_source_chart hc hs (hA.trans hG) hAs (hG hφ') ψ
    fun φ hφ ↦ h φ hφ ψ hψB
  -- Then pass from `ψ` to `ψ'` via the planar weak chain rule applied to `id : M → M`.
  set W := Opens.interior ((φ'.extend J).target ∩
    (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source)))
  have hzt : (φ'.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  have hzW : z ∈ W := mem_interior_extend_target_inter_preimage' hzt
    ((hc.isOpen_inter_preimage hs (ψ.open_source.inter ψ'.open_source)).mem_nhds
      ⟨(interior_subset hz).2.1, hxψ, (interior_subset hz).2.2⟩)
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

/-- Global chart independence of `HasWeakMFDerivGroupoid` for covering subfamilies of the maximal
atlases. -/
theorem hasWeakMFDerivGroupoid_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {A : Set (OpenPartialHomeomorph X H')} (hA : A ⊆ G.maximalAtlas X)
    (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG
    isOpen_univ hA (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence at groupoid generality: testing the given atlases `atlas H' X` and
`atlas H M` suffices (without assuming `[CompleteSpace F]` upfront). -/
theorem hasWeakMFDerivOnGroupoid_iff_atlas [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {s : Set X} (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas H' X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun φ hφ ψ hψ ↦ h.hasWeakFDerivOn_chart
      (StructureGroupoid.subset_maximalAtlas G hφ) (IsManifold.subset_maximalAtlas hψ)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩⟩
  have : CompleteSpace F :=
    (h _ (chart_mem_atlas H' (φ'.symm (J.symm 0)))
      _ (chart_mem_atlas H (ψ'.symm (I.symm 0)))).completeSpace
  exact ((hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG hs
    (StructureGroupoid.subset_maximalAtlas G) (fun x _ ↦ ⟨_, chart_mem_atlas H' x,
      mem_chart_source H' x⟩)
    IsManifold.subset_maximalAtlas (fun x _ ↦ ⟨_, chart_mem_atlas H (u x),
      mem_chart_source H (u x)⟩)).2 ⟨hc, h⟩).hasWeakFDerivOn_chart hφ' hψ'

/-- Global chart independence at groupoid generality: testing `atlas H' X` and `atlas H M`
suffices. -/
theorem hasWeakMFDerivGroupoid_iff_atlas [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ φ ∈ atlas H' X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_atlas hG isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence at groupoid generality: testing preferred charts `chartAt H' x` and
`chartAt H y` suffices (without assuming `[CompleteSpace F]` upfront). -/
theorem hasWeakMFDerivOnGroupoid_iff_chartAt [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {s : Set X} (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior ((extChartAt J x).target ∩
          (extChartAt J x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt J x).symm)
        (chartTangentHom J I (chartAt H' x) (chartAt H y) u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun x y ↦ h.hasWeakFDerivOn_chart
      (StructureGroupoid.chart_mem_maximalAtlas G x) (IsManifold.chart_mem_maximalAtlas y)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩⟩
  have : CompleteSpace F := (h (φ'.symm (J.symm 0)) (ψ'.symm (I.symm 0))).completeSpace
  refine ((hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG hs
    (A := range (chartAt H')) (range_subset_iff.2 (StructureGroupoid.chart_mem_maximalAtlas G))
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source H' x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩)).2
      ⟨hc, ?_⟩).hasWeakFDerivOn_chart hφ' hψ'
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact h x y

/-- Global chart independence at groupoid generality: testing preferred charts `chartAt H' x` and
`chartAt H y` suffices. -/
theorem hasWeakMFDerivGroupoid_iff_chartAt [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior ((extChartAt J x).target ∩
          (extChartAt J x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt J x).symm)
        (chartTangentHom J I (chartAt H' x) (chartAt H y) u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_chartAt hG isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

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
  have hzt : (φ.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  have hopen : IsOpen (s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source)) := by
    have hset : (s ∩ u ⁻¹' (chartAt H y₀).source) ∩ (s ∩ (f ∘ u) ⁻¹' ψ'.source) =
        s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source) := by
      ext x; simp only [mem_inter_iff]; tauto
    exact hset ▸ (hu.continuousOn.isOpen_inter_preimage hs (chartAt H y₀).open_source).inter
      (hc.isOpen_inter_preimage hs ψ'.open_source)
  have hzW : z ∈ W := mem_interior_extend_target_inter_preimage' hzt
    (hopen.mem_nhds ⟨(interior_subset hz).2.1, mem_chart_source H y₀, (interior_subset hz).2.2⟩)
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

/-- Postcomposing `u : X → M` with a `C^n` (`1 ≤ n`) diffeomorphism `e : M ≃ₘ^n⟮I, I'⟯ N` of
boundaryless smooth targets transforms weak differentials on `s` by `mfderiv I I' e`. Because
`HasWeakMFDerivOn` and `HasWeakMFDerivOnBordered` are `abbrev`s of `HasWeakMFDerivOnGroupoid`, this
applies to both directly. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : 1 ≤ n)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)}
    {s : Set X} (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I' (e ∘ u) (fun x ↦ (mfderiv I I' e (u x)).comp (du x)) s ↔
      HasWeakMFDerivOnGroupoid G J I u du s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp e.contMDiff.contMDiffOn hn hs isOpen_univ
    (mapsTo_univ _ _)⟩
  have hn0 : n ≠ 0 := by intro h0; rw [h0] at hn; exact not_le_of_gt zero_lt_one hn
  refine (h.contMDiffOn_comp e.symm.contMDiff.contMDiffOn hn hs isOpen_univ
    (mapsTo_univ _ _)).congr (fun x _ ↦ e.symm_apply_apply (u x)) fun x _ ↦ ?_
  have hcomp :
      (mfderiv I' I e.symm ((e ∘ u) x)).comp ((mfderiv I I' e (u x)).comp (du x)) =
        (mfderiv I I ((e.symm : N → M) ∘ e) (u x)).comp (du x) := by
    ext v
    exact (mfderiv_comp_apply (u x) (e.symm.mdifferentiable hn0 (e (u x)))
      (e.mdifferentiable hn0 (u x)) (du x v)).symm
  rw [hcomp]
  have hid : ∀ (g : M → M), g = id →
      (tangentSpaceCast I (g (u x)) (u x)).toContinuousLinearMap.comp
        ((mfderiv I I g (u x)).comp (du x)) = du x := by
    rintro _ rfl
    -- `tangentSpaceCast` between equal basepoints is definitionally the identity.
    have hcast : (tangentSpaceCast I (u x) (u x)).toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext; rfl
    rw [id_eq, hcast, mfderiv_id, ContinuousLinearMap.id_comp, ContinuousLinearMap.id_comp]
  exact hid ((e.symm : N → M) ∘ e) (funext e.symm_apply_apply)

/-- Global target-diffeomorphism equivalence for `HasWeakMFDerivGroupoid`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivGroupoid_diffeomorph_comp_iff
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : 1 ≤ n)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivGroupoid G J I' (e ∘ u) (fun x ↦ (mfderiv I I' e (u x)).comp (du x)) ↔
      HasWeakMFDerivGroupoid G J I u du := by
  rw [← hasWeakMFDerivOnGroupoid_univ, ← hasWeakMFDerivOnGroupoid_univ]
  exact e.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff hn isOpen_univ

/-- Precomposing `u : X → M` with a `C^n` (`1 ≤ n`) diffeomorphism `e : Y ≃ₘ^n⟮J, J⟯ X` whose
inverse transports `G'`-charts of `Y` into `G`-charts of `X` pulls a weak differential `du` on `s`
back to `y ↦ (du (e y)).comp (mfderiv J J e y)` on `e ⁻¹' s`. Both `X` and `Y` may have boundary. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] {G' : StructureGroupoid H'}
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y)
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s : Set X}
    (hu : HasWeakMFDerivOnGroupoid G J I u du s) :
    HasWeakMFDerivOnGroupoid G' J I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv J J e y)) (e ⁻¹' s) := by
  have hn0 : n ≠ 0 := by intro h0; rw [h0] at hn; exact not_le_of_gt zero_lt_one hn
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨hu.continuousOn.comp e.continuous.continuousOn (mapsTo_preimage e s), fun φ hφ ψ hψ ↦ ?_⟩
  set φ' : OpenPartialHomeomorph X H' := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ
  have hφ' : φ' ∈ G.maximalAtlas X := he φ hφ
  have hchart := hu.hasWeakFDerivOn_chart hφ' hψ
  have ht' : (φ'.extend J).target = (φ.extend J).target := by
    simp [φ', mfld_simps]
  have hs' : ⇑(φ'.extend J).symm = e ∘ ⇑(φ.extend J).symm := by
    ext w; simp [φ', mfld_simps]
  have hdom : Opens.interior ((φ'.extend J).target ∩
      (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) =
    Opens.interior ((φ.extend J).target ∩
      (φ.extend J).symm ⁻¹' (e ⁻¹' s ∩ (u ∘ e) ⁻¹' ψ.source)) := by
    simp only [ht', hs', preimage_comp, preimage_inter]
  rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards with z
    simp only [Function.comp_apply, congr_fun hs' z]
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    have hzint : z ∈ interior (φ.extend J).target := interior_mono inter_subset_left hz
    have hzR : range J ∈ 𝓝 z :=
      mem_of_superset (mem_interior_iff_mem_nhds.1 hzint) φ.extend_target_subset_range
    have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ.extend J).symm (φ.extend J).target := by
      rw [φ.extend_target']; exact contMDiffOn_extend_symm (hG' hφ)
    have hdφ : MDifferentiableAt 𝓘(ℝ, ℂ) J (φ.extend J).symm z :=
      ((hsymm z (interior_subset hzint)).contMDiffAt
        (mem_interior_iff_mem_nhds.1 hzint)).mdifferentiableAt one_ne_zero
    rw [chartTangentHom_apply, chartTangentHom_apply, mfderivWithin_of_mem_nhds hzR,
      mfderivWithin_of_mem_nhds hzR]
    have hgen : ∀ (g : ℂ → X), g = e ∘ ⇑(φ.extend J).symm →
        mvfderiv I (ψ.extend I) (u (g z)) ∘L du (g z) ∘L
          (mfderiv 𝓘(ℝ, ℂ) J g z ∘L
            (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) =
        mvfderiv I (ψ.extend I) ((u ∘ e) ((φ.extend J).symm z)) ∘L
          ((du (e ((φ.extend J).symm z))).comp (mfderiv J J e ((φ.extend J).symm z))) ∘L
            (mfderiv 𝓘(ℝ, ℂ) J (φ.extend J).symm z ∘L
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) := by
      rintro _ rfl
      simp only [Function.comp_apply, mfderiv_comp z (e.mdifferentiable hn0 _) hdφ,
        ContinuousLinearMap.comp_assoc]
    exact hgen _ hs'

/-- Equivalence of weak differentials under precomposition with a `C^n` (`1 ≤ n`) diffeomorphism
`e : Y ≃ₘ^n⟮J, J⟯ X` preserving the maximal atlases of `G` and `G'`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] {G' : StructureGroupoid H'}
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y)
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    (hesymm : ∀ φ ∈ G.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G'.maximalAtlas Y)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s : Set X} :
    HasWeakMFDerivOnGroupoid G' J I (u ∘ e)
        (fun y ↦ (du (e y)).comp (mfderiv J J e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOnGroupoid G J I u du s := by
  refine ⟨fun h ↦ ?_, e.hasWeakMFDerivOnGroupoid_comp_diffeomorph hG' hn he⟩
  have hn0 : n ≠ 0 := by intro h0; rw [h0] at hn; exact not_le_of_gt zero_lt_one hn
  have hback := e.symm.hasWeakMFDerivOnGroupoid_comp_diffeomorph hG hn hesymm h
  have hpre : e.symm ⁻¹' (e ⁻¹' s) = s := by ext x; simp
  rw [hpre] at hback
  refine hback.congr (fun x _ ↦ congrArg u (e.apply_symm_apply x)) fun x _ ↦ ?_
  have hcomp :
      ((du (e (e.symm x))).comp (mfderiv J J e (e.symm x))).comp (mfderiv J J e.symm x) =
        (du (((e : Y → X) ∘ e.symm) x)).comp (mfderiv J J ((e : Y → X) ∘ e.symm) x) := by
    ext v
    exact congrArg (du (e (e.symm x)))
      (mfderiv_comp_apply x (e.mdifferentiable hn0 (e.symm x))
        (e.symm.mdifferentiable hn0 x) v).symm
  rw [hcomp]
  have hid : ∀ (g : X → X), g = id →
      (tangentSpaceCast I (u (g x)) (u x)).toContinuousLinearMap.comp
        ((du (g x)).comp (mfderiv J J g x)) = du x := by
    rintro _ rfl
    -- `tangentSpaceCast` between equal basepoints is definitionally the identity.
    have hcast : (tangentSpaceCast I (u x) (u x)).toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext; rfl
    rw [id_eq, hcast, mfderiv_id, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  exact hid ((e : Y → X) ∘ e.symm) (funext e.apply_symm_apply)

/-- Global source-diffeomorphism equivalence for `HasWeakMFDerivGroupoid`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivGroupoid_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] {G' : StructureGroupoid H'}
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y)
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    (hesymm : ∀ φ ∈ G.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G'.maximalAtlas Y)
    {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivGroupoid G' J I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv J J e y)) ↔
      HasWeakMFDerivGroupoid G J I u du := by
  rw [← hasWeakMFDerivOnGroupoid_univ, ← hasWeakMFDerivOnGroupoid_univ,
    ← preimage_univ (f := e)]
  exact e.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff hG hG' hn he hesymm

/-! ### Existence of a global weak differential -/

/-- Pulling a planar derivative field `D : ℂ → ℂ →L[ℝ] F` in preferred charts `(x₀, y₀)` back to a
family of tangent-space maps `du : ∀ x, TangentSpace J x →L[ℝ] TangentSpace I (u x)` via the total
vector-bundle trivialization maps `continuousLinearMapAt` and `symmL`. -/
private def pullbackChartDeriv [IsManifold J 1 X] [IsManifold I 1 M]
    (u : X → M) (x₀ : X) (y₀ : M) (D : ℂ → ℂ →L[ℝ] F) (x : X) :
    TangentSpace J x →L[ℝ] TangentSpace I (u x) :=
  (trivializationAt F (TangentSpace I) y₀).symmL ℝ (u x) ∘L
    D (extChartAt J x₀ x) ∘L
    (trivializationAt ℂ (TangentSpace J) x₀).continuousLinearMapAt ℝ x

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
  ext v
  simp only [ContinuousLinearMap.inCoordinates, pullbackChartDeriv, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_symmL _ hx',
    Trivialization.continuousLinearMapAt_symmL _ hy']

/-- Existence of a weak differential on a single chart-pair neighborhood
`s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)`. -/
private theorem exists_local_hasWeakMFDerivOnGroupoid
    [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} {s : Set X}
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) (x₀ : X) :
    ∃ d : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u d
        (s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  let U₀ := s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)
  have hUo : IsOpen U₀ := isOpen_inter_inter_preimage hu.continuousOn hs
    (chartAt H' x₀).open_source (chartAt H (u x₀)).open_source
  obtain ⟨D, hD, -⟩ := (hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas (u x₀))).exists_weakFDeriv
  have : CompleteSpace F := hD.completeSpace
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

omit [ChartedSpace H' X] in
/-- Extracting an `ℕ`-indexed subcover of a nonempty set `s` in a second-countable space from a
family `U : X → Set X` of open subsets of `s` with `x ∈ U x` for every `x ∈ s`. -/
private theorem exists_nat_subcover [SecondCountableTopology X] {s : Set X} (hne : s.Nonempty)
    {U : X → Set X} (hUo : ∀ x₀, IsOpen (U x₀)) (hUmem : ∀ x ∈ s, x ∈ U x)
    (hUsub : ∀ x₀, U x₀ ⊆ s) :
    ∃ c : ℕ → X, s = ⋃ n : ℕ, U (c n) := by
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable (fun i : s ↦ U i.1) (fun i ↦ hUo i.1)
  have hTs : s = ⋃ i ∈ T, U i.1 := Subset.antisymm
    (fun x hxs ↦ hTcov.symm ▸ mem_iUnion.2 ⟨⟨x, hxs⟩, hUmem x hxs⟩)
    (iUnion₂_subset fun _ _ ↦ hUsub _)
  obtain ⟨x₁, hx₁s⟩ := hne
  rcases mem_iUnion₂.1 (hTs ▸ hx₁s) with ⟨i₀, hi₀T, -⟩
  have : Nonempty T := ⟨⟨i₀, hi₀T⟩⟩
  have : Countable T := hTcnt.to_subtype
  obtain ⟨q, hqsurj⟩ := exists_surjective_nat T
  refine ⟨fun n ↦ (q n).1.1, ?_⟩
  ext x; rw [Set.ext_iff.1 hTs x]; simp only [mem_iUnion, exists_prop]
  exact ⟨fun ⟨i, hiT, hx⟩ ↦ let ⟨n, hn⟩ := hqsurj ⟨i, hiT⟩; ⟨n, by simpa [hn] using hx⟩,
    fun ⟨n, hx⟩ ↦ ⟨(q n).1, (q n).2, hx⟩⟩

/-- Gluing local weak differentials along a countable open cover `⋃ n : ℕ, V n` via `Nat.find`
and almost-everywhere uniqueness on pairwise overlaps. -/
private theorem exists_hasWeakMFDerivOnGroupoid_iUnion_nat
    [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {u : X → M} {V : ℕ → Set X} (hVo : ∀ n, IsOpen (V n))
    (hV : ∀ n, ∃ d : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u d (V n)) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u du (⋃ n : ℕ, V n) := by
  choose d hd using hV
  classical
  let du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x) := fun x ↦
    if h : ∃ n : ℕ, x ∈ V n then d (Nat.find h) x else 0
  refine ⟨du, (hasWeakMFDerivOnGroupoid_iUnion_iff hVo).2 fun n ↦
    (hd n).congr_deriv_of_isNullSet hG ?_⟩
  refine (IsNullSet.iUnion fun k : ℕ ↦ ((hd n).mono inter_subset_left).isNullSet_ne
    ((hVo n).inter (hVo k)) ((hd k).mono inter_subset_right)).mono fun x ⟨hxn, hxne⟩ ↦ ?_
  have hex : ∃ k : ℕ, x ∈ V k := ⟨n, hxn⟩
  refine mem_iUnion.2 ⟨Nat.find hex, ⟨hxn, Nat.find_spec hex⟩, fun heq ↦ hxne ?_⟩
  simp only [du, hex, ↓reduceDIte, heq]

/-- **Existence of a global weak differential.** On a Lindelöf surface `X` (with or without
boundary) and an open set `s ⊆ X`, every local Sobolev map `u : X → M` of order `1` into a
boundaryless smooth manifold `M` admits a weak differential `du` on `s`. -/
theorem MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} {s : Set X}
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u du s := by
  -- Handle empty `X` or `s`, then extract `CompleteSpace F` from `hu` on a nonempty chart pair.
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ ↦ 0, hasWeakMFDerivOnGroupoid_iff.2
      ⟨fun x _ ↦ (IsEmpty.false x).elim, fun φ _ _ _ ↦ (IsEmpty.false (φ.symm (J.symm 0))).elim⟩⟩
  have : CompleteSpace F :=
    (hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
      (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ 0, hasWeakMFDerivOnGroupoid_empty⟩
  -- Cover `s` by countably many preferred-chart neighborhoods and glue local weak differentials.
  have : SecondCountableTopology H' := J.secondCountableTopology
  have : SecondCountableTopology X := ChartedSpace.secondCountable_of_lindelof H' X
  let U : X → Set X := fun x₁ ↦
    s ∩ ((chartAt H' x₁).source ∩ u ⁻¹' (chartAt H (u x₁)).source)
  have hUo : ∀ x₁, IsOpen (U x₁) := fun x₁ ↦
    isOpen_inter_inter_preimage hu.continuousOn hs (chartAt H' x₁).open_source
      (chartAt H (u x₁)).open_source
  obtain ⟨c, hcov⟩ := exists_nat_subcover hne hUo
    (fun x hxs ↦ ⟨hxs, mem_chart_source H' x, mem_chart_source H (u x)⟩)
    (fun _ ↦ inter_subset_left)
  rw [hcov]
  exact exists_hasWeakMFDerivOnGroupoid_iUnion_nat hG (fun n ↦ hUo (c n))
    fun n ↦ exists_local_hasWeakMFDerivOnGroupoid hG hu hs (c n)

/-- Global existence of a weak differential for a structure groupoid `G`. -/
theorem MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} (hu : MemWkpLocMapGroupoid G J I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivGroupoid G J I u du := by
  obtain ⟨du, hdu⟩ :=
    (memWkpLocMapOnGroupoid_univ.2 hu).exists_hasWeakMFDerivOnGroupoid hG isOpen_univ
  exact ⟨du, hasWeakMFDerivOnGroupoid_univ.1 hdu⟩

/-- **First-order Sobolev characterization at groupoid generality.** On a Lindelöf surface `X`
(with or without boundary) and an open set `s ⊆ X`, a map `u : X → M` into a boundaryless smooth
manifold belongs to `MemWkpLocMapOnGroupoid G J I p 1 u s` if and only if it admits a weak
differential `du` on `s` whose coordinate expressions `chartTangentHom` belong to `MemLpLoc p` up
to the boundary of `J`. -/
theorem memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} {s : Set X} (hs : IsOpen s) :
    MemWkpLocMapOnGroupoid G J I p 1 u s ↔
      ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivOnGroupoid G J I u du s ∧
          ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
            MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
              (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun hu ↦ ?_, fun ⟨du, hdu, hLp⟩ ↦ (hdu.memWkpLocMapOnGroupoid_one_iff hs).2 hLp⟩
  obtain ⟨du, hdu⟩ := hu.exists_hasWeakMFDerivOnGroupoid hG hs
  exact ⟨du, hdu, (hdu.memWkpLocMapOnGroupoid_one_iff hs).1 hu⟩

/-- Global first-order Sobolev characterization at groupoid generality. -/
theorem memWkpLocMapGroupoid_one_iff_exists_hasWeakMFDerivGroupoid
    [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    {p : ENNReal} {u : X → M} :
    MemWkpLocMapGroupoid G J I p 1 u ↔
      ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivGroupoid G J I u du ∧
          ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
            MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source))
              (chartTangentHom J I φ ψ u du) := by
  rw [← memWkpLocMapOnGroupoid_univ,
    memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid hG isOpen_univ]
  simp only [hasWeakMFDerivOnGroupoid_univ, univ_inter]

end Transitions

/-! ### Riemann surfaces without boundary -/

section BoundarylessSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {s : Set X}

omit [ChartedSpace ℂ X] in
private theorem extend_modelWithCornersSelf_target (φ : OpenPartialHomeomorph X ℂ) :
    (φ.extend 𝓘(ℝ, ℂ)).target = φ.target := by
  simp [mfld_simps]

omit [ChartedSpace ℂ X] in
private theorem extend_modelWithCornersSelf_symm (φ : OpenPartialHomeomorph X ℂ) :
    ⇑(φ.extend 𝓘(ℝ, ℂ)).symm = ⇑φ.symm := by
  ext z; simp [mfld_simps]

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
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs hA hAs hB hBs]
  simp only [extend_modelWithCornersSelf_target, extend_modelWithCornersSelf_symm]

/-- Global chart independence for covering subfamilies on a Riemann surface without boundary. -/
theorem hasWeakMFDeriv_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_of_subset_maximalAtlas isOpen_univ hA (fun x _ ↦ hAs x) hB
      (fun x _ ↦ hBs x)).trans ?_)
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDerivOn_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_atlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs]
  simp only [extend_modelWithCornersSelf_target, extend_modelWithCornersSelf_symm]

/-- Global chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_atlas isOpen_univ).trans ?_)
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: testing the preferred charts `chartAt ℂ x` and `chartAt H y` suffices. -/
theorem hasWeakMFDerivOn_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_chartAt
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs]
  simp only [extChartAt, extend_modelWithCornersSelf_target, extend_modelWithCornersSelf_symm]

/-- Global chart independence: testing the preferred charts of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_chartAt isOpen_univ).trans ?_)
  simp only [continuousOn_univ, univ_inter]

/-- On `ℂ` and a normed space `F`, `HasWeakMFDerivOn 𝓘(ℝ, F)` on an open set `Ω ⊆ ℂ` is equivalent
to continuity on `Ω` together with `HasWeakFDerivOn volume Ω u` for the transported derivative
field. -/
theorem hasWeakMFDerivOn_model_iff {u : ℂ → F}
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
          du z ∘L (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap := by
    intro x y; rw [chartAt_self_eq, chartAt_self_eq]; exact funext (chartTangentHom_refl du)
  refine and_congr_right fun _ ↦ ?_
  simp only [hdom, hextF, hch]
  exact ⟨fun h ↦ h 0 (u 0), fun h _ _ ↦ h⟩

/-- Precomposing `u : X → M` with a biholomorphism `e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X` (`1 ≤ n`) pulls a
weak differential `du` on `s` back to `y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)` on
`e ⁻¹' s`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOn_comp_diffeomorph
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n)
    (hu : HasWeakMFDerivOn I u du s) :
    HasWeakMFDerivOn I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) (e ⁻¹' s) := by
  let eR : Y ≃ₘ^1⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ X :=
    ⟨e.toEquiv,
      by have h := (e.contMDiff.of_le hn).restrictScalars ℝ
         rwa [modelWithCornersSelf_restrictScalars] at h,
      by have h := (e.symm.contMDiff.of_le hn).restrictScalars ℝ
         rwa [modelWithCornersSelf_restrictScalars] at h⟩
  refine eR.hasWeakMFDerivOnGroupoid_comp_diffeomorph
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) le_rfl
    (fun φ hφ ↦ ?_) hu
  have heq : eR.symm.toHomeomorph.toOpenPartialHomeomorph =
      (e.symm.toPartialDiffeomorph.ofLE hn).toOpenPartialHomeomorph :=
    OpenPartialHomeomorph.toPartialEquiv_injective
      ((e.symm.toPartialDiffeomorph.ofLE_toPartialEquiv hn).trans
        e.symm.toPartialDiffeomorph_toPartialEquiv).symm
  rw [heq]
  exact (e.symm.toPartialDiffeomorph.ofLE hn).trans_mem_maximalAtlas hφ

/-- Global precomposition of a weak differential with a biholomorphism
`e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X`. -/
theorem _root_.Diffeomorph.hasWeakMFDeriv_comp_diffeomorph
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n)
    (hu : HasWeakMFDeriv I u du) :
    HasWeakMFDeriv I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) :=
  hasWeakMFDerivOnGroupoid_univ.1
    (by simpa only [preimage_univ] using
      e.hasWeakMFDerivOn_comp_diffeomorph hn (hasWeakMFDerivOnGroupoid_univ.2 hu))

/-- Equivalence of weak differentials under precomposition with a biholomorphism
`e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X` (`1 ≤ n`) between Riemann surfaces without boundary. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOn_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    HasWeakMFDerivOn I (u ∘ e)
        (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOn I u du s := by
  let eR : Y ≃ₘ^1⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ X :=
    ⟨e.toEquiv,
      by have h := (e.contMDiff.of_le hn).restrictScalars ℝ
         rwa [modelWithCornersSelf_restrictScalars] at h,
      by have h := (e.symm.contMDiff.of_le hn).restrictScalars ℝ
         rwa [modelWithCornersSelf_restrictScalars] at h⟩
  refine eR.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero)
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero)
    le_rfl (fun φ hφ ↦ ?_) (fun φ hφ ↦ ?_)
  · have heq : eR.symm.toHomeomorph.toOpenPartialHomeomorph =
        (e.symm.toPartialDiffeomorph.ofLE hn).toOpenPartialHomeomorph :=
      OpenPartialHomeomorph.toPartialEquiv_injective
        ((e.symm.toPartialDiffeomorph.ofLE_toPartialEquiv hn).trans
          e.symm.toPartialDiffeomorph_toPartialEquiv).symm
    rw [heq]
    exact (e.symm.toPartialDiffeomorph.ofLE hn).trans_mem_maximalAtlas hφ
  · have heq : eR.toHomeomorph.toOpenPartialHomeomorph =
        (e.toPartialDiffeomorph.ofLE hn).toOpenPartialHomeomorph :=
      OpenPartialHomeomorph.toPartialEquiv_injective
        ((e.toPartialDiffeomorph.ofLE_toPartialEquiv hn).trans
          e.toPartialDiffeomorph_toPartialEquiv).symm
    rw [heq]
    exact (e.toPartialDiffeomorph.ofLE hn).trans_mem_maximalAtlas hφ

/-- Global equivalence of weak differentials under precomposition with a biholomorphism
`e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X` (`1 ≤ n`). -/
theorem _root_.Diffeomorph.hasWeakMFDeriv_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    HasWeakMFDeriv I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) ↔
      HasWeakMFDeriv I u du := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    (Iff.trans ?_ hasWeakMFDerivOnGroupoid_univ)
  rw [← preimage_univ (f := e)]
  exact e.hasWeakMFDerivOn_comp_diffeomorph_iff hn

/-- **Existence of a weak differential on a Riemann surface without boundary.** On a Lindelöf
Riemann surface `X` and an open set `s ⊆ X`, every map `u ∈ MemWkpLocMapOn I p 1 u s` into a
boundaryless smooth manifold `M` has a weak differential on `s`. -/
theorem MemWkpLocMapOn.exists_hasWeakMFDerivOn
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOn I u du s := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hu hs

/-- **Global existence of a weak differential on a Riemann surface without boundary.** -/
theorem MemWkpLocMap.exists_hasWeakMFDeriv
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
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
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    (hs : IsOpen s) :
    MemWkpLocMapOn I p 1 u s ↔
      ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivOn I u du s ∧ ∀ x : X, ∀ y : M,
          MemLpLoc p
            ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
            (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  constructor
  · intro hu
    obtain ⟨du, hdu⟩ := MemWkpLocMapOn.exists_hasWeakMFDerivOn hu hs
    refine ⟨du, hdu, fun x y ↦ ?_⟩
    have hLp := hdu.memLpLoc_chartTangentHom hu hs
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y)
    rwa [extend_modelWithCornersSelf_target, extend_modelWithCornersSelf_symm] at hLp
  · rintro ⟨du, hdu, hLp⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · exact memWkpLocMapOn_iff.2
        ⟨fun x _ ↦ (IsEmpty.false x).elim, fun φ _ _ _ ↦ (IsEmpty.false (φ.symm 0)).elim⟩
    have : CompleteSpace F :=
      (hdu.hasWeakFDerivOn_chart (IsManifold.chart_mem_maximalAtlas x₀)
        (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
    refine (memWkpLocMapOn_iff_chartAt le_rfl hs).2 ⟨hdu.continuousOn, fun x y ↦ ?_⟩
    have huc : ContinuousOn (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)) :=
      (chartAt ℂ x).continuousOn_comp_comp_symm
        (((chartAt H y).continuousOn_extend (I := I)).mono (chartAt H y).extend_source.ge)
        hdu.continuousOn
    have hweak := hdu.hasWeakFDerivOn_chart (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y)
    rw [extend_modelWithCornersSelf_target, extend_modelWithCornersSelf_symm] at hweak
    exact memWkpLoc_succ_iff.2 ⟨huc.memLpLoc, _, hweak, memWkpLoc_zero_iff.2 (hLp x y)⟩

/-- Global first-order Sobolev characterization via preferred charts on a Riemann surface without
boundary. -/
theorem memWkpLocMap_one_iff_exists_hasWeakMFDeriv
    [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless] :
    MemWkpLocMap I p 1 u ↔
      ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDeriv I u du ∧ ∀ x : X, ∀ y : M,
          MemLpLoc p
            ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
            (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  refine memWkpLocMapOnGroupoid_univ.symm.trans
    ((memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn isOpen_univ).trans ?_)
  simp only [hasWeakMFDerivOnGroupoid_univ, univ_inter]

end BoundarylessSurface

/-! ### Riemann surfaces with boundary -/

section BorderedSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)}
  {s : Set X}

private theorem borderedHolomorphicGroupoid_maximalAtlas_subset'
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ClosedUpperHalfPlane Y] :
    borderedHolomorphicGroupoid.maximalAtlas Y ⊆
      IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 Y :=
  StructureGroupoid.maximalAtlas_mono
    (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le (by exact_mod_cast le_top)))

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
    borderedHolomorphicGroupoid_maximalAtlas_subset' hs hA hAs hB hBs

/-- Global chart independence of `HasWeakMFDerivBordered` for covering subfamilies. -/
theorem hasWeakMFDerivBordered_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X)
    (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivBordered I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
        (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivGroupoid_iff_of_subset_maximalAtlas
    borderedHolomorphicGroupoid_maximalAtlas_subset' hA hAs hB hBs

/-- Chart independence of `HasWeakMFDerivOnBordered`: testing `atlas ClosedUpperHalfPlane X` and
`atlas H M` suffices. -/
theorem hasWeakMFDerivOnBordered_iff_atlas [HasGroupoid X borderedHolomorphicGroupoid]
    [IsManifold I ∞ M] [I.Boundaryless] (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u du s ↔
      ContinuousOn u s ∧ ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        HasWeakFDerivOn volume
          (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
          (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivOnGroupoid_iff_atlas borderedHolomorphicGroupoid_maximalAtlas_subset' hs

/-- Global chart independence of `HasWeakMFDerivBordered`: testing `atlas ClosedUpperHalfPlane X`
and `atlas H M` suffices. -/
theorem hasWeakMFDerivBordered_iff_atlas [HasGroupoid X borderedHolomorphicGroupoid]
    [IsManifold I ∞ M] [I.Boundaryless] :
    HasWeakMFDerivBordered I u du ↔
      Continuous u ∧ ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        HasWeakFDerivOn volume
          (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
          (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivGroupoid_iff_atlas borderedHolomorphicGroupoid_maximalAtlas_subset'

/-- Chart independence of `HasWeakMFDerivOnBordered`: testing preferred charts
`chartAt ClosedUpperHalfPlane x` and `chartAt H y` suffices. -/
theorem hasWeakMFDerivOnBordered_iff_chartAt [HasGroupoid X borderedHolomorphicGroupoid]
    [IsManifold I ∞ M] [I.Boundaryless] (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior ((extChartAt closedUpperHalfPlaneModel x).target ∩
          (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm)
        (chartTangentHom closedUpperHalfPlaneModel I
          (chartAt ClosedUpperHalfPlane x) (chartAt H y) u du) :=
  hasWeakMFDerivOnGroupoid_iff_chartAt borderedHolomorphicGroupoid_maximalAtlas_subset' hs

/-- Global chart independence of `HasWeakMFDerivBordered`: testing preferred charts suffices. -/
theorem hasWeakMFDerivBordered_iff_chartAt [HasGroupoid X borderedHolomorphicGroupoid]
    [IsManifold I ∞ M] [I.Boundaryless] :
    HasWeakMFDerivBordered I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior ((extChartAt closedUpperHalfPlaneModel x).target ∩
          (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm)
        (chartTangentHom closedUpperHalfPlaneModel I
          (chartAt ClosedUpperHalfPlane x) (chartAt H y) u du) :=
  hasWeakMFDerivGroupoid_iff_chartAt borderedHolomorphicGroupoid_maximalAtlas_subset'

/-- Equivalence of weak differentials under precomposition with a `C^n` (`1 ≤ n`) diffeomorphism of
bordered Riemann surfaces preserving `borderedHolomorphicGroupoid.maximalAtlas`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnBordered_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ClosedUpperHalfPlane Y]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮closedUpperHalfPlaneModel, closedUpperHalfPlaneModel⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas X)
    (hesymm : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas Y) :
    HasWeakMFDerivOnBordered I (u ∘ e)
        (fun y ↦ (du (e y)).comp
          (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOnBordered I u du s :=
  e.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff
    borderedHolomorphicGroupoid_maximalAtlas_subset'
    borderedHolomorphicGroupoid_maximalAtlas_subset' hn he hesymm

/-- Global equivalence of weak differentials under precomposition with a bordered biholomorphism. -/
theorem _root_.Diffeomorph.hasWeakMFDerivBordered_comp_diffeomorph_iff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ClosedUpperHalfPlane Y]
    {n : ℕ∞ω} (e : Y ≃ₘ^n⟮closedUpperHalfPlaneModel, closedUpperHalfPlaneModel⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas X)
    (hesymm : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas Y) :
    HasWeakMFDerivBordered I (u ∘ e)
        (fun y ↦ (du (e y)).comp
          (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e y)) ↔
      HasWeakMFDerivBordered I u du :=
  e.hasWeakMFDerivGroupoid_comp_diffeomorph_iff
    borderedHolomorphicGroupoid_maximalAtlas_subset'
    borderedHolomorphicGroupoid_maximalAtlas_subset' hn he hesymm

/-- **Existence of a global weak differential on a Riemann surface with boundary.** On a Lindelöf
bordered Riemann surface `X` and an open set `s ⊆ X`, every map satisfying
`MemWkpLocMapOnBordered I p 1 u s` into a boundaryless smooth manifold `M` admits a weak
differential `du` on `s` (whose coordinate expressions also satisfy `MemLpLoc p` up to `∂X` by
`HasWeakMFDerivOnGroupoid.memLpLoc_chartTangentHom`). -/
theorem MemWkpLocMapOnBordered.exists_hasWeakMFDerivOnBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless]
    (hu : MemWkpLocMapOnBordered I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnBordered I u du s :=
  MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset' hu hs

/-- **Global existence of a weak differential on a Riemann surface with boundary.** -/
theorem MemWkpLocMapBordered.exists_hasWeakMFDerivBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless]
    (hu : MemWkpLocMapBordered I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivBordered I u du :=
  MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset' hu

/-- First-order Sobolev characterization on an open subset of a Lindelöf Riemann surface with
boundary. -/
theorem memWkpLocMapOnBordered_one_iff_exists_hasWeakMFDerivOnBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless] (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p 1 u s ↔
      ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivOnBordered I u du s ∧
          ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
            MemLpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
              (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
              (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset' hs

/-- Global first-order Sobolev characterization on a Lindelöf Riemann surface with boundary. -/
theorem memWkpLocMapBordered_one_iff_exists_hasWeakMFDerivBordered
    [LindelofSpace X] [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]
    [I.Boundaryless] :
    MemWkpLocMapBordered I p 1 u ↔
      ∃ du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x),
        HasWeakMFDerivBordered I u du ∧
          ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
            MemLpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
              (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
              (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  memWkpLocMapGroupoid_one_iff_exists_hasWeakMFDerivGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset'

end BorderedSurface

end TauCeti
