/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.TangentHom
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
public import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Measure.Differentiable

/-!
# The weak differential of a local Sobolev map: definitions, locality, and uniqueness

For a surface `X` (possibly with boundary) and `M` modelled on `I : ModelWithCorners ℝ F H`,
`TauCeti.HasWeakMFDerivOnGroupoid G J I u du s` requires `ContinuousOn u s` and that
`TauCeti.chartTangentHom J I φ ψ u du` is a weak Fréchet derivative on the interior of every chart
overlap domain, independent of `p` and retaining both `(1, 0)` and `(0, 1)` components.

## Main declarations

* `TauCeti.HasWeakMFDerivOnGroupoid`, `TauCeti.HasWeakMFDerivGroupoid`,
  `TauCeti.HasWeakMFDerivOn`, `TauCeti.HasWeakMFDeriv`,
  `TauCeti.HasWeakMFDerivOnBordered`, `TauCeti.HasWeakMFDerivBordered`: weak differential
  predicates at groupoid generality and `abbrev` specializations for surfaces without/with boundary.
* `TauCeti.HasWeakMFDerivOnGroupoid.aestronglyMeasurable_chartTangentHom`,
  `TauCeti.HasWeakMFDerivOnGroupoid.memLpLoc_chartTangentHom`,
  `TauCeti.HasWeakMFDerivOnGroupoid.memWkpLocMapOnGroupoid_one_iff`: measurability and `MemLpLoc`
  regularity of `chartTangentHom` up to `∂J`.
* `TauCeti.hasWeakMFDerivOnGroupoid_iff_locally`, `TauCeti.ContMDiffOn.hasWeakMFDerivOnGroupoid`,
  `TauCeti.HasWeakMFDerivOnGroupoid.isNullSet_ne`: locality, `mfderiv` consistency, and a.e.
  uniqueness.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 3.1.
-/

public section

open Bundle Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology ComplexConjugate

noncomputable section

namespace TauCeti

section Groupoid

variable {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {u : X → M}
  {du du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s t : Set X}
  {φ : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H}

variable (G J I) in
/-- Weak differential of `u : X → M` on `s ⊆ X` for `G`, tested on open chart-overlap interiors. -/
def HasWeakMFDerivOnGroupoid (u : X → M)
    (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  ContinuousOn u s ∧ ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)

variable (G J I) in
/-- Global weak differential of `u : X → M` on `X` for the structure groupoid `G`. -/
def HasWeakMFDerivGroupoid (u : X → M)
    (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)) : Prop :=
  Continuous u ∧ ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)

/-- Unfolding `HasWeakMFDerivOnGroupoid`. -/
theorem hasWeakMFDerivOnGroupoid_iff : HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by rfl

/-- Unfolding `HasWeakMFDerivGroupoid`. -/
theorem hasWeakMFDerivGroupoid_iff : HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by rfl

/-- On `univ`, the relative weak differential predicate agrees with the global one. -/
@[simp] theorem hasWeakMFDerivOnGroupoid_univ :
    HasWeakMFDerivOnGroupoid G J I u du univ ↔ HasWeakMFDerivGroupoid G J I u du := by
  simp only [HasWeakMFDerivOnGroupoid, HasWeakMFDerivGroupoid, continuousOn_univ, univ_inter]

/-- Vacuous weak differentiability on `∅`. -/
@[simp] theorem hasWeakMFDerivOnGroupoid_empty [CompleteSpace F] :
    HasWeakMFDerivOnGroupoid G J I u du ∅ :=
  ⟨continuousOn_empty u, fun _ _ _ _ ↦ hasWeakFDerivOn_iff_locally.2 fun _ hz ↦
    False.elim (interior_subset hz).2.1⟩

/-- A constant map `fun _ ↦ c` has weak differential `0` on any set `s`. -/
theorem hasWeakMFDerivOnGroupoid_const [CompleteSpace F] (c : M) :
    HasWeakMFDerivOnGroupoid G J I (fun _ : X ↦ c) (fun _ ↦ 0) s :=
  ⟨continuousOn_const, fun _ _ ψ _ ↦ hasWeakFDerivOn_iff.2 fun v ↦ by
    simpa only [Function.comp_def, chartTangentHom_zero, zero_apply] using
      hasWeakLineDerivOn_const (μ := volume) (ψ.extend I c) (v := v)⟩

/-- A constant map `fun _ ↦ c` has global weak differential `0`. -/
theorem hasWeakMFDerivGroupoid_const [CompleteSpace F] (c : M) :
    HasWeakMFDerivGroupoid G J I (fun _ : X ↦ c) (fun _ ↦ 0) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hasWeakMFDerivOnGroupoid_const c)

/-- Continuity on `s` of a map with a weak differential on `s`. -/
theorem HasWeakMFDerivOnGroupoid.continuousOn (h : HasWeakMFDerivOnGroupoid G J I u du s) :
    ContinuousOn u s := h.1

/-- Continuity of a map with a global weak differential. -/
theorem HasWeakMFDerivGroupoid.continuous (h : HasWeakMFDerivGroupoid G J I u du) :
    Continuous u := h.1

/-- Reading off the planar weak derivative in charts `φ` and `ψ`. -/
theorem HasWeakMFDerivOnGroupoid.hasWeakFDerivOn_chart (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hφ : φ ∈ G.maximalAtlas X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := h.2 φ hφ ψ hψ

/-- Reading off the planar weak derivative of a global weak differential in charts `φ` and `ψ`. -/
theorem HasWeakMFDerivGroupoid.hasWeakFDerivOn_chart (h : HasWeakMFDerivGroupoid G J I u du)
    (hφ : φ ∈ G.maximalAtlas X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := h.2 φ hφ ψ hψ

/-- Restricting a weak differential to a subset. -/
theorem HasWeakMFDerivOnGroupoid.mono (h : HasWeakMFDerivOnGroupoid G J I u du s) (hts : t ⊆ s) :
    HasWeakMFDerivOnGroupoid G J I u du t :=
  ⟨h.1.mono hts, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono
    (interior_mono (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))))⟩

/-- Restricting a global weak differential to any subset. -/
theorem HasWeakMFDerivGroupoid.hasWeakMFDerivOnGroupoid (h : HasWeakMFDerivGroupoid G J I u du) :
    HasWeakMFDerivOnGroupoid G J I u du s :=
  (hasWeakMFDerivOnGroupoid_univ.2 h).mono (subset_univ s)

/-- Replacing `du` by a section agreeing with it on `s` preserves `HasWeakMFDerivOnGroupoid`. -/
theorem HasWeakMFDerivOnGroupoid.congr_deriv (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hdu : ∀ x ∈ s, du x = du' x) : HasWeakMFDerivOnGroupoid G J I u du' s := by
  refine ⟨h.1, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).congr_ae_deriv ?_⟩
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  exact chartTangentHom_congr (hdu _ (interior_subset hz).2.1)

/-- Congruence of `HasWeakMFDerivOnGroupoid` under `(u, du)` agreeing on `s` up to
`tangentSpaceCast`. -/
theorem HasWeakMFDerivOnGroupoid.congr {u' : X → M}
    {du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u' x)}
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hu : EqOn u u' s)
    (hdu : ∀ x ∈ s, (tangentSpaceCast I (u x) (u' x)).toContinuousLinearMap.comp (du x) = du' x) :
    HasWeakMFDerivOnGroupoid G J I u' du' s := by
  refine ⟨h.1.congr hu.symm, fun φ hφ ψ hψ ↦ ?_⟩
  have hdom : s ∩ u ⁻¹' ψ.source = s ∩ u' ⁻¹' ψ.source :=
    ext fun x ↦ and_congr_right fun hxs ↦ by simp [hu hxs]
  have hchart := h.2 φ hφ ψ hψ; rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    simp only [Function.comp_apply, hu (interior_subset hz).2.1]
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    exact chartTangentHom_congr_map (hu (interior_subset hz).2.1) (hdu _ (interior_subset hz).2.1)

/-- Global congruence of `HasWeakMFDerivGroupoid` up to `tangentSpaceCast`. -/
theorem HasWeakMFDerivGroupoid.congr {u' : X → M}
    {du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u' x)}
    (h : HasWeakMFDerivGroupoid G J I u du) (hu : ∀ x, u x = u' x)
    (hdu : ∀ x, (tangentSpaceCast I (u x) (u' x)).toContinuousLinearMap.comp (du x) = du' x) :
    HasWeakMFDerivGroupoid G J I u' du' :=
  hasWeakMFDerivOnGroupoid_univ.1
    ((hasWeakMFDerivOnGroupoid_univ.2 h).congr (fun x _ ↦ hu x) (fun x _ ↦ hdu x))

/-- Local integrability of `chartTangentHom` on the interior of every chart overlap domain. -/
theorem HasWeakMFDerivOnGroupoid.locallyIntegrableOn_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hφ : φ ∈ G.maximalAtlas X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    LocallyIntegrableOn (chartTangentHom J I φ ψ u du)
      (interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) volume :=
  (h.hasWeakFDerivOn_chart hφ hψ).locallyIntegrableOn_deriv

/-- A.e. strong measurability of `chartTangentHom` on the full chart overlap domain (up to `∂J`). -/
theorem HasWeakMFDerivOnGroupoid.aestronglyMeasurable_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hs : IsOpen s)
    (hφ : φ ∈ G.maximalAtlas X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    AEStronglyMeasurable (chartTangentHom J I φ ψ u du)
      (volume.restrict ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) := by
  rw [← φ.measure_restrict_interior_extend_eq (h.1.isOpen_inter_preimage hs ψ.open_source) volume]
  exact (h.locallyIntegrableOn_chartTangentHom hφ hψ).aestronglyMeasurable

/-- Local `Lᵖ` regularity of `chartTangentHom` up to `∂J` for `MemWkpLocMapOnGroupoid G J I p 1`. -/
theorem HasWeakMFDerivOnGroupoid.memLpLoc_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hu : MemWkpLocMapOnGroupoid G J I p 1 u s)
    (hs : IsOpen s) (hφ : φ ∈ G.maximalAtlas X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (chartTangentHom J I φ ψ u du) := by
  obtain ⟨D, hD, hDp⟩ := (hu.memWkpLoc_chart hφ hψ).exists_weakFDeriv
  have hae := hD.ae_eq (h.hasWeakFDerivOn_chart hφ hψ)
  rw [Opens.coe_interior, φ.measure_restrict_interior_extend_eq
    (h.1.isOpen_inter_preimage hs ψ.open_source) volume] at hae
  exact (memWkpLoc_zero_iff.1 hDp).congr_ae hae

/-- Given `du` on open `s`, `MemWkpLocMapOnGroupoid G J I p 1 u s` holds iff every `chartTangentHom`
is `MemLpLoc p`. -/
theorem HasWeakMFDerivOnGroupoid.memWkpLocMapOnGroupoid_one_iff
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hs : IsOpen s) :
    MemWkpLocMapOnGroupoid G J I p 1 u s ↔
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (chartTangentHom J I φ ψ u du) :=
  ⟨fun hu _ hφ _ hψ ↦ h.memLpLoc_chartTangentHom hu hs hφ hψ,
    fun hLp ↦ memWkpLocMapOnGroupoid_iff.2 ⟨h.1, fun φ hφ ψ hψ ↦ memWkpLoc_succ_iff.2
      ⟨(φ.continuousOn_extend_comp_symm ψ h.1 subset_rfl).memLpLoc, chartTangentHom J I φ ψ u du,
        h.hasWeakFDerivOn_chart hφ hψ, memWkpLoc_zero_iff.2 (hLp φ hφ ψ hψ)⟩⟩⟩

/-- **Neighborhood locality of weak differentials** on an open set `s`. -/
theorem hasWeakMFDerivOnGroupoid_iff_locally [CompleteSpace F] (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔
      ∀ x ∈ s, ∃ U ⊆ s, IsOpen U ∧ x ∈ U ∧ HasWeakMFDerivOnGroupoid G J I u du U := by
  refine ⟨fun h x hx ↦ ⟨s, subset_rfl, hs, hx, h⟩, fun hloc ↦ ?_⟩
  have hc : ContinuousOn u s := fun x hx ↦
    let ⟨U, _, hUo, hxU, hU⟩ := hloc x hx
    ((hU.continuousOn x hxU).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt
  refine ⟨hc, fun φ hφ ψ hψ ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩
  obtain ⟨U, hUs, hUo, hxU, hU⟩ := hloc _ (interior_subset hz).2.1
  exact ⟨Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (U ∩ u ⁻¹' ψ.source)),
    φ.mem_interior_extend_target_inter_preimage
      (mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left))
      (((hc.mono hUs).isOpen_inter_preimage hUo ψ.open_source).mem_nhds
        ⟨hxU, (interior_subset hz).2.2⟩),
    hU.hasWeakFDerivOn_chart hφ hψ⟩

/-- **Open-cover locality of weak differentials** on `⋃ i, U i`. -/
theorem hasWeakMFDerivOnGroupoid_iUnion_iff [CompleteSpace F] {ι : Sort*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) : HasWeakMFDerivOnGroupoid G J I u du (⋃ i, U i) ↔
      ∀ i, HasWeakMFDerivOnGroupoid G J I u du (U i) := by
  refine ⟨fun h i ↦ h.mono (subset_iUnion U i), fun h ↦ ?_⟩
  rw [hasWeakMFDerivOnGroupoid_iff_locally (isOpen_iUnion hU)]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩
  exact ⟨U i, subset_iUnion U i, hU i, hxi, h i⟩

/-- Gluing weak differentials on two open sets. -/
theorem HasWeakMFDerivOnGroupoid.union {s₁ s₂ : Set X} (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂)
    (h₁ : HasWeakMFDerivOnGroupoid G J I u du s₁) (h₂ : HasWeakMFDerivOnGroupoid G J I u du s₂) :
    HasWeakMFDerivOnGroupoid G J I u du (s₁ ∪ s₂) := by
  refine ⟨h₁.1.union_of_isOpen h₂.1 hs₁ hs₂, fun φ hφ ψ hψ ↦ ?_⟩
  have := (h₁.hasWeakFDerivOn_chart hφ hψ).completeSpace
  refine hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_
  have hzt : (φ.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  rcases (interior_subset hz).2.1 with hzs | hzs
  · exact ⟨_, φ.mem_interior_extend_target_inter_preimage hzt
      ((h₁.1.isOpen_inter_preimage hs₁ ψ.open_source).mem_nhds ⟨hzs, (interior_subset hz).2.2⟩),
      h₁.hasWeakFDerivOn_chart hφ hψ⟩
  · exact ⟨_, φ.mem_interior_extend_target_inter_preimage hzt
      ((h₂.1.isOpen_inter_preimage hs₂ ψ.open_source).mem_nhds ⟨hzs, (interior_subset hz).2.2⟩),
      h₂.hasWeakFDerivOn_chart hφ hψ⟩

/-- **Consistency with `mfderiv`** for `C^n` (`1 ≤ n`) maps on open `s`. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOnGroupoid [CompleteSpace F] {n : ℕ∞ω}
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) (hu : ContMDiffOn J I n u s)
    (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u (fun x ↦ mfderiv J I u x) s := by
  refine ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  set V := (φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hψ1 : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by simp)) hψ
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) 1 (ψ.extend I ∘ u ∘ (φ.extend J).symm) (interior V) :=
    (ψ.contMDiffOn_extend hψ1).comp
      ((hu.of_le hn).comp ((φ.extend_target' (I := J) ▸ contMDiffOn_extend_symm (hG hφ)).mono
        (interior_subset.trans inter_subset_left)) fun _ hz ↦ (interior_subset hz).2.1)
      fun _ hz ↦ (interior_subset hz).2.2
  refine ((contMDiffOn_iff_contDiffOn.1 hcomp).hasWeakFDerivOn_fderiv
    (μ := volume) (Ω := Opens.interior V)).congr_ae_deriv ?_
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  exact (chartTangentHom_mfderiv (hG hφ) hψ1 (interior_mono inter_subset_left hz)
    (interior_subset hz).2.2 (((hu.of_le hn _ (interior_subset hz).2.1).contMDiffAt
      (hs.mem_nhds (interior_subset hz).2.1)).mdifferentiableAt one_ne_zero)).symm

/-- Modifying `du` on a chartwise null subset of `s` preserves `HasWeakMFDerivOnGroupoid`. -/
theorem HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet [IsManifold J 1 X]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hnull : IsNullSet J {x ∈ s | du x ≠ du' x}) :
    HasWeakMFDerivOnGroupoid G J I u du' s := by
  refine ⟨h.1, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).congr_ae_deriv ?_⟩
  rw [EventuallyEq, Opens.coe_interior, ae_restrict_iff' isOpen_interior.measurableSet]
  filter_upwards [compl_mem_ae_iff.2
    (hnull.measure_inter_preimage_extend_symm_eq_zero (hG hφ) volume)] with z hz hzV
  exact chartTangentHom_congr
    (not_not.1 fun hne ↦ hz ⟨(interior_subset hzV).1, (interior_subset hzV).2.1, hne⟩)

private theorem measure_image_interior_ne_eq_zero [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] (hs : IsOpen s) (h₁ : HasWeakMFDerivOnGroupoid G J I u du s)
    (h₂ : HasWeakMFDerivOnGroupoid G J I u du' s) (x₀ : X) (y₀ : M)
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    μ (extChartAt J x₀ '' {x | x ∈ s ∧ du x ≠ du' x ∧ x ∈ (extChartAt J x₀).source ∧
      u x ∈ (chartAt H y₀).source ∧ J.IsInteriorPoint x}) = 0 := by
  have hx₀ := StructureGroupoid.chart_mem_maximalAtlas G x₀
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  rcases eventually_iff_exists_mem.1 ((ae_restrict_iff' isOpen_interior.measurableSet).1
    ((h₁.hasWeakFDerivOn_chart hx₀ (IsManifold.chart_mem_maximalAtlas y₀)).ae_eq
      (h₂.hasWeakFDerivOn_chart hx₀ (IsManifold.chart_mem_maximalAtlas y₀)))) with
    ⟨S, hSae, hSeq⟩
  refine Measure.absolutelyContinuous_isAddHaarMeasure μ volume
    (measure_mono_null (t := Sᶜ) ?_ (mem_ae_iff.1 hSae))
  rintro _ ⟨x, ⟨hxs, hxne, hxsrc, hy, hxint⟩, rfl⟩ hzS
  have hxsrc' : x ∈ (chartAt H' x₀).source := by simpa only [extChartAt_source] using hxsrc
  exact hxne ((chartTangentHom_chartAt_eq_iff hxsrc' hy).1 (hSeq (extChartAt J x₀ x) hzS
    ((chartAt H' x₀).mem_interior_extend_target_inter_preimage
      (ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint one_ne_zero x₀ hxsrc hxint)
      (by rw [extChartAt, (chartAt H' x₀).extend_left_inv hxsrc']
          exact (h₁.1.isOpen_inter_preimage hs (chartAt H y₀).open_source).mem_nhds ⟨hxs, hy⟩))))

/-- **Almost-everywhere uniqueness of the weak differential** on an open set `s`. -/
theorem HasWeakMFDerivOnGroupoid.isNullSet_ne [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] (hs : IsOpen s) (h₁ : HasWeakMFDerivOnGroupoid G J I u du s)
    (h₂ : HasWeakMFDerivOnGroupoid G J I u du' s) : IsNullSet J {x ∈ s | du x ≠ du' x} := by
  rw [isNullSet_iff]; intro x₀ μ _
  -- Cover `W ⊆ ℂ` (second-countable) by countably many target-chart pullbacks, then split `∂J`.
  set W := interior ((extChartAt J x₀).target ∩ (extChartAt J x₀).symm ⁻¹' s)
  let U : M → Set ℂ := fun y₀ ↦ W ∩ (u ∘ (extChartAt J x₀).symm) ⁻¹' (chartAt H y₀).source
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable U fun y₀ ↦
    (h₁.1.comp ((continuousOn_extChartAt_symm x₀).mono (interior_subset.trans inter_subset_left))
      fun _ hz ↦ (interior_subset hz).2).isOpen_inter_preimage
        isOpen_interior (chartAt H y₀).open_source
  refine measure_mono_null ?_
    (measure_union_null ((isNullSet_boundary (I := J)).chartwise x₀ μ)
      ((measure_biUnion_null_iff hTcnt).2
        fun y₀ _ ↦ measure_image_interior_ne_eq_zero hs h₁ h₂ x₀ y₀ μ))
  rintro _ ⟨x, ⟨⟨hxs, hxne⟩, hxsrc⟩, rfl⟩
  have hxsrc' : x ∈ (chartAt H' x₀).source := by simpa only [extChartAt_source] using hxsrc
  -- Interior points lie in the countable target-chart cover; non-interior points lie in `∂J`.
  by_cases hbd : J.IsInteriorPoint x
  · have hzW : extChartAt J x₀ x ∈ W := (chartAt H' x₀).mem_interior_extend_target_inter_preimage
      (ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint one_ne_zero x₀ hxsrc hbd)
      (by rw [extChartAt, (chartAt H' x₀).extend_left_inv hxsrc']; exact hs.mem_nhds hxs)
    have hzU : extChartAt J x₀ x ∈ ⋃ y₀ ∈ T, U y₀ :=
      hTcov ▸ mem_iUnion.2 ⟨_, hzW, mem_chart_source H _⟩
    rcases mem_iUnion₂.1 hzU with ⟨y₀, hy₀T, _, hy₀⟩
    rw [mem_preimage, Function.comp_apply, (extChartAt J x₀).left_inv hxsrc] at hy₀
    exact Or.inr (mem_iUnion₂.2 ⟨y₀, hy₀T, x, ⟨hxs, hxne, hxsrc, hy₀, hbd⟩, rfl⟩)
  · exact Or.inl ⟨x, ⟨(J.isBoundaryPoint_iff_not_isInteriorPoint x).2 hbd, hxsrc⟩, rfl⟩

/-- On open `s` where `u` is `C^n` (`1 ≤ n`), any weak differential agrees a.e. with `mfderiv`. -/
theorem HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] {n : ℕ∞ω} (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hu : ContMDiffOn J I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    IsNullSet J {x ∈ s | du x ≠ mfderiv J I u x} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · exact (isNullSet_iff J _).2 fun _ _ _ ↦ by simp
  have := (h.hasWeakFDerivOn_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
  let G' : StructureGroupoid H' := G ⊓ contDiffGroupoid 1 J
  have : HasGroupoid X G' := hasGroupoid_inf_iff.2 ⟨inferInstance, inferInstance⟩
  exact HasWeakMFDerivOnGroupoid.isNullSet_ne (G := G') hs
    (hasWeakMFDerivOnGroupoid_iff.2
      ⟨h.1, fun φ hφ ψ hψ ↦ h.2 φ (StructureGroupoid.maximalAtlas_mono inf_le_left hφ) ψ hψ⟩)
    (hu.hasWeakMFDerivOnGroupoid (StructureGroupoid.maximalAtlas_mono inf_le_right) hn hs)

end Groupoid

/-! ### Riemann surfaces without boundary -/

section BoundarylessSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {u : X → M} {du du' : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {s : Set X}

variable (I) in
/-- Weak differential of `u : X → M` on `s ⊆ X` for a Riemann surface `X` without boundary. -/
abbrev HasWeakMFDerivOn (u : X → M)
    (du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  HasWeakMFDerivOnGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I u du s

variable (I) in
/-- Global weak differential of `u : X → M` from a Riemann surface without boundary. -/
abbrev HasWeakMFDeriv (u : X → M)
    (du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) : Prop :=
  HasWeakMFDerivGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I u du

/-- Unfolding `HasWeakMFDerivOn` on an open set `s` of a Riemann surface without boundary. -/
theorem hasWeakMFDerivOn_iff (hs : IsOpen s) : HasWeakMFDerivOn I u du s ↔ ∃ hc : ContinuousOn u s,
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume ⟨φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source),
        φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source⟩
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine ⟨fun ⟨hc, h⟩ ↦ ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩, fun ⟨hc, h⟩ ↦ ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩⟩ <;>
  · have hO : Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) =
        ⟨_, φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source⟩ :=
      Opens.ext (φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source).interior_eq
    simpa only [OpenPartialHomeomorph.extend_modelWithCornersSelf,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm, hO] using h φ hφ ψ hψ

/-- Unfolding `HasWeakMFDeriv` on a Riemann surface without boundary. -/
theorem hasWeakMFDeriv_iff : HasWeakMFDeriv I u du ↔ ∃ hc : Continuous u,
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume ⟨φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source),
        φ.isOpen_inter_preimage_symm (ψ.open_source.preimage hc)⟩
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  simpa only [← hasWeakMFDerivOnGroupoid_univ, continuousOn_univ, univ_inter] using
    hasWeakMFDerivOn_iff (I := I) (u := u) (du := du) isOpen_univ

/-- Consistency of `HasWeakMFDerivOn` with `mfderiv` for `C^n` (`1 ≤ n`) maps on open `s`. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOn I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) s :=
  hu.hasWeakMFDerivOnGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hn hs

/-- Global consistency of `HasWeakMFDeriv` with `mfderiv` for `C^n` (`1 ≤ n`) maps. -/
theorem _root_.ContMDiff.hasWeakMFDeriv [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I n u) (hn : 1 ≤ n) :
    HasWeakMFDeriv I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hu.contMDiffOn.hasWeakMFDerivOn hn isOpen_univ)

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℂ E H''} [I''.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H'' M']
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold I'' 1 M'] {f : X → M'}

/-- A map holomorphic on an open set `s` has `mfderiv` as a weak differential on `s`. -/
theorem _root_.MDifferentiableOn.hasWeakMFDerivOn (hf : MDifferentiableOn 𝓘(ℂ) I'' f s)
    (hs : IsOpen s) : HasWeakMFDerivOn (I''.restrictScalars ℝ) f
      (fun x ↦ mfderiv 𝓘(ℝ, ℂ) (I''.restrictScalars ℝ) f x) s := by
  have hf' := (hf.contMDiffOn (n := 1) hs).restrictScalars ℝ
  rw [modelWithCornersSelf_restrictScalars] at hf'
  exact hf'.hasWeakMFDerivOn le_rfl hs

/-- A holomorphic map from a Riemann surface has `mfderiv` as a global weak differential. -/
theorem _root_.MDifferentiable.hasWeakMFDeriv (hf : MDifferentiable 𝓘(ℂ) I'' f) :
    HasWeakMFDeriv (I''.restrictScalars ℝ) f
      (fun x ↦ mfderiv 𝓘(ℝ, ℂ) (I''.restrictScalars ℝ) f x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hf.mdifferentiableOn.hasWeakMFDerivOn isOpen_univ)

end Holomorphic

section Uniqueness

variable [IsManifold 𝓘(ℂ) 1 X]

private theorem isManifold_real : IsManifold 𝓘(ℝ, ℂ) 1 X :=
  IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance

/-- Almost-everywhere uniqueness of the weak differential on a Riemann surface without boundary. -/
theorem HasWeakMFDerivOn.isNullSet_ne [IsManifold I ∞ M] (hs : IsOpen s)
    (h₁ : HasWeakMFDerivOn I u du s) (h₂ : HasWeakMFDerivOn I u du' s) :
    IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ du' x} :=
  haveI := isManifold_real (X := X); HasWeakMFDerivOnGroupoid.isNullSet_ne hs h₁ h₂

/-- Null-set congruence of the weak differential on a Riemann surface without boundary. -/
theorem HasWeakMFDerivOn.congr_deriv_of_isNullSet (h : HasWeakMFDerivOn I u du s)
    (hnull : IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ du' x}) : HasWeakMFDerivOn I u du' s :=
  haveI := isManifold_real (X := X)
  HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) h hnull

/-- Consistency uniqueness against `mfderiv` on an open subset of a Riemann surface. -/
theorem HasWeakMFDerivOn.isNullSet_ne_mfderiv [IsManifold I ∞ M] {n : ℕ∞ω}
    (h : HasWeakMFDerivOn I u du s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hn : 1 ≤ n)
    (hs : IsOpen s) : IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ mfderiv 𝓘(ℝ, ℂ) I u x} :=
  haveI := isManifold_real (X := X); HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv h hu hn hs

end Uniqueness

end BoundarylessSurface

/-! ### Riemann surfaces with boundary -/

section BorderedSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {u : X → M}
  {du du' : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)}
  {s : Set X}

variable (I) in
/-- Weak differential of `u : X → M` on `s ⊆ X` for a Riemann surface `X` with boundary. -/
abbrev HasWeakMFDerivOnBordered (u : X → M)
    (du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x))
    (s : Set X) : Prop :=
  HasWeakMFDerivOnGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I u du s

variable (I) in
/-- Global weak differential of `u : X → M` on a Riemann surface with boundary. -/
abbrev HasWeakMFDerivBordered (u : X → M)
    (du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)) : Prop :=
  HasWeakMFDerivGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I u du

/-- Consistency of `HasWeakMFDerivOnBordered` with `mfderiv` for `C^n` (`1 ≤ n`) maps on `s`. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOnBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn closedUpperHalfPlaneModel I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u (fun x ↦ mfderiv closedUpperHalfPlaneModel I u x) s :=
  hu.hasWeakMFDerivOnGroupoid (borderedHolomorphicGroupoid_maximalAtlas_subset (by simp)) hn hs

/-- Global consistency of `HasWeakMFDerivBordered` with `mfderiv` for `C^n` (`1 ≤ n`) maps. -/
theorem _root_.ContMDiff.hasWeakMFDerivBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff closedUpperHalfPlaneModel I n u) (hn : 1 ≤ n) :
    HasWeakMFDerivBordered I u (fun x ↦ mfderiv closedUpperHalfPlaneModel I u x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hu.contMDiffOn.hasWeakMFDerivOnBordered hn isOpen_univ)

/-- Null-set congruence of the weak differential on a Riemann surface with boundary. -/
theorem HasWeakMFDerivOnBordered.congr_deriv_of_isNullSet
    [HasGroupoid X borderedHolomorphicGroupoid] (h : HasWeakMFDerivOnBordered I u du s)
    (hnull : IsNullSet closedUpperHalfPlaneModel {x ∈ s | du x ≠ du' x}) :
    HasWeakMFDerivOnBordered I u du' s :=
  HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet
    (borderedHolomorphicGroupoid_maximalAtlas_subset (by simp)) h hnull

end BorderedSurface

/-! ### Concrete checks on the complex plane -/

section Checks

/-- Reading `du` in the holomorphic chart `z ↦ 2 z` of `ℂ` scales `chartTangentHom` by `2⁻¹`. -/
theorem chartTangentHom_mulLeft_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (ψ : OpenPartialHomeomorph M H) (u : ℂ → M)
    (du : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace I (u z)) (w : ℂ) :
    chartTangentHom 𝓘(ℝ, ℂ) I
        (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph ψ u du w =
      (2⁻¹ : ℝ) • chartTangentHom 𝓘(ℝ, ℂ) I (OpenPartialHomeomorph.refl ℂ) ψ u du (2⁻¹ * w) := by
  simpa using chartTangentHom_mulLeft₀ (𝕜 := ℝ) (D := ℂ) ψ u du (c := 2) (by norm_num) w

/-- Complex conjugation `conj : ℂ → ℂ` has weak differential `Complex.conjCLE`. -/
theorem hasWeakMFDeriv_conj : HasWeakMFDeriv 𝓘(ℝ, ℂ) (conj : ℂ → ℂ) fun z ↦
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z)).symm.toContinuousLinearMap ∘L
      Complex.conjCLE.toContinuousLinearMap ∘L
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap := by
  have hc : ContDiff ℝ 1 (conj : ℂ → ℂ) := funext Complex.conjCLE_apply ▸ Complex.conjCLE.contDiff
  convert (contMDiff_iff_contDiff.2 hc).hasWeakMFDeriv le_rfl using 2 with z
  ext v; rw [mfderiv_eq_fderiv, ← funext Complex.conjCLE_apply, Complex.conjCLE.fderiv]

private theorem not_hasWeakMFDerivOn_zero_of_ne {u : ℂ → ℂ}
    {du : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (u z)} {s : Set ℂ}
    (hs : IsOpen s) (hne : s.Nonempty) (hu : HasWeakMFDerivOn 𝓘(ℝ, ℂ) u du s)
    (hdu : ∀ z, du z ≠ 0) : ¬ HasWeakMFDerivOn 𝓘(ℝ, ℂ) u (fun _ ↦ 0) s := fun h0 ↦
  hne.ne_empty (hs.interior_eq ▸
    ((h0.isNullSet_ne hs hu).mono fun z hzs ↦ ⟨hzs, (hdu z).symm⟩).interior_eq_empty)

/-- On any nonempty open subset `s ⊆ ℂ`, `0` is not a weak differential of `id : ℂ → ℂ`. -/
theorem not_hasWeakMFDerivOn_id_zero {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ HasWeakMFDerivOn 𝓘(ℝ, ℂ) (id : ℂ → ℂ) (fun _ ↦ 0) s :=
  not_hasWeakMFDerivOn_zero_of_ne hs hne (contMDiffOn_id.hasWeakMFDerivOn (n := 1) le_rfl hs)
    fun z h ↦ one_ne_zero (α := ℂ) <| by
      simpa [mfderiv_id] using congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) z)
        (DFunLike.congr_fun h ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm 1))

/-- On any nonempty open subset `s ⊆ ℂ`, `0` is not a weak differential of `conj : ℂ → ℂ`. -/
theorem not_hasWeakMFDerivOn_conj_zero {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ HasWeakMFDerivOn 𝓘(ℝ, ℂ) (conj : ℂ → ℂ) (fun _ ↦ 0) s :=
  not_hasWeakMFDerivOn_zero_of_ne hs hne hasWeakMFDeriv_conj.hasWeakMFDerivOnGroupoid
    fun z h ↦ one_ne_zero (α := ℂ) <| by
      simpa using congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z))
        (DFunLike.congr_fun h ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm 1))

end Checks

end TauCeti
