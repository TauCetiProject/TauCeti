/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Local Sobolev maps from a Riemann surface with boundary into a manifold

Let `X` be a Riemann surface with boundary, given as a charted space modelled on the closed upper
half-plane `ClosedUpperHalfPlane` whose chart changes lie in `TauCeti.borderedHolomorphicGroupoid`,
and let `M` be a smooth manifold modelled on `I : ModelWithCorners ℝ F H`. A map `u : X → M` lies
in the local Sobolev class `W^{k,p}_loc(X, M)` up to the boundary
(`TauCeti.MemWkpLocMapBordered I p k u`) when it is continuous and every coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` belongs to the planar local Sobolev
class `TauCeti.MemWkpLoc p _ k` on the part of the extended target of `φ` where `u` maps into the
source of `ψ`. Here `φ` runs over all bordered holomorphic charts of `X`, the charts of the
maximal atlas of `TauCeti.borderedHolomorphicGroupoid`, and `ψ` over all charts of the maximal
smooth atlas of `M`.

The extended target of a chart of `X` lies in the closed upper half-plane `{z | 0 ≤ z.im}` of
`ℂ`, and the domain of a coordinate expression is relatively open there: it has the form
`Ω ∩ {z | 0 ≤ z.im}` for an open `Ω ⊆ ℂ`. The planar class `TauCeti.MemWkpLoc` on such a
half-disc type set imposes its `Lᵖ` bounds on compact sets reaching the real axis, so the
definition controls the map up to the boundary of `X`. This is the boundary-chart counterpart
of `TauCeti.MemWkpLocMapOn`, which treats Riemann surfaces without boundary.

The relative version `TauCeti.MemWkpLocMapOnBordered I p k u s` asks for continuity on `s` and
tests the coordinate expressions over `s`; it is intended for open subsets `s` of `X`. Both are the
classes `TauCeti.MemWkpLocMapOnGroupoid` and `TauCeti.MemWkpLocMapGroupoid` for the groupoid
`TauCeti.borderedHolomorphicGroupoid` and the model `closedUpperHalfPlaneModel`, so they share
their unfolding, restriction and monotonicity lemmas with the class for surfaces without boundary.

## Main declarations

* `TauCeti.MemWkpLocMapOnBordered`, `TauCeti.MemWkpLocMapBordered`: local Sobolev maps on a
  subset and on the whole surface with boundary.
* `ContMDiffOn.memWkpLocMapOnBordered`, `ContMDiff.memWkpLocMapBordered`: `C^n` maps belong to the
  class of every order `k ≤ n`, for every exponent. In a chart the coordinate expression is `Cᵏ`
  on a relatively open subset of the closed upper half-plane, hence in the planar class there
  (`ContDiffOn.memWkpLoc_inter_setOf_im_nonneg`).
* `TauCeti.MemWkpLocMapOn.memWkpLocMapOnBordered_image`: on an open subset of the interior
  `TauCeti.borderedInterior X`, a local Sobolev map for the Riemann surface structure of the
  interior is a local Sobolev map up to the boundary, with the same order and exponent. The
  coordinate expressions in a bordered holomorphic chart are those in its restriction to the
  interior, read in `ℂ` through the open upper half-plane.
* `TauCeti.not_memWkpLocMapOnBordered_sqrt_im`: on the closed upper half-disc, `z ↦ √(Im z)` is
  continuous but is not in the class of order `1` for any `p ≥ 2`, since the boundary chart
  tests its derivative `(2 √(Im z))⁻¹` on compact sets reaching the real axis.

## Implementation notes

As for `TauCeti.MemWkpLocMapOn`, the charts tested are those of the maximal atlases and the
definitions carry no manifold hypotheses; they are meant for
`HasGroupoid X borderedHolomorphicGroupoid` and `IsManifold I ∞ M`. That it suffices to test one
atlas of `X` near the boundary needs the change of variables for the half-disc classes along
bordered holomorphic chart changes, which are smooth only up to the real axis, and is not part of
this file. Neither is the converse of the comparison with the interior class, which tests charts
of the interior with values anywhere in `ℂ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 2.4.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

/-! ### The class of local Sobolev maps up to the boundary -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

variable (I) in
/-- A map `u : X → M` from a Riemann surface with boundary is in the local Sobolev class
`W^{k,p}_loc` on `s ⊆ X` if it is continuous on `s` and, for every bordered holomorphic chart `φ`
of `X` and every smooth chart `ψ` of `M`, the coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` over `s` where `u` maps into the
source of `ψ`. That part is relatively open in the closed upper half-plane, and the `Lᵖ` bounds
reach the real axis. The definition is intended for open `s`. -/
abbrev MemWkpLocMapOnBordered (p : ENNReal) (k : ℕ) (u : X → M) (s : Set X) : Prop :=
  MemWkpLocMapOnGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I p k u s

variable (I) in
/-- A map `u : X → M` from a Riemann surface with boundary is in the local Sobolev class
`W^{k,p}_loc(X, M)` if it is continuous and, for every bordered holomorphic chart `φ` of `X` and
every smooth chart `ψ` of `M`, the coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` where `u` maps into the source of
`ψ`, with `Lᵖ` bounds reaching the real axis. -/
abbrev MemWkpLocMapBordered (p : ENNReal) (k : ℕ) (u : X → M) : Prop :=
  MemWkpLocMapGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I p k u

/-! ### Smooth maps -/

/-- A map that is `C^n` on an open set, for the smooth structure of the Riemann surface with
boundary and a manifold `M` modelled on a real Banach space, is a local Sobolev map up to the
boundary on that set, of every order `k ≤ n` and every exponent. -/
theorem _root_.ContMDiffOn.memWkpLocMapOnBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn closedUpperHalfPlaneModel I n u s) (hk : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s := by
  refine memWkpLocMapOnGroupoid_iff.2 ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  have hφ' : φ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel k X :=
    StructureGroupoid.maximalAtlas_mono (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le (by exact_mod_cast le_top))) hφ
  have hψ' : ContMDiffOn I 𝓘(ℝ, F) k (ψ.extend I) ψ.source :=
    (ψ.contMDiffOn_extend hψ).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
    refine hψ'.comp ((hu.of_le hk).comp ((contMDiffOn_extend_symm hφ').mono ?_)
      fun _ hz ↦ hz.2.1) fun _ hz ↦ hz.2.2
    rw [← OpenPartialHomeomorph.extend_target']
    exact inter_subset_left
  obtain ⟨Ω, hΩ, hV⟩ := φ.exists_isOpen_extend_target_inter_preimage
    (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  rw [hV] at hcomp ⊢
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).memWkpLoc_inter_setOf_im_nonneg hΩ

/-- A `C^n` map, for the smooth structure of the Riemann surface with boundary and a manifold `M`
modelled on a real Banach space, is a local Sobolev map up to the boundary of every order
`k ≤ n` and every exponent. -/
theorem _root_.ContMDiff.memWkpLocMapBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff closedUpperHalfPlaneModel I n u) (hk : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMapBordered I p k u :=
  memWkpLocMapOnGroupoid_univ.mp (hu.contMDiffOn.memWkpLocMapOnBordered hk isOpen_univ)

/-! ### Comparison with the class on the interior -/

section Interior

variable [IsManifold closedUpperHalfPlaneModel 1 X]

open ClosedUpperHalfPlane in
/-- On an open subset `s` of the interior of a Riemann surface with boundary, a local Sobolev
map for the Riemann surface structure of the interior is a local Sobolev map up to the boundary
on `s`, with the same order and exponent. The coordinate expression in a bordered holomorphic
chart over `s` is its coordinate expression in the restriction of the chart to the interior, read
in `ℂ` through the open upper half-plane. -/
theorem MemWkpLocMapOn.memWkpLocMapOnBordered_image [CompleteSpace F]
    {s : Set (borderedInterior X)} (hu : MemWkpLocMapOn I p k (u ∘ (↑)) s) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u ((↑) '' s) := by
  have hcont : ContinuousOn u ((↑) '' s) :=
    Topology.IsInducing.subtypeVal.continuousOn_image_iff.2 hu.continuousOn
  refine memWkpLocMapOnGroupoid_iff.2 ⟨hcont, fun φ hφ ψ hψ ↦ ?_⟩
  set V := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' ((↑) '' s ∩ u ⁻¹' ψ.source)
  obtain ⟨Ω, hΩ, hV⟩ := φ.exists_isOpen_extend_target_inter_preimage
    (hcont.isOpen_inter_preimage
      ((borderedInterior X).isOpen.isOpenMap_subtype_val s hs) ψ.open_source)
  rcases V.eq_empty_or_nonempty with hV₀ | ⟨z₀, hz₀⟩
  · rw [hV₀]
    exact memWkpLoc_iff_locally.2 fun x hx ↦ hx.elim
  obtain ⟨x₀, -, -⟩ := hz₀.2.1
  have hne : Nonempty (borderedInterior X) := ⟨x₀⟩
  have hφ1 : φ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 X :=
    StructureGroupoid.maximalAtlas_mono (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le (by exact_mod_cast le_top))) hφ
  set φi := φ.subtypeRestr hne ≫ₕ upperHalfPlaneChart
  -- Every point of `V` lies in the test set of `φi`, where the two coordinate expressions agree.
  have hmem : ∀ z ∈ V, z ∈ φi.target ∩ φi.symm ⁻¹' (s ∩ (u ∘ (↑)) ⁻¹' ψ.source) ∧
      (ψ.extend I ∘ (u ∘ (↑)) ∘ φi.symm) z =
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z := by
    rintro z ⟨hzt, ⟨x, hxs, hxz⟩, hzψ⟩
    rw [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage,
      range_closedUpperHalfPlaneModel] at hzt
    rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] at hxz hzψ
    have hzi : z ∈ φi.target := by
      rw [subtypeRestr_trans_upperHalfPlaneChart_target hφ1 hne]
      have hxφ : (x : X) ∈ φ.source := by
        rw [hxz]
        exact φ.map_target hzt.1
      have h := (mem_borderedInterior_iff_im_pos hφ1 hxφ).1 x.2
      rw [hxz, φ.right_inv hzt.1, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hzt.2] at h
      exact ⟨hzt.1, h⟩
    have hsymm : φi.symm z = x :=
      Subtype.ext ((subtypeRestr_trans_upperHalfPlaneChart_symm_apply hzi).trans hxz.symm)
    refine ⟨⟨hzi, ?_, ?_⟩, ?_⟩
    · rw [hsymm]
      exact hxs
    · rw [mem_preimage, hsymm, Function.comp_apply, hxz]
      exact hzψ
    · simp only [Function.comp_apply, hsymm, OpenPartialHomeomorph.extend_coe_symm, ← hxz]
  have hVm : MeasurableSet V := by
    rw [show V = Ω ∩ {z | 0 ≤ z.im} from hV]
    exact hΩ.measurableSet_inter_setOf_im_nonneg
  exact ((hu.memWkpLoc_chart (subtypeRestr_trans_upperHalfPlaneChart_mem_maximalAtlas hφ hne)
    hψ).mono fun z hz ↦ (hmem z hz).1).congr_ae
      ((ae_restrict_iff' hVm).2 (Eventually.of_forall fun z hz ↦ (hmem z hz).2))

end Interior

/-! ### A square-root profile on the closed upper half-disc -/

/-- On the closed upper half-disc `{z | ‖z‖ < 1}` of `ClosedUpperHalfPlane`, the map
`z ↦ √(Im z)` is continuous, but it is not a local Sobolev map up to the boundary of order `1`
for any exponent `p ≥ 2`: in the identity chart its coordinate expression is `z ↦ √(Im z)` on
`ball 0 1 ∩ {z | 0 ≤ z.im}`, whose derivative `(2 √(Im z))⁻¹` is not square integrable near the
real axis (`TauCeti.memWkpLoc_sqrt_im_iff`). On the open half-disc it is smooth. -/
theorem not_memWkpLocMapOnBordered_sqrt_im (hp : 2 ≤ p) :
    ¬ MemWkpLocMapOnBordered 𝓘(ℝ) p 1 (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im)
      {z | ‖(z : ℂ)‖ < 1} := by
  intro h
  have hφ := borderedHolomorphicGroupoid.chart_mem_maximalAtlas (ClosedUpperHalfPlane.ofReal 0)
  have hψ := (contDiffGroupoid ∞ 𝓘(ℝ)).chart_mem_maximalAtlas (0 : ℝ)
  have hc := h.memWkpLoc_chart hφ hψ
  have hset : ((chartAt ClosedUpperHalfPlane (ClosedUpperHalfPlane.ofReal 0)).extend
      closedUpperHalfPlaneModel).target ∩
      ((chartAt ClosedUpperHalfPlane (ClosedUpperHalfPlane.ofReal 0)).extend
        closedUpperHalfPlaneModel).symm ⁻¹' ({z : ClosedUpperHalfPlane | ‖(z : ℂ)‖ < 1} ∩
        (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im) ⁻¹' (chartAt ℝ (0 : ℝ)).source) =
      Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im} := by
    ext z
    simp only [chartAt_self_eq, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.refl_target,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_source,
      OpenPartialHomeomorph.refl_apply, range_closedUpperHalfPlaneModel, preimage_univ,
      inter_univ, mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply, id_eq,
      Metric.mem_ball, dist_zero_right, mem_univ, true_and]
    constructor
    · rintro ⟨hz, hzn⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz] at hzn
      exact ⟨hzn, hz⟩
    · rintro ⟨hzn, hz⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz]
      exact ⟨hz, hzn⟩
  rw [hset] at hc
  have hc' : MemWkpLoc p (Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 1 (fun z : ℂ ↦ √z.im) := by
    refine hc.congr_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet_inter_setOf_im_nonneg).2
      (Eventually.of_forall fun z hz ↦ ?_))
    simp [chartAt_self_eq, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz.2]
  exact absurd (memWkpLoc_sqrt_im_iff.1 hc') (not_lt.2 hp)

end TauCeti
