/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic

/-!
# Unique continuation for holomorphic differentials

On a connected Riemann surface a holomorphic differential with infinite order at one point
vanishes everywhere. In particular, a nonzero holomorphic differential has finite order at
every point. This permits division by a nonzero differential in the meromorphic function field.

The local input is Mathlib's clopen infinite-order locus for meromorphic functions, applied
to the coefficient of the differential in each chart.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §§1 and 9, for unique continuation in charts.
-/

public section

open Filter Function IsManifold Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] {ω : OneForm X}

private theorem isOpen_order_locus (p : WithTop ℤ → Prop)
    (hp : ∀ x : X, IsOpen {z : (chartAt ℂ x).target |
      p (_root_.meromorphicOrderAt (ω.coeff (chartAt ℂ x)) z)}) :
    IsOpen {x | p (ω.order x)} := by
  rw [ChartedSpace.isOpen_iff (H := ℂ)]
  intro x
  have ho := (chartAt ℂ x).open_target.isOpenEmbedding_subtypeVal.isOpenMap _ (hp x)
  convert ho using 1
  ext z
  simp only [mem_image, mem_inter_iff, mem_ofPred_eq, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    exact ⟨chartAt ℂ x y, (chartAt ℂ x).map_source hy, by
      rwa [← order_eq_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hy], rfl⟩
  · rintro ⟨w, hw, hωw, rfl⟩
    refine ⟨(chartAt ℂ x).symm w, ⟨(chartAt ℂ x).map_target hw, ?_⟩,
      (chartAt ℂ x).right_inv hw⟩
    rwa [order_eq_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
      ((chartAt ℂ x).map_target hw), (chartAt ℂ x).right_inv hw]

/-- The infinite-order locus of an everywhere meromorphic differential is clopen. -/
theorem isClopen_setOf_order_eq_top (hω : ∀ x, ω.MeromorphicAt x) :
    IsClopen {x | ω.order x = ⊤} := by
  have hchart (x : X) :
      IsClopen {z : (chartAt ℂ x).target |
        _root_.meromorphicOrderAt (ω.coeff (chartAt ℂ x)) z = ⊤} := by
    apply MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top
    intro z hz
    have h := (meromorphicAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
      ((chartAt ℂ x).map_target hz)).1 (hω ((chartAt ℂ x).symm z))
    simpa only [(chartAt ℂ x).right_inv hz] using h
  exact ⟨isOpen_compl_iff.1 (isOpen_order_locus (fun a ↦ a ≠ ⊤)
    fun x ↦ (hchart x).isClosed.isOpen_compl),
    isOpen_order_locus (fun a ↦ a = ⊤) fun x ↦ (hchart x).isOpen⟩

/-- A holomorphic differential of infinite order at a point vanishes at that point. -/
theorem HolomorphicAt.apply_eq_zero_of_order_eq_top {x : X} (hω : ω.HolomorphicAt x)
    (hx : ω.order x = ⊤) : ω x = 0 := by
  have ha := (holomorphicAt_def ω x).1 hω
  have hc : ω.coeff (chartAt ℂ x) (chartAt ℂ x x) = 0 := by
    apply tendsto_nhds_unique_of_eventuallyEq
      (ha.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {chartAt ℂ x x}ᶜ)))
      (continuousAt_const.tendsto.mono_left nhdsWithin_le_nhds)
    exact _root_.meromorphicOrderAt_eq_top_iff.1 ((order_def ω x).symm.trans hx)
  rw [← (coeff_eq_iff ω (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)).1 rfl,
    hc, zero_smul]

/-- **Unique continuation.** On a connected surface, a holomorphic differential has infinite
order at a point exactly when it is the zero differential. -/
@[simp]
theorem order_eq_top_iff [PreconnectedSpace X] (hω : ∀ x, ω.HolomorphicAt x) (x : X) :
    ω.order x = ⊤ ↔ ω = 0 := by
  refine ⟨fun hx ↦ ?_, fun h ↦ by simp [h]⟩
  have hu := (isClopen_setOf_order_eq_top fun y ↦ (hω y).meromorphicAt).eq_univ ⟨x, hx⟩
  funext y
  exact (hω y).apply_eq_zero_of_order_eq_top (eq_univ_iff_forall.1 hu y)

end TauCeti.RiemannSurface.OneForm
