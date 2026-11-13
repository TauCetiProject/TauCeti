/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Smooth families of point motions

Let `M` be a Hausdorff boundaryless `C^n` manifold, `1 ≤ n`, modelled on a finite-dimensional
real normed space `E`. Near a point `y`, read in the chart at `y`, the maps `p ↦ p + ρ(p) • d`,
with `ρ` a bump function equal to `1` near `y`, are compactly supported diffeomorphisms of the
model space carrying the chart point `extChartAt I y y` to `extChartAt I y y + d`. Extended by
the identity outside the chart they form a family of diffeomorphisms of `M`, indexed by `d ∈ E`
and depending jointly smoothly on `d` and the point of `M`, carrying `y` to
`(extChartAt I y).symm (extChartAt I y y + d)` for small `d`, hence to every nearby point.

## Main results

* `TauCeti.exists_contMDiff_family_apply_eq`: jointly smooth families of diffeomorphisms
  moving a point to every nearby point.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma.
-/

public section

open Set Metric Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ∞} [IsManifold I n M]

/-- **Smooth families of point motions.** For `1 ≤ n`, every point `y` of an open set `V` of a
Hausdorff boundaryless `C^n` manifold `M` has an open neighbourhood `U` with a family `S d`,
`d ∈ E`, of `C^n` diffeomorphisms of `M`, depending jointly `C^n`-smoothly on `d` and the point of
`M`, and a map `f : M → E`, continuous on `U`, such that `S (f z)` carries `y` to `z` for every
`z ∈ U` and `S (f y)` is the identity. Every `S d` fixes each point outside a compact subset `K`
of `V`. -/
theorem exists_contMDiff_family_apply_eq (hn : 1 ≤ n) {V : Set M} (hV : IsOpen V) {y : M}
    (hy : y ∈ V) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ (K : Set M) (S : E → M ≃ₘ^n⟮I, I⟯ M) (f : M → E),
      IsCompact K ∧ K ⊆ V ∧ ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ S q.1 q.2) ∧
      ContinuousOn f U ∧ (∀ z ∈ U, S (f z) y = z) ∧ S (f y) = Diffeomorph.refl I M n ∧
      ∀ d, EqOn (S d) id Kᶜ := by
  set e := extChartAt I y with he
  -- A closed ball `K` about `e y` in the interior of the chart target, with image in `V`.
  have hVy : interior e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e y) :=
    Filter.inter_mem (isOpen_interior.mem_nhds
      ((I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint))
      ((continuousAt_extChartAt_symm y).preimage_mem_nhds
        (by rw [extChartAt_to_inv]; exact hV.mem_nhds hy))
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hVy
  set K := closedBall (e y) (r / 2)
  have hKr : K ⊆ ball (e y) r := closedBall_subset_ball (by linarith)
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ interior e.target := fun p hp ↦ (hrV (hKr hp)).1
  -- The compactly supported translations `τ d` of the model space, moving `e y` to `e y + d`.
  obtain ⟨δ, hδ, τ, hτs, hτK, hτ0, hτc⟩ :=
    exists_diffeomorph_family_apply_eq_add (e y) (by positivity : 0 < r / 2) hn
  have hτK' (d : E) : ∀ p ∉ K, τ d p = p := fun p hp ↦ hτK d p fun h ↦ hp (ball_subset_closedBall h)
  -- Their extensions through the chart form a smooth family `S` of diffeomorphisms of `M`.
  let S : E → M ≃ₘ^n⟮I, I⟯ M := fun d ↦ (τ d).chartExtend y hKc hKt (hτK' d)
  have hS : ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ S q.1 q.2) := by
    have hτs' := contMDiff_iff_contDiff.2 hτs
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hτs'
    exact Diffeomorph.contMDiff_chartExtend hτs' hτK'
  have hS_apply (d : E) (hd : ‖d‖ < δ) : S d y = e.symm (e y + d) := by
    have h := Diffeomorph.chartExtend_extChartAt_symm (φ := τ d) (hK := hKc) (hKt := hKt)
      (hφ := hτK' d) (mem_extChartAt_target y)
    rwa [← he, e.left_inv (mem_extChartAt_source y), hτc d hd] at h
  -- The section at `z` is `S (e z - e y)`, on the chart points within `δ` of `e y`.
  refine ⟨e.source ∩ e ⁻¹' ball (e y) δ, isOpen_extChartAt_preimage' y isOpen_ball,
    ⟨mem_extChartAt_source y, mem_ball_self hδ⟩, e.symm '' K, S, fun z ↦ e z - e y,
    isCompact_extChartAt_symm_image_closedBall fun p hp ↦ interior_subset (hKt hp),
    image_subset_iff.2 fun p hp ↦ (hrV (hKr hp)).2, hS, ?_, fun z hz ↦ ?_, ?_,
    fun d z hz ↦ Diffeomorph.chartExtend_eq_self hz⟩
  · exact ((continuousOn_extChartAt y).sub continuousOn_const).mono fun _ hz ↦ hz.1
  · rw [hS_apply _ (by rw [← dist_eq_norm]; exact hz.2), add_sub_cancel, e.left_inv hz.1]
  · ext z
    simp [S, hτ0, chartExtend_id]

end TauCeti
