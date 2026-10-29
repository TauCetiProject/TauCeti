/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Positive normal derivative of half-space coordinate transitions

At a boundary point, the zeroth coordinate of a chart transition has a local minimum within
the model half-space. Fermat's theorem on the positive tangent cone makes its derivative vanish
on the coordinate hyperplane and nonnegative in the inward direction. The inverse chart
transition makes the inward coefficient strictly positive. Thus outward signs are independent
of the preferred chart, including at boundary points.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- At a boundary point an actual coordinate transition scales the normal coordinate by a
strictly positive number. No block structure or orientation identity is assumed. -/
theorem tangentCoordChange_normal_pos {α β x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (hβ : x ∈ (extChartAt (𝓡∂ (n + 1)) β).source) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : EuclideanSpace ℝ (Fin (n + 1)),
      (tangentCoordChange (𝓡∂ (n + 1)) α β x v) 0 = a * v 0 := by
  let I := 𝓡∂ (n + 1)
  let y := extChartAt I α x
  let D := tangentCoordChange I α β x
  let f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun z ↦ (extChartAt I β ((extChartAt I α).symm z)) 0
  let π : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hz (γ : M) (hγ : x ∈ (extChartAt I γ).source) : (extChartAt I γ x) 0 = 0 := by
    have hc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) γ).source := by
      simpa only [extChartAt_source] using hγ
    have hb := (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
      one_ne_zero (chart_mem_atlas _ γ) hc).mp hx
    simpa only [I, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_toFun] using hb
  have hy0 : y 0 = 0 := hz α hα
  have hf0 : f y = 0 := by
    dsimp only [f, y]
    rw [(extChartAt I α).left_inv hα]
    exact hz β hβ
  have hsource : (extChartAt I α).symm ⁻¹' (extChartAt I β).source ∈ 𝓝 y := by
    apply (continuousAt_extChartAt_symm' hα).preimage_mem_nhds
    rw [(extChartAt I α).left_inv hα]
    exact extChartAt_source_mem_nhds' hβ
  have hmin : IsLocalMinOn f (range I) y := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hsource] with z hz'
    rw [hf0]
    have hm := extChartAt_target_subset_range β ((extChartAt I β).map_source hz')
    rw [range_modelWithCornersEuclideanHalfSpace] at hm
    exact hm
  have hdf : HasFDerivWithinAt f (π.comp D) (range I) y :=
    π.hasFDerivAt.comp_hasFDerivWithinAt y (hasFDerivWithinAt_tangentCoordChange ⟨hα, hβ⟩)
  have hcone (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) :
      v ∈ posTangentConeAt (range I) y := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset (mem_range_self (chartAt _ α x))
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp only [mem_ofPred_eq, PiLp.add_apply, hy0, zero_add]
    exact hv
  have hnonneg (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) : 0 ≤ (D v) 0 := by
    exact hmin.hasFDerivWithinAt_nonneg hdf (hcone v hv)
  let ν := EuclideanSpace.single (𝕜 := ℝ) (0 : Fin (n + 1)) 1
  let a := (D ν) 0
  have hfactor (v : EuclideanSpace ℝ (Fin (n + 1))) : (D v) 0 = a * v 0 :=
    (π.comp D).eq_mul_apply_zero_of_nonneg hnonneg v
  have ha : 0 ≤ a := hnonneg ν (by simp [ν])
  have hpos : 0 < a := by
    by_contra hn
    have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
    have hi : D (tangentCoordChange I β α x ν) = ν := by
      exact (tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hβ⟩).trans
        (tangentCoordChange_self hβ)
    have h := hfactor (tangentCoordChange I β α x ν)
    rw [hi, ha0, zero_mul] at h
    simp [ν] at h
  exact ⟨a, hpos, hfactor⟩

end TauCeti
