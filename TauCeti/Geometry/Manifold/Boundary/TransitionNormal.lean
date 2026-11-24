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
of the preferred chart, including at boundary points. The minimum of the normal coordinate at a
boundary point is `normal_le_of_mem_boundary`, and the Fermat step,
`hasFDerivWithinAt_nonneg_of_isLocalMin`, holds for any function with a local minimum at a
boundary point, read in a preferred chart.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- The normal coordinate `(e ·).1 0` of a half-space chart `e` attains its minimum at a boundary
point `x` of the source of `e`: it vanishes there and is nonnegative everywhere. -/
theorem normal_le_of_mem_boundary {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    {x : M} (hx : x ∈ (𝓡∂ (n + 1)).boundary M) (hxe : x ∈ e.source) (y : M) :
    (e x).val 0 ≤ (e y).val 0 :=
  ((ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hxe).mp hx).trans_le (e y).property

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- **Fermat's theorem at a boundary point**, read in a chart. If `f : M → ℝ` has a local minimum
at a boundary point `x`, then, read in an extended chart at `α` whose source contains `x`, its
derivative within the model half-space is nonnegative on the closed inward half-space
`0 ≤ v 0`. -/
theorem hasFDerivWithinAt_nonneg_of_isLocalMin {f : M → ℝ} {α x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source) (hmin : IsLocalMin f x)
    {f' : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ}
    (hf : HasFDerivWithinAt (f ∘ (extChartAt (𝓡∂ (n + 1)) α).symm) f'
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) α x))
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : 0 ≤ v 0) : 0 ≤ f' v := by
  let I := 𝓡∂ (n + 1)
  have hy0 : (extChartAt I α x) 0 = 0 := by
    have hc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
      simpa only [extChartAt_source] using hα
    simpa only [I, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_toFun] using
      (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hc).mp hx
  have hmin' : IsLocalMinOn (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) := by
    refine IsMinFilter.comp_of_tendsto ?_ (map_extChartAt_symm_nhdsWithin_range' (I := I) hα).le
    rwa [(extChartAt I α).left_inv hα]
  have hcone : v ∈ posTangentConeAt (range I) (extChartAt I α x) := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset (mem_range_self (chartAt _ α x))
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp only [mem_ofPred_eq, PiLp.add_apply, hy0, zero_add]
    exact hv
  exact hmin'.hasFDerivWithinAt_nonneg hf hcone

/-- At a boundary point an actual coordinate transition maps the closed inward half-space
`0 ≤ v 0` into itself: the normal coordinate of the image of an inward vector is nonnegative. -/
theorem tangentCoordChange_normal_nonneg {α β x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (hβ : x ∈ (extChartAt (𝓡∂ (n + 1)) β).source)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) :
    0 ≤ (tangentCoordChange (𝓡∂ (n + 1)) α β x v) 0 := by
  have hD := (PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0).hasFDerivAt.comp_hasFDerivWithinAt _
    (hasFDerivWithinAt_tangentCoordChange (I := 𝓡∂ (n + 1)) ⟨hα, hβ⟩)
  have hβ' : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) β).source := by
    simpa only [extChartAt_source] using hβ
  exact hasFDerivWithinAt_nonneg_of_isLocalMin
    (f := fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) β y).val 0) hx hα
    (Eventually.of_forall (normal_le_of_mem_boundary hx hβ')) hD hv

/-- At a boundary point an actual coordinate transition scales the normal coordinate by a
strictly positive number. No block structure or orientation identity is assumed. -/
theorem tangentCoordChange_normal_pos {α β x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M)
    (hα : x ∈ (extChartAt (𝓡∂ (n + 1)) α).source)
    (hβ : x ∈ (extChartAt (𝓡∂ (n + 1)) β).source) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : EuclideanSpace ℝ (Fin (n + 1)),
      (tangentCoordChange (𝓡∂ (n + 1)) α β x v) 0 = a * v 0 := by
  let I := 𝓡∂ (n + 1)
  let D := tangentCoordChange I α β x
  let π : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hnonneg (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) : 0 ≤ (D v) 0 :=
    tangentCoordChange_normal_nonneg hx hα hβ v hv
  let ν := EuclideanSpace.single (𝕜 := ℝ) (0 : Fin (n + 1)) 1
  let a := (D ν) 0
  have hfactor (v : EuclideanSpace ℝ (Fin (n + 1))) : (D v) 0 = a * v 0 :=
    Module.Dual.apply_eq_mul_apply_of_nonneg (EuclideanSpace.projₗ (𝕜 := ℝ) 0)
      (π.comp D : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) (x := ν) (by simp [ν])
      hnonneg v
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
