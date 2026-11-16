/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Coordinate continuity of regular differential forms

The coordinate expression of a differential form is the fiber coordinate of its section in the
existing alternating tangent-bundle trivialization. Consequently even `C⁰` section regularity
implies coordinate continuity on the extended chart target, including boundary and corner points.
The zero set of a regular form is closed, as can be checked in local bundle trivializations. A
`C⁰` form evaluated on tangent vectors that converge in the tangent bundle converges to the value
on the limit vectors (`TauCeti.IsSmoothForm.tendsto_apply`), as can likewise be read off in the
trivialization at the limit point.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- On an extended chart target, the form's coordinate expression is exactly its section's
fiber coordinate in the preferred alternating-bundle trivialization. -/
theorem RoughForm.inChartAt_eq_trivializationAt (φ : RoughForm I M F k) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    φ.inChartAt α z =
      (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) α
          ⟨(extChartAt I α).symm z, φ ((extChartAt I α).symm z)⟩).2 := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp only [ContinuousAlternatingMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization]
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  rw [TangentBundle.symmL_trivializationAt hy, (extChartAt I α).right_inv hz]
  ext v
  rw [RoughForm.inChartAt_apply]
  rfl

/-- Within the model range near the image of the chart centre, the section's fiber coordinate in
the preferred alternating-bundle trivialization is the form's coordinate expression. -/
theorem RoughForm.trivializationAt_snd_eventuallyEq_inChartAt (φ : RoughForm I M F k) (α : M) :
    (fun z ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) α
        ⟨(extChartAt I α).symm z, φ ((extChartAt I α).symm z)⟩).2) =ᶠ[
          𝓝[range I] (extChartAt I α α)] φ.inChartAt α := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) α] with z hz
  exact (φ.inChartAt_eq_trivializationAt α hz).symm

/-- Every regular fixed-coefficient form, including a `C⁰` form, has continuous coordinate
coefficients on each preferred extended chart target. -/
theorem IsSmoothForm.continuousOn_inChartAt {n : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) (α : M) :
    ContinuousOn (φ.inChartAt α) (extChartAt I α).target := by
  let e := trivializationAt (E [⋀^Fin k]→L[ℝ] F)
    (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) α
  have hmap : MapsTo (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x))
      (extChartAt I α).source e.source := by
    intro x hx
    rw [e.mem_source]
    -- The section projects to x; reduce that projection before using the base-set formula.
    change x ∈ e.baseSet
    dsimp only [e]
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
      TangentBundle.trivializationAt_baseSet]
    refine ⟨?_, by simp⟩
    simpa only [extChartAt_source] using hx
  have hc : ContinuousOn (fun x ↦ (e ⟨x, φ x⟩).2) (extChartAt I α).source :=
    (e.continuousOn.comp hφ.contMDiff.continuous.continuousOn hmap).snd
  apply (hc.comp (continuousOn_extChartAt_symm α) (extChartAt I α).mapsTo_symm).congr
  intro z hz
  exact φ.inChartAt_eq_trivializationAt α hz

/-- The zero set of a regular differential form is closed, including for a continuous form.
Neither closedness of the form nor a Hausdorff base is needed. -/
theorem IsSmoothForm.isClosed_zeroSet {n : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) : IsClosed {x | φ x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  let e := trivializationAt (E [⋀^Fin k]→L[ℝ] F)
    (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x
  have hmap : MapsTo (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y))
      e.baseSet e.source := fun y hy ↦ e.mem_source.2 hy
  have hc : ContinuousOn (fun y ↦ (e ⟨y, φ y⟩).2) e.baseSet :=
    (e.continuousOn.comp hφ.contMDiff.continuous.continuousOn hmap).snd
  have heq (y : M) (hy : y ∈ e.baseSet) : (e ⟨y, φ y⟩).2 = 0 ↔ φ y = 0 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy]
    exact (e.continuousLinearEquivAt ℝ y hy).map_eq_zero_iff
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hxne : (e ⟨x, φ x⟩).2 ≠ 0 := mt (heq x hxbase).1 hx
  have hnear := (hc.continuousAt (e.open_baseSet.mem_nhds hxbase)).preimage_mem_nhds
    (isOpen_compl_singleton.mem_nhds hxne)
  filter_upwards [hnear, e.open_baseSet.mem_nhds hxbase] with y hy hybase
  exact mt (heq y hybase).2 hy

open Filter in
/-- **Evaluating a continuous form along converging tangent vectors.** If the base points `x i`
tend to `x₀` and, for each `j`, the tangent vectors `v i j ∈ T_(x i) M` tend to `v₀ j` in the
tangent bundle, then `φ (x i) (v i)` tends to `φ x₀ v₀` for every `C⁰` form `φ`. -/
theorem IsSmoothForm.tendsto_apply {φ : RoughForm I M F k} (hφ : IsSmoothForm I 0 φ) {ι : Type*}
    {l : Filter ι} {x : ι → M} {x₀ : M} {v : (i : ι) → Fin k → TangentSpace I (x i)}
    {v₀ : Fin k → TangentSpace I x₀} (hx : Tendsto x l (𝓝 x₀))
    (hv : ∀ j, Tendsto (fun i ↦ (⟨x i, v i j⟩ : TangentBundle I M)) l (𝓝 ⟨x₀, v₀ j⟩)) :
    Tendsto (fun i ↦ φ (x i) (v i)) l (𝓝 (φ x₀ v₀)) := by
  set T := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x₀
  -- The coordinate expression `A y` of `φ y` in the trivialization at `x₀` is continuous at `x₀`.
  set A : M → E [⋀^Fin k]→L[ℝ] F := fun y ↦
    ContinuousAlternatingMap.inCoordinates E F x₀ y x₀ y (φ y)
  have hA : ContinuousAt A x₀ :=
    ((continuousAt_continuousAlternatingMap_bundle
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y))).1
        (hφ.contMDiff.continuous.continuousAt)).2
  -- On the base set, `φ y` acts on vectors as `A y` acts on their coordinates.
  have hφA (y : M) (hy : y ∈ T.baseSet) (w : Fin k → TangentSpace I y) :
      φ y w = A y fun j ↦ T.continuousLinearMapAt ℝ y (w j) := by
    simp only [A, ContinuousAlternatingMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
      ContinuousLinearMap.id_apply]
    congr 1
    funext j
    exact (T.symmL_continuousLinearMapAt hy (w j)).symm
  have hcoord : Tendsto (fun i j ↦ T.continuousLinearMapAt ℝ (x i) (v i j)) l
      (𝓝 fun j ↦ T.continuousLinearMapAt ℝ x₀ (v₀ j)) :=
    tendsto_pi_nhds.2 fun j ↦ ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hv j)).2
  rw [hφA x₀ hx₀]
  refine ((continuous_eval.tendsto _).comp ((hA.tendsto.comp hx).prodMk_nhds hcoord)).congr'
    ((hx.eventually_mem (T.open_baseSet.mem_nhds hx₀)).mono fun i hi ↦ (hφA (x i) hi (v i)).symm)

end TauCeti
