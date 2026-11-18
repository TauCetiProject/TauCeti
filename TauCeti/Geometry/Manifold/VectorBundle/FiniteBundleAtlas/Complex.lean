/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Smoothness of the transitions of a finite bundle atlas over a complex curve

Let `A` be a finite bundle atlas of a vector bundle `V` over a smooth complex curve `M` (modelled on
`ℂ`, without boundary). Read in the charts of `A`, the chart transitions `τ` and the coordinate
changes `g` of `V` are real `C¹` on the overlaps. These are the regularity facts behind the weak
chain and Leibniz rules for the chart data of Sobolev sections on overlaps.

## Main results

* `TauCeti.FiniteBundleAtlas.contDiffOn_transition`: the chart transitions are real `C¹`
  (`ContDiffOn ℝ 1`) on the overlaps.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coordChangeL`: for a smooth vector bundle, the coordinate
  change from chart `i` to chart `i'`, read in chart `i'`, is real `C¹` on the overlap.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]

section Transition

variable {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] (A : FiniteBundleAtlas ℂ M F V)

/-- The chart transition from chart `i'` to chart `i` of a finite bundle atlas over a smooth complex
curve (modelled on `ℂ`) is real `C¹` (`ContDiffOn ℝ 1`) on the overlap. -/
theorem contDiffOn_transition (i i' : Fin A.n) :
    ContDiffOn ℝ 1 (A.transition i i') (A.overlap i i') := by
  refine ((contDiffOn_symm_trans_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (A.center i'))
    (IsManifold.chart_mem_maximalAtlas (A.center i))).mono fun y hy ↦ ?_).congr fun y hy ↦ ?_
  · obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hy
    have hs' := A.dom_subset_chart_source i' hx.2
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨(A.chart i').map_source hs', by
      rw [(A.chart i').left_inv hs']; exact A.dom_subset_chart_source i hx.1⟩
  · obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hy
    rw [A.transition_chart hx.2, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]

end Transition

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)

/-- The coordinate change of `V` from chart `i` to chart `i'`, read in chart `i'`, is `C¹` on the
overlap. -/
theorem contDiffOn_coordChangeL (i i' : Fin A.n) :
    ContDiffOn ℝ 1 (fun y ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) :
      F →L[ℝ] F)) (A.overlap i i') := by
  refine ((contMDiffOn_coordChangeL (IB := 𝓘(ℝ, ℂ)) (n := 1) (𝕜 := ℝ) (A.triv i)
    (A.triv i')).contDiffOn_comp_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (A.center i'))).mono fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hy
  have hs' := A.dom_subset_chart_source i' hx.2
  refine ⟨(A.chart i').map_source hs', ?_⟩
  rw [mem_preimage, (A.chart i').left_inv hs']
  exact ⟨A.dom_subset_baseSet i hx.1, A.dom_subset_baseSet i' hx.2⟩

end FiniteBundleAtlas

end TauCeti
