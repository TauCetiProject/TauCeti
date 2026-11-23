/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Frame covariant derivatives read in the charts of a finite bundle atlas

Let `A` be a finite bundle atlas of a real vector bundle `V → M`. The flat covariant derivative
`Manifold.frameCovariantDerivative` of a local frame over the trivialization of chart `i` is the
covariant derivative for which that frame is parallel. Read in chart `i`, through the preferred
trivializations of the tangent bundle and of `V` at the centre of the chart, it is the ordinary
derivative of the reading `A.coord i s` of the section.

## Main results

* `TauCeti.FiniteBundleAtlas.inCoordinates_frameCovariantDerivative`: the flat covariant derivative
  of the frame of chart `i` reads in chart `i` as the derivative of the reading of the section.
-/

public section

open Bundle Module Set
open scoped Manifold Topology

universe u

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- The reading in chart `i` of the flat covariant derivative of the frame of chart `i` is the
derivative of the reading of the section. -/
theorem inCoordinates_frameCovariantDerivative [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) (i : Fin A.n) {z : E} (hz : z ∈ A.image i)
    {s : Π x, V x} (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) F V (A.center i)
        ((A.chart i).symm z) (A.center i) ((A.chart i).symm z)
        (Manifold.frameCovariantDerivative 𝓘(ℝ, E) b (A.triv i) s ((A.chart i).symm z)) =
      fderiv ℝ (A.coord i s) z := by
  set x := (A.chart i).symm z
  set e := A.triv i
  have hxd : x ∈ A.dom i := A.symm_mem_dom hz
  have hx : x ∈ e.baseSet := A.dom_subset_baseSet i hxd
  have hxc : x ∈ (chartAt E (A.center i)).source := A.dom_subset_chart_source i hxd
  have hzt : z ∈ (extChartAt 𝓘(ℝ, E) (A.center i)).target := by
    simpa using A.closure_image_subset_target i (subset_closure hz)
  -- First, the frame derivative is the derivative of the fibre coordinate `g` of `s` in `e`,
  -- carried back to `V` by `e`.
  set g : M → F := fun y ↦ (e ⟨y, s y⟩).2
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g x := (e.mdifferentiableAt_section_iff _ s hx).1 hs
  have hcoeff (k : ι) : (fun y ↦ e.localFrameCoeff 𝓘(ℝ, E) b k y (s y)) =ᶠ[𝓝 x]
      fun y ↦ b.coord k (g y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrameCoeff_eq_coeff hy, Basis.coord_apply]
  rw [Manifold.frameCovariantDerivative_eq_symmL_comp b hg.hasMFDerivAt hcoeff hx]
  -- Second, the reading of `s` is `g` composed with the inverse of the extended chart, so its
  -- derivative is the chain rule composite.
  have hφ := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) hzt
  rw [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at hφ
  have hφz : (extChartAt 𝓘(ℝ, E) (A.center i)).symm z = x := by simp [x]
  have hcomp : A.coord i s = g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm := by
    ext y
    simp [g, coord_def, e]
  have hd := (hφz ▸ hg).hasMFDerivAt.comp z hφ.hasMFDerivAt
  -- The manifold derivatives between model spaces are maps `E →L[ℝ] F` up to the `TangentSpace`
  -- type synonyms, which `hasMFDerivAt_iff_hasFDerivAt` needs to see through.
  have hd' : HasFDerivAt (g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm)
      (show E →L[ℝ] F from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z)) z :=
    hasMFDerivAt_iff_hasFDerivAt.1 hd
  -- Third, the trivializations of the tangent bundle and of `V` at the centre cancel the chart
  -- derivative and `e` in the reading.
  rw [hcomp, hd'.fderiv, ContinuousLinearMap.inCoordinates,
    ← ContinuousLinearMap.comp_assoc, TangentBundle.symmL_trivializationAt hxc]
  have hzx : extChartAt 𝓘(ℝ, E) (A.center i) x = z := by
    simpa [x] using (A.chart i).right_inv (by simpa using hzt)
  rw [hzx]
  ext v
  -- Unfold the compositions; the tangent space of the model space is `E` by definition.
  change (trivializationAt F V (A.center i)).continuousLinearMapAt ℝ x
      ((trivializationAt F V (A.center i)).symmL ℝ x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm
          (range 𝓘(ℝ, E)) z v))) =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z v)
  rw [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  exact (trivializationAt F V (A.center i)).continuousLinearMapAt_symmL hx _

end FiniteBundleAtlas

end TauCeti
