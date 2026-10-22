/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Level
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import Mathlib.Geometry.Manifold.Submersion

/-!
# The submersion normal form of a scalar function at a regular point

Let `f : M → ℝ` be a function on a boundaryless manifold modelled on a finite-dimensional real
space `E`, and let `x` be a regular point of `f`. Write

`D = fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)`

for the derivative of `f` in the preferred extended chart at `x`, `P` for the chosen projection of
`E` onto `ker D`, and `L = D.implicitCoordEquiv : E ≃L[ℝ] ℝ × ker D`, `L v = (D v, P v)`.
The implicit-function chart `Φ y = (f ((extChartAt I x).symm y) - f x, P (y - extChartAt I x x))`
of `f - f x`, restricted to the preferred chart target and to the neighbourhood where its
derivative stays invertible, and followed by `L⁻¹`, gives the chart
`TauCeti.scalarSubmersionChartAt` of `M` around `x`. Its extended coordinates are

`w ↦ L⁻¹ (f w - f x, P (extChartAt I x w - extChartAt I x x))`

(`TauCeti.scalarSubmersionChartAt_extend_apply`), so that `f` reads as `v ↦ D v + f x` in these
coordinates (`TauCeti.apply_scalarSubmersionChartAt_extend_symm`). With the chart `t ↦ t - f x` of
`ℝ`, this is the projection `Prod.fst ∘ L`: if `f` is `C^n` near `x`, `1 ≤ n`, then `f` is a `C^n`
submersion at `x` with complement `ker D` (`TauCeti.IsRegularPoint.isSubmersionAtOfComplement`).

On a regular level `f⁻¹(c)` the second coordinate is all that remains: the chart restricts on the
level to the preferred level chart `TauCeti.scalarRegularLevelChartAt`, built from the same `D`,
`P` and implicit-function chart, followed by the inverse of the same identification
`K : ker D ≃ (Fin (dim E - 1) → ℝ)` (`TauCeti.scalarSubmersionChartAt_extend_coe`), and the two
charts have the same domain on the level (`TauCeti.preimage_coe_scalarSubmersionChartAt_source`).
Charts of the sublevels `{f ≤ c}` adapted to their boundary level `f⁻¹(c)` are read off from this
comparison.

## Main declarations

* `TauCeti.scalarSubmersionChartAt`: the submersion chart of `f` at a regular point.
* `TauCeti.scalarSubmersionChartAt_source`, `TauCeti.scalarSubmersionChartAt_extend_apply`,
  `TauCeti.scalarSubmersionChartAt_extend_symm_apply` and
  `TauCeti.mem_scalarSubmersionChartAt_extend_target_iff`: the chart formulas.
* `TauCeti.scalarSubmersionChartAt_mem_maximalAtlas`: the chart is a `C^n` chart of `M`.
* `TauCeti.IsRegularPoint.isSubmersionAtOfComplement`: `f` is a `C^n` submersion at `x` with
  complement `ker D`.
* `TauCeti.scalarSubmersionChartAt_extend_coe` and
  `TauCeti.preimage_coe_scalarSubmersionChartAt_source`: on a regular level, the chart is the
  preferred level chart.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (the rank theorem for submersions) and Corollary 5.14.
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {x : M}

namespace ScalarSubmersion

private theorem closedComplemented_ker [FiniteDimensional ℝ E] (x : M) :
    (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker.ClosedComplemented :=
  (ContinuousLinearMap.isFredholm_of_finiteDimensional _).closedComplemented_ker

variable [I.Boundaryless]

/-- The equation `f - f x` read in the preferred extended chart at `x` has strict derivative the
preferred-chart derivative of `f`. -/
private theorem hasStrictFDerivAt_coord (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) :
    HasStrictFDerivAt (fun y ↦ f ((extChartAt I x).symm y) - f x)
      (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)) (extChartAt I x x) :=
  (hf.contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const _

private theorem range_eq_top (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).range = ⊤ :=
  LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm

variable [FiniteDimensional ℝ E] (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x)

/-- The implicit-function chart `y ↦ (f ((extChartAt I x).symm y) - f x, P (y - extChartAt I x x))`
of `f - f x` in the preferred extended chart at `x`. -/
private noncomputable abbrev implicitChart :
    OpenPartialHomeomorph E
      (ℝ × (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker) :=
  (hasStrictFDerivAt_coord hf).implicitToOpenPartialHomeomorphOfComplemented _ _ (range_eq_top hx)
    (closedComplemented_ker x)

/-- The domain on which the implicit-function chart is used: its own source, inside the preferred
chart target and the neighbourhood where its derivative stays invertible. -/
private noncomputable abbrev domain : Set E :=
  (implicitChart hf hx).source ∩ (extChartAt I x).target ∩
    (hasStrictFDerivAt_coord hf).implicitCoordSource (range_eq_top hx) (closedComplemented_ker x)

private theorem isOpen_domain : IsOpen (domain hf hx) :=
  ((implicitChart hf hx).open_source.inter (isOpen_extChartAt_target x)).inter
    ((hasStrictFDerivAt_coord hf).isOpen_implicitCoordSource _ _)

/-- The domain lies in the preferred extended chart target, hence over the preferred chart
target. -/
private theorem domain_subset : domain hf hx ⊆ I.symm ⁻¹' (chartAt H x).target :=
  fun _ hp ↦ ((extChartAt_target (I := I) x).subset hp.1.2).1

/-- The derivative `L v = (D v, P v)` of the implicit-function chart at the base point. -/
private noncomputable abbrev coordEquiv :
    E ≃L[ℝ] ℝ × (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker :=
  (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).implicitCoordEquiv (range_eq_top hx)
    (closedComplemented_ker x)

/-- The implicit-function chart on its domain, followed by `L⁻¹`, as a chart of `E`. -/
private noncomputable abbrev coordChart : OpenPartialHomeomorph E E :=
  ((implicitChart hf hx).restrOpen (domain hf hx) (isOpen_domain hf hx)).transHomeomorph
    (coordEquiv hx).symm.toHomeomorph

/-- The submersion chart on the self-modelled copy of `M`. -/
private noncomputable abbrev modelChart : OpenPartialHomeomorph (BoundarylessModel I M) E :=
  (chartAt E (BoundarylessModel.homeomorph I M x)).trans (coordChart hf hx)

private theorem coe_coordChart :
    ⇑(coordChart hf hx) = (coordEquiv hx).symm ∘ implicitChart hf hx := by
  rw [OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.coe_restrOpen,
    ContinuousLinearEquiv.coe_toHomeomorph]

private theorem coe_coordChart_symm :
    ⇑(coordChart hf hx).symm = (implicitChart hf hx).symm ∘ coordEquiv hx := by
  rw [OpenPartialHomeomorph.transHomeomorph_symm_apply, OpenPartialHomeomorph.coe_restrOpen_symm,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, ContinuousLinearEquiv.symm_symm]

private theorem modelChart_apply (y : BoundarylessModel I M) :
    modelChart hf hx y = (coordEquiv hx).symm
      (implicitChart hf hx (extChartAt I x ((BoundarylessModel.homeomorph I M).symm y))) := by
  simp only [OpenPartialHomeomorph.coe_trans, coe_coordChart, comp_apply,
    BoundarylessModel.chartAt_apply, Homeomorph.symm_apply_apply]

private theorem modelChart_symm_apply (v : E) :
    (BoundarylessModel.homeomorph I M).symm ((modelChart hf hx).symm v) =
      (extChartAt I x).symm ((implicitChart hf hx).symm (coordEquiv hx v)) := by
  simp only [OpenPartialHomeomorph.coe_trans_symm, coe_coordChart_symm, comp_apply,
    BoundarylessModel.chartAt_symm_apply, Homeomorph.symm_apply_apply]

/-- The source of the restricted implicit-function chart is the domain, which lies in the source of
the implicit-function chart. -/
private theorem coordChart_source : (coordChart hf hx).source = domain hf hx := by
  rw [OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.2 fun _ hp ↦ hp.1.1

private theorem mem_modelChart_source_iff (y : BoundarylessModel I M) :
    y ∈ (modelChart hf hx).source ↔
      (BoundarylessModel.homeomorph I M).symm y ∈ (chartAt H x).source ∧
        extChartAt I x ((BoundarylessModel.homeomorph I M).symm y) ∈ domain hf hx := by
  simp only [OpenPartialHomeomorph.trans_source, coordChart_source, BoundarylessModel.chartAt_eq,
    BoundarylessModel.chart_source, BoundarylessModel.chart_apply, Homeomorph.symm_apply_apply,
    extChartAt_coe, comp_apply, mem_inter_iff, mem_preimage]

private theorem mem_modelChart_target_iff (v : E) :
    v ∈ (modelChart hf hx).target ↔
      coordEquiv hx v ∈ (implicitChart hf hx).target ∧
        (implicitChart hf hx).symm (coordEquiv hx v) ∈ domain hf hx := by
  simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.transHomeomorph_target,
    OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, ContinuousLinearEquiv.symm_symm,
    coe_coordChart_symm, BoundarylessModel.chartAt_eq, BoundarylessModel.chart_target,
    Homeomorph.symm_apply_apply, comp_apply, mem_inter_iff, mem_preimage]
  -- The target of the restricted implicit-function chart is cut out by the domain, which lies over
  -- the preferred chart target.
  exact and_iff_left_of_imp fun h ↦ domain_subset hf hx h.2

/-- In the submersion chart, `f - f x` is the first coordinate of `L`. -/
private theorem apply_modelChart_symm {v : E} (hv : v ∈ (modelChart hf hx).target) :
    f ((BoundarylessModel.homeomorph I M).symm ((modelChart hf hx).symm v)) - f x =
      (coordEquiv hx v).1 := by
  rw [modelChart_symm_apply]
  have h := congrArg Prod.fst
    ((implicitChart hf hx).right_inv ((mem_modelChart_target_iff hf hx v).1 hv).1)
  rwa [(hasStrictFDerivAt_coord hf).implicitToOpenPartialHomeomorphOfComplemented_fst] at h

/-- The submersion chart is `C^n` wherever `f` is. -/
private theorem contMDiffAt_modelChart {n : ℕ∞ω} [IsManifold I n M] {y : BoundarylessModel I M}
    (hy : y ∈ (modelChart hf hx).source)
    (hfy : ContMDiffAt I 𝓘(ℝ) n f ((BoundarylessModel.homeomorph I M).symm y)) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (modelChart hf hx) y := by
  obtain ⟨hy₁, -⟩ := (mem_modelChart_source_iff hf hx y).1 hy
  have hg : ContDiffAt ℝ n (fun z ↦ f ((extChartAt I x).symm z) - f x)
      (extChartAt I x ((BoundarylessModel.homeomorph I M).symm y)) :=
    ((contMDiffAt_iff_contDiffAt_comp_extend_symm (IsManifold.chart_mem_maximalAtlas x) hy₁).1
      hfy).sub contDiffAt_const
  have hcoord : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (coordChart hf hx)
      (chartAt E (BoundarylessModel.homeomorph I M x) y) := by
    rw [contMDiffAt_iff_contDiffAt, coe_coordChart, BoundarylessModel.chartAt_apply,
      Homeomorph.symm_apply_apply]
    exact (coordEquiv hx).symm.contDiff.contDiffAt.comp _
      ((hasStrictFDerivAt_coord hf).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented hg _ _)
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (chartAt E (BoundarylessModel.homeomorph I M x)) y :=
    contMDiffOn_chart.contMDiffAt ((chartAt E _).open_source.mem_nhds hy.1)
  rw [OpenPartialHomeomorph.coe_trans]
  exact hcoord.comp y hchart

/-- The inverse of the submersion chart is `C^n` wherever `f` is, when `1 ≤ n`. -/
private theorem contMDiffAt_modelChart_symm {n : ℕ∞ω} [IsManifold I n M] (hn : 1 ≤ n) {v : E}
    (hv : v ∈ (modelChart hf hx).target)
    (hfv : ContMDiffAt I 𝓘(ℝ) n f
      ((BoundarylessModel.homeomorph I M).symm ((modelChart hf hx).symm v))) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (modelChart hf hx).symm v := by
  obtain ⟨hvΦ, hvD⟩ := (mem_modelChart_target_iff hf hx v).1 hv
  set p := (implicitChart hf hx).symm (coordEquiv hx v)
  have hp : (extChartAt I x).symm p ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hvD.1.2
  rw [modelChart_symm_apply] at hfv
  have hg : ContDiffAt ℝ n (fun z ↦ f ((extChartAt I x).symm z) - f x) p := by
    have h := ((contMDiffAt_iff_contDiffAt_comp_extend_symm (IsManifold.chart_mem_maximalAtlas x)
      hp).1 hfv).sub (contDiffAt_const (c := f x))
    rwa [← extChartAt, (extChartAt I x).right_inv hvD.1.2] at h
  have hcoord : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (coordChart hf hx).symm v := by
    rw [contMDiffAt_iff_contDiffAt, coe_coordChart_symm]
    exact (HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem
      (hasStrictFDerivAt_coord hf) _ _ hvΦ hvD.2
      ((hg.differentiableAt (zero_lt_one.trans_le hn).ne').hasFDerivAt) hg).comp v
      (coordEquiv hx).contDiff.contDiffAt
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n
      (chartAt E (BoundarylessModel.homeomorph I M x)).symm p := by
    refine contMDiffOn_chart_symm.contMDiffAt ((chartAt E _).open_target.mem_nhds ?_)
    rw [BoundarylessModel.chartAt_eq, BoundarylessModel.chart_target, Homeomorph.symm_apply_apply]
    exact domain_subset hf hx hvD
  rw [OpenPartialHomeomorph.coe_trans_symm]
  exact hchart.comp v hcoord

/-- The submersion chart, restricted to an open set on which `f` is `C^n`, is a chart of the `C^n`
maximal atlas of the self-modelled copy of `M`. -/
private theorem restrOpen_modelChart_mem_maximalAtlas {n : ℕ∞ω} [IsManifold I n M] (hn : 1 ≤ n)
    {U : Set (BoundarylessModel I M)} (hU : IsOpen U)
    (hfU : ∀ y ∈ U, ContMDiffAt I 𝓘(ℝ) n f ((BoundarylessModel.homeomorph I M).symm y)) :
    (modelChart hf hx).restrOpen U hU ∈
      IsManifold.maximalAtlas 𝓘(ℝ, E) n (BoundarylessModel I M) := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ (fun y hy ↦ ?_) fun v hv ↦ ?_
  · exact (contMDiffAt_modelChart hf hx hy.1 (hfU y hy.2)).contMDiffWithinAt
  · exact (contMDiffAt_modelChart_symm hf hx hn hv.1 (hfU _ hv.2)).contMDiffWithinAt

end ScalarSubmersion

open ScalarSubmersion

variable [I.Boundaryless] [FiniteDimensional ℝ E]

section Chart

variable (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x)

/-- The submersion chart of a scalar function `f` at a regular point `x`. Writing `D` for the
derivative of `f` in the preferred extended chart at `x`, `P` for the chosen projection onto
`ker D` and `L v = (D v, P v)`, its extended coordinates are
`w ↦ L⁻¹ (f w - f x, P (extChartAt I x w - extChartAt I x x))`
(`TauCeti.scalarSubmersionChartAt_extend_apply`), in which `f` reads as `v ↦ D v + f x`. -/
noncomputable def scalarSubmersionChartAt : OpenPartialHomeomorph M H :=
  BoundarylessModel.originalChart I (modelChart hf hx)

/-- The extended coordinates of the submersion chart at `x`: a point `w` is read as
`L⁻¹ (f w - f x, P (extChartAt I x w - extChartAt I x x))`, where `D` is the preferred-chart
derivative of `f` at `x`, `P` the chosen projection onto `ker D` and `L v = (D v, P v)`. -/
theorem scalarSubmersionChartAt_extend_apply {w : M} (hw : w ∈ (chartAt H x).source) :
    (scalarSubmersionChartAt hf hx).extend I w =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      let hD' : D.range = ⊤ := LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm
      (D.implicitCoordEquiv hD' D.isFredholm_of_finiteDimensional.closedComplemented_ker).symm
        (f w - f x, Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
          (extChartAt I x w - extChartAt I x x)) := by
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_extend_apply, modelChart_apply,
    BoundarylessModel.homeomorph_symm_apply, BoundarylessModel.homeomorph_apply,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply,
    PartialEquiv.left_inv _ (by rwa [extChartAt_source])]

/-- The source of the submersion chart at `x`: points of the preferred chart at `x` whose extended
coordinates lie in the source of the implicit-function chart of `f - f x` and in the neighbourhood
where its derivative stays invertible. -/
theorem scalarSubmersionChartAt_source :
    (scalarSubmersionChartAt hf hx).source =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I x).symm y) - f x) D
          (extChartAt I x x) :=
        (hf.contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const _
      let hD' : D.range = ⊤ := LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      {w : M | w ∈ (chartAt H x).source ∧ extChartAt I x w ∈
        (hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).source ∩
          hD.implicitCoordSource hD' hker} := by
  ext w
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_source, mem_preimage,
    mem_modelChart_source_iff, Homeomorph.symm_apply_apply]
  refine and_congr_right fun hw ↦ ?_
  have hwt : extChartAt I x w ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (by rwa [extChartAt_source])
  simp only [domain, mem_inter_iff, hwt, and_true]

/-- The point `x` lies in the source of its submersion chart. -/
theorem mem_scalarSubmersionChartAt_source : x ∈ (scalarSubmersionChartAt hf hx).source := by
  rw [scalarSubmersionChartAt_source]
  exact ⟨mem_chart_source H x,
    (hasStrictFDerivAt_coord hf).mem_implicitToOpenPartialHomeomorphOfComplemented_source _ _,
    (hasStrictFDerivAt_coord hf).mem_implicitCoordSource _ _⟩

/-- The submersion chart at `x` is centred at `x`. -/
theorem scalarSubmersionChartAt_extend_self : (scalarSubmersionChartAt hf hx).extend I x = 0 := by
  rw [scalarSubmersionChartAt_extend_apply hf hx (mem_chart_source H x)]
  dsimp only
  rw [sub_self, sub_self, map_zero, Prod.mk_zero_zero, map_zero]

/-- The inverse extended submersion chart at `x` is the inverse preferred extended chart of `M` at
`x` applied to the inverse implicit-function chart of `f - f x`, after `L`. -/
theorem scalarSubmersionChartAt_extend_symm_apply (v : E) :
    ((scalarSubmersionChartAt hf hx).extend I).symm v =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I x).symm y) - f x) D
          (extChartAt I x x) :=
        (hf.contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const _
      let hD' : D.range = ⊤ := LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      (extChartAt I x).symm ((hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).symm
        (D.implicitCoordEquiv hD' hker v)) := by
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_extend_symm_apply,
    modelChart_symm_apply]

/-- The target of the extended submersion chart at `x`: vectors `v` such that `L v` lies in the
target of the implicit-function chart of `f - f x`, whose inverse lies in the preferred chart
target and in the neighbourhood where the derivative of that chart stays invertible. -/
theorem mem_scalarSubmersionChartAt_extend_target_iff (v : E) :
    v ∈ ((scalarSubmersionChartAt hf hx).extend I).target ↔
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I x).symm y) - f x) D
          (extChartAt I x x) :=
        (hf.contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const _
      let hD' : D.range = ⊤ := LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      let L := D.implicitCoordEquiv hD' hker
      let Φ := hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker
      L v ∈ Φ.target ∧ Φ.symm (L v) ∈ (extChartAt I x).target ∧
        Φ.symm (L v) ∈ hD.implicitCoordSource hD' hker := by
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_extend_target,
    mem_modelChart_target_iff]
  simp only [domain, mem_inter_iff, and_assoc]
  rw [and_congr_right_iff]
  intro hv
  exact and_iff_right_of_imp fun _ ↦
    (implicitChart hf hx).map_target hv

/-- **The submersion normal form.** In the submersion chart at `x`, `f` reads as `v ↦ D v + f x`,
where `D` is the derivative of `f` in the preferred extended chart at `x`. -/
theorem apply_scalarSubmersionChartAt_extend_symm {v : E}
    (hv : v ∈ ((scalarSubmersionChartAt hf hx).extend I).target) :
    f (((scalarSubmersionChartAt hf hx).extend I).symm v) =
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v + f x := by
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_extend_target] at hv
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_extend_symm_apply,
    ← sub_eq_iff_eq_add, apply_modelChart_symm hf hx hv,
    ContinuousLinearMap.implicitCoordEquiv_apply]

/-- If `f` is `C^n` on the source of its submersion chart at `x`, `1 ≤ n`, then this chart belongs
to the `C^n` maximal atlas of `M`. -/
theorem scalarSubmersionChartAt_mem_maximalAtlas {n : ℕ∞ω} [IsManifold I n M] (hn : 1 ≤ n)
    (hfn : ∀ y ∈ (scalarSubmersionChartAt hf hx).source, ContMDiffAt I 𝓘(ℝ) n f y) :
    scalarSubmersionChartAt hf hx ∈ IsManifold.maximalAtlas I n M := by
  rw [scalarSubmersionChartAt, BoundarylessModel.originalChart_mem_maximalAtlas_iff]
  have hfy : ∀ y ∈ (modelChart hf hx).source,
      ContMDiffAt I 𝓘(ℝ) n f ((BoundarylessModel.homeomorph I M).symm y) := fun y hy ↦ hfn _ <| by
    rwa [scalarSubmersionChartAt, BoundarylessModel.originalChart_source, mem_preimage,
      Homeomorph.apply_symm_apply]
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ (fun y hy ↦ ?_) fun v hv ↦ ?_
  · exact (contMDiffAt_modelChart hf hx hy (hfy y hy)).contMDiffWithinAt
  · exact (contMDiffAt_modelChart_symm hf hx hn hv
      (hfy _ ((modelChart hf hx).map_target hv))).contMDiffWithinAt

/-- **A regular point of a scalar function is a submersion point.** If `f` is `C^n` near a regular
point `x`, with `1 ≤ n`, then `f` is a `C^n` submersion at `x` with complement the kernel of the
derivative `D` of `f` in the preferred extended chart at `x`. In the submersion chart at `x`,
restricted to where `f` is `C^n`, and the chart `t ↦ t - f x` of `ℝ`, the map `f` is the
projection `Prod.fst ∘ L`, where `L v = (D v, P v)` for the chosen projection `P` onto `ker D`. -/
theorem IsRegularPoint.isSubmersionAtOfComplement {n : ℕ∞ω} [IsManifold I n M]
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (hn : 1 ≤ n) (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) n f y) :
    Manifold.IsSubmersionAtOfComplement
      (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker I 𝓘(ℝ) n f x := by
  obtain ⟨U, hfU, hU, hxU⟩ := eventually_nhds_iff.1 hfn
  have hf : ContMDiffAt I 𝓘(ℝ) 1 f x := (hfU x hxU).of_le hn
  have hU' : IsOpen ((BoundarylessModel.homeomorph I M).symm ⁻¹' U) :=
    hU.preimage (BoundarylessModel.homeomorph I M).symm.continuous
  set φ := (modelChart hf hx).restrOpen _ hU'
  -- The chart `t ↦ t - f x` of `ℝ`.
  have hsub : (Homeomorph.subRight (f x)).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ) n ℝ :=
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      (contMDiffOn_iff_contDiffOn.2 (contDiff_id.sub contDiff_const).contDiffOn)
      (contMDiffOn_iff_contDiffOn.2 (contDiff_id.add contDiff_const).contDiffOn)
  have hφ : ⇑φ.symm = (modelChart hf hx).symm := OpenPartialHomeomorph.coe_restrOpen_symm _ _
  refine Manifold.IsSubmersionAtOfComplement.mk_of_charts (coordEquiv hx)
    (BoundarylessModel.originalChart I φ) (Homeomorph.subRight (f x)).toOpenPartialHomeomorph
    ?_ (mem_univ _) ?_ hsub (fun _ _ ↦ mem_univ _) fun v hv ↦ ?_
  · rw [BoundarylessModel.originalChart_source, mem_preimage]
    refine ⟨?_, by rwa [mem_preimage, Homeomorph.symm_apply_apply]⟩
    have h := mem_scalarSubmersionChartAt_source hf hx
    rwa [scalarSubmersionChartAt, BoundarylessModel.originalChart_source, mem_preimage] at h
  · exact (BoundarylessModel.originalChart_mem_maximalAtlas_iff I φ n).2
      (restrOpen_modelChart_mem_maximalAtlas hf hx hn hU' fun y hy ↦ hfU _ hy)
  · rw [BoundarylessModel.originalChart_extend_target] at hv
    rw [comp_apply, comp_apply, BoundarylessModel.originalChart_extend_symm_apply, hφ,
      OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_comp]
    exact apply_modelChart_symm hf hx hv.1

end Chart

/-! ### The submersion chart on a regular level -/

variable {c : ℝ} (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ) f c)

/-- **On a regular level, the submersion chart is the level chart.** At a point `x` of a regular
level `f⁻¹(c)`, the extended submersion chart sends each point `w` of the level in the preferred
chart at `x` to the kernel vector `K⁻¹ (scalarRegularLevelChartAt x w)` of the derivative `D` of
`f` in the preferred extended chart at `x`, where `K : ker D ≃ (Fin (dim E - 1) → ℝ)` is the
identification used by the level atlas. -/
theorem scalarSubmersionChartAt_extend_coe (x : {x : M // f x = c}) {w : {x : M // f x = c}}
    (hw : (w : M) ∈ (chartAt H (x : M)).source) :
    (scalarSubmersionChartAt (hf x x.2) (hreg.isRegularPoint x.2)).extend I w =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      ((D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm).symm
          (scalarRegularLevelChartAt hf hreg x w) : E) := by
  rw [scalarSubmersionChartAt_extend_apply _ _ hw, scalarRegularLevelChartAt_apply]
  dsimp only
  rw [ContinuousLinearEquiv.symm_apply_apply, w.2, x.2, sub_self,
    ContinuousLinearMap.implicitCoordEquiv_symm_apply_zero_mk]

/-- **On a regular level, the submersion chart and the level chart have the same domain.** A point
of a regular level `f⁻¹(c)` lies in the source of the submersion chart at a point `x` of the level
exactly when it lies in the source of the preferred level chart at `x`. -/
theorem preimage_coe_scalarSubmersionChartAt_source (x : {x : M // f x = c}) :
    Subtype.val ⁻¹' (scalarSubmersionChartAt (hf x x.2) (hreg.isRegularPoint x.2)).source =
      (scalarRegularLevelChartAt hf hreg x).source := by
  have hfun : (fun y ↦ f ((extChartAt I (x : M)).symm y) - f x) =
      fun y ↦ f ((extChartAt I (x : M)).symm y) - c := by
    rw [x.2]
  have hD := hasStrictFDerivAt_coord (hf x x.2)
  have hD' := range_eq_top (hreg.isRegularPoint x.2)
  have hker := closedComplemented_ker (f := f) (I := I) (x : M)
  rw [scalarSubmersionChartAt_source, scalarRegularLevelChartAt_source]
  dsimp only
  rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_congr hD (hfun ▸ hD) hfun rfl
      hD' hker,
    HasStrictFDerivAt.implicitCoordSource_congr hD (hfun ▸ hD) hfun rfl hD' hker]
  -- Both sides are now the same condition on the underlying point of `M`.
  rfl

end TauCeti
