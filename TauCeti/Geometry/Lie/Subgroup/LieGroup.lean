/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Manifold
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Lie-group structures from subgroup slice charts

A smooth ambient chart which identifies a subgroup with the zero transverse slice gives more than
a smooth atlas on the subgroup: the inclusion is smooth, and smoothness of a map into the subgroup
can be checked after composing with that inclusion. Consequently, the group operations inherited
from an ambient Lie group are smooth for the slice-chart manifold structure.

## Main results

* `Subgroup.contMDiff_subtypeVal_chartedSpaceOfIsSliceChart` proves that the subgroup inclusion is
  smooth.
* `Subgroup.contMDiff_iff_comp_subtypeVal_chartedSpaceOfIsSliceChart` characterizes smooth maps
  into the subgroup by their composites with the inclusion.
* `Subgroup.contMDiffMul_chartedSpaceOfIsSliceChart` makes inherited multiplication smooth.
* `Subgroup.lieGroup_chartedSpaceOfIsSliceChart` equips the charted subgroup with the inherited
  Lie-group operations.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

namespace Subgroup

open Set
open scoped ContDiff Manifold Topology

variable {E H G F F' : Type*} {n : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

variable (K : Subgroup G) (e : OpenPartialHomeomorph G (F × F'))
  (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
  (h1 : (1 : G) ∈ e.source)
  (he' : ContMDiffOn I 𝓘(ℝ, F × F') n e e.source)
  (he_symm : ContMDiffOn 𝓘(ℝ, F × F') I n e.symm e.target)

section ContMDiffMul

variable [ContMDiffMul I n G]

include he_symm in
/-- The inclusion of a subgroup carrying its slice-chart manifold structure into the ambient
smooth group is smooth. -/
theorem contMDiff_subtypeVal_chartedSpaceOfIsSliceChart :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    ContMDiff 𝓘(ℝ, F) I n (fun x : K ↦ (x : G)) := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  intro g
  rw [contMDiffAt_iff_source]
  have hchart : chartAt F g = preferredSliceChart K e he g :=
    chartedSpaceOfIsSliceChart_chartAt K e he h1 g
  have hg_target : preferredSliceChart K e he g g ∈
      (preferredSliceChart K e he g).target := by
    have hg := mem_extChartAt_target (I := 𝓘(ℝ, F)) g
    rw [extChartAt, hchart, OpenPartialHomeomorph.extend_target] at hg
    exact hg.1
  have hzero : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F') n
      (fun y : F ↦ (y, (0 : F'))) :=
    (contDiff_prodMk_left (0 : F')).contMDiff
  have hinv : ContMDiffAt 𝓘(ℝ, F × F') I n e.symm
      (preferredSliceChart K e he g g, 0) :=
    he_symm.contMDiffAt (e.open_target.mem_nhds (by simpa using hg_target))
  have hsmooth : ContMDiffAt 𝓘(ℝ, F) I n
      (fun y : F ↦ (g : G) * e.symm (y, 0)) (preferredSliceChart K e he g g) :=
    contMDiff_mul_left.contMDiffAt.comp _
      (hinv.comp (preferredSliceChart K e he g g) hzero.contMDiffAt)
  have hbase : extChartAt 𝓘(ℝ, F) g g = preferredSliceChart K e he g g := by
    simp [extChartAt, hchart]
  rw [hbase]
  apply hsmooth.contMDiffWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [nhdsWithin_le_nhds
        ((preferredSliceChart K e he g).open_target.mem_nhds hg_target)] with y hy_target
    have hy' : (y, (0 : F')) ∈ e.target := by
      simpa only [preferredSliceChart_target, Set.mem_preimage] using hy_target
    simpa [extChartAt, hchart, hy_target] using
      coe_preferredSliceChart_symm_apply K e he g hy'
  · exact ⟨_, rfl⟩

variable {E₀ H₀ M : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] {J : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace M] [ChartedSpace H₀ M]

/-- A map into a subgroup with its slice-chart manifold structure is smooth exactly when its
composite with the inclusion into the ambient smooth group is smooth. -/
theorem contMDiff_iff_comp_subtypeVal_chartedSpaceOfIsSliceChart (f : M → K) :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    let _ : IsManifold 𝓘(ℝ, F) n K :=
      isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
    ContMDiff J 𝓘(ℝ, F) n f ↔
      ContMDiff J I n ((fun x : K ↦ (x : G)) ∘ f) := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  let _ : IsManifold 𝓘(ℝ, F) n K :=
    isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  constructor
  · intro hf
    exact (contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm).comp hf
  · intro hf
    have hf_cont : Continuous f := by
      simpa only [Function.comp_apply] using hf.continuous.subtype_mk fun x ↦ (f x).property
    intro x
    rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source F (f x))]
    refine ⟨hf_cont.continuousAt, ?_⟩
    have htranslated : ContMDiffAt J I n
        (fun y ↦ ((f x : K) : G)⁻¹ * (f y : G)) x :=
      contMDiff_mul_left.contMDiffAt.comp x (hf x)
    have hcoordinate : ContMDiffAt J 𝓘(ℝ, F) n
        (fun y ↦ (e (((f x : K) : G)⁻¹ * (f y : G))).1) x :=
      contDiff_fst.contMDiff.contMDiffAt.comp x
        ((he'.contMDiffAt (e.open_source.mem_nhds (by simpa using h1))).comp x htranslated)
    apply hcoordinate.congr_of_eventuallyEq
    have hfx_source : f x ∈ (preferredSliceChart K e he (f x)).source := by
      simpa only [← chartedSpaceOfIsSliceChart_chartAt K e he h1] using
        mem_chart_source F (f x)
    filter_upwards [hf_cont.continuousAt
        ((preferredSliceChart K e he (f x)).open_source.mem_nhds
          hfx_source)] with y hy
    simp [extChartAt, chartedSpaceOfIsSliceChart_chartAt]

/-- Multiplication inherited by a subgroup is smooth for its slice-chart manifold structure. -/
theorem contMDiffMul_chartedSpaceOfIsSliceChart :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    let _ : IsManifold 𝓘(ℝ, F) n K :=
      isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
    ContMDiffMul 𝓘(ℝ, F) n K := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  let _ : IsManifold 𝓘(ℝ, F) n K :=
    isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  constructor
  apply (contMDiff_iff_comp_subtypeVal_chartedSpaceOfIsSliceChart
    K e he h1 he' he_symm _).2
  apply (((contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm).comp
    contMDiff_fst).mul
      ((contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm).comp
        contMDiff_snd)).congr
  intro p
  simp only [Function.comp_apply, Pi.mul_apply, Subgroup.coe_mul]

end ContMDiffMul

section LieGroup

variable [LieGroup I n G]

/-- A subgroup carrying the manifold structure induced by a smooth slice chart inherits the
Lie-group structure of the ambient Lie group. -/
theorem lieGroup_chartedSpaceOfIsSliceChart :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    let _ : IsManifold 𝓘(ℝ, F) n K :=
      isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
    LieGroup 𝓘(ℝ, F) n K := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  let _ : IsManifold 𝓘(ℝ, F) n K :=
    isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  let _ : ContMDiffMul 𝓘(ℝ, F) n K :=
    contMDiffMul_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  constructor
  apply (contMDiff_iff_comp_subtypeVal_chartedSpaceOfIsSliceChart
    K e he h1 he' he_symm _).2
  apply ((contMDiff_inv I n).comp
    (contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm)).congr
  intro x
  simp only [Function.comp_apply, Subgroup.coe_inv]

end LieGroup

end Subgroup
