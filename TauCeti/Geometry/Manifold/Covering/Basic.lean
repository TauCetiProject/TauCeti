/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Covering.Basic

/-!
# Smooth structures on covering spaces

A covering map into a charted space pulls the charted structure back to its total space.  The
preferred chart at a point first applies the covering map on a sheet where it is a homeomorphism,
then applies the preferred chart of the base.  This construction depends on the covering map, so
it is provided as an explicit structure rather than as a global instance.

The resulting structure makes the total space a manifold of the same regularity as the base and
makes the covering projection a local diffeomorphism.  Conversely, any manifold structure for
which the projection is a local diffeomorphism is compatible with the induced structure.

## Main declarations

* `IsCoveringMap.inducedChartedSpace`: the charted structure pulled back along a covering map.
* `IsCoveringMap.induced_isManifold`: the induced structure is a manifold structure.
* `IsCoveringMap.induced_isLocalDiffeomorph`: the projection is a local diffeomorphism.
* `IsCoveringMap.induced_unique`: uniqueness up to compatibility of atlases.
* `ContMDiff.of_comp_isCoveringMap`: a continuous lift of a smooth map is smooth.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

namespace IsCoveringMap

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace X]

private def inducedChart {p : X → M} (hp : IsCoveringMap p) (x : X) :
    OpenPartialHomeomorph X H :=
  (hp.isLocalHomeomorph.localInverseAt x).symm.trans (chartAt H (p x))

/-- The charted-space structure on the total space induced by a covering map.  This is a
constructor rather than an instance because the same topological space can carry several covering
presentations. -/
@[instance_reducible]
def inducedChartedSpace (H : Type*) [TopologicalSpace H] [ChartedSpace H M]
    {p : X → M} (hp : IsCoveringMap p) : ChartedSpace H X where
  atlas := Set.range (hp.inducedChart (H := H))
  chartAt := hp.inducedChart (H := H)
  mem_chart_source x := by
    simp [inducedChart]
  chart_mem_atlas x := mem_range_self x

private theorem inducedChart_eqOn {p : X → M} (hp : IsCoveringMap p) (x : X) :
    EqOn (hp.inducedChart (H := H) x) (chartAt H (p x) ∘ p)
      (hp.inducedChart (H := H) x).source := by
  intro y hy
  simp only [inducedChart, OpenPartialHomeomorph.trans_apply,
    hp.isLocalHomeomorph.localInverseAt_symm]
  rfl

/-- The preferred chart for the induced charted structure is the lifted preferred chart of the
base. -/
theorem inducedChartedSpace_chartAt {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) (x : X) :
    EqOn (chartAt H x) (chartAt H (p x) ∘ p) (chartAt H x).source := by
  subst c
  exact hp.inducedChart_eqOn x

private theorem induced_transition_eqOn {p : X → M} (hp : IsCoveringMap p) (x y : X) :
    EqOn ((chartAt H (p x)).symm.trans (chartAt H (p y)))
      ((hp.inducedChart (H := H) x).symm.trans (hp.inducedChart (H := H) y))
      ((hp.inducedChart (H := H) x).symm.trans
        (hp.inducedChart (H := H) y)).source := by
  intro z hz
  simp only [inducedChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    at hz
  simp only [inducedChart, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    hp.isLocalHomeomorph.localInverseAt_symm, OpenPartialHomeomorph.symm_symm]
  rw [hp.isLocalHomeomorph.apply_localInverseAt_of_mem]
  exact hz.1.2

private theorem induced_transition_source_subset {p : X → M} (hp : IsCoveringMap p) (x y : X) :
    ((hp.inducedChart (H := H) x).symm.trans
        (hp.inducedChart (H := H) y)).source ⊆
      ((chartAt H (p x)).symm.trans (chartAt H (p y))).source := by
  intro z hz
  simp only [inducedChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    at hz ⊢
  refine ⟨hz.1.1, ?_⟩
  rw [← hp.isLocalHomeomorph.apply_localInverseAt_of_mem hz.1.2]
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply, hp.isLocalHomeomorph.localInverseAt_symm,
    OpenPartialHomeomorph.symm_symm] using hz.2.2

/-- Pulling back the charts of a manifold along a covering map makes the total space a manifold
of the same regularity. -/
theorem induced_isManifold {n : WithTop ℕ∞} [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) :
    IsManifold I n X := by
  subst c
  let _ : ChartedSpace H X := hp.inducedChartedSpace H
  refine { compatible := ?_ }
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  let b := (chartAt H (p x)).symm.trans (chartAt H (p y))
  have hb : b ∈ contDiffGroupoid n I :=
    StructureGroupoid.compatible (contDiffGroupoid n I)
      (chart_mem_atlas H (p x)) (chart_mem_atlas H (p y))
  have hr := (contDiffGroupoid n I).restr_mem_of_eqOn hb
    ((hp.inducedChart x).symm.trans (hp.inducedChart y)).open_source
    (hp.induced_transition_eqOn x y)
    (inter_subset_left.trans (hp.induced_transition_source_subset x y))
  rw [OpenPartialHomeomorph.restr_eq_of_source_subset (subset_refl _)] at hr
  exact hr

private def projectionChart (H : Type*) [TopologicalSpace H] [ChartedSpace H M]
    [ChartedSpace H X] {p : X → M} (x : X) :
    OpenPartialHomeomorph X M :=
  (chartAt H x).trans (chartAt H (p x)).symm

private theorem projectionChart_eqOn {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) (x : X) :
    EqOn p (projectionChart (M := M) (X := X) (p := p) H x)
      (projectionChart (M := M) (X := X) (p := p) H x).source := by
  subst c
  let _ : ChartedSpace H X := hp.inducedChartedSpace H
  intro y hy
  have hyp : p y ∈ (chartAt H (p x)).source := by
    simpa only [projectionChart, inducedChartedSpace, inducedChart,
      OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      hp.isLocalHomeomorph.localInverseAt_symm, OpenPartialHomeomorph.symm_symm] using hy.1.2
  change p y = (chartAt H (p x)).symm (chartAt H x y)
  rw [hp.inducedChartedSpace_chartAt rfl x hy.1, Function.comp_apply]
  exact ((chartAt H (p x)).left_inv hyp).symm

private theorem projectionChart_self_mem_source {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) (x : X) :
    x ∈ (projectionChart (M := M) (X := X) (p := p) H x).source := by
  subst c
  let _ : ChartedSpace H X := hp.inducedChartedSpace H
  simp only [projectionChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    mem_chart_source, true_and]
  change (hp.inducedChart x) x ∈ (chartAt H (p x)).target
  rw [hp.inducedChart_eqOn x (mem_chart_source H x)]
  exact (chartAt H (p x)).map_source (mem_chart_source H (p x))

private def projectionPartialDiffeomorph {n : WithTop ℕ∞} [IsManifold I n M]
    [c : ChartedSpace H X] [IsManifold I n X] {p : X → M} (hp : IsCoveringMap p)
    (hc : c = hp.inducedChartedSpace H) (x : X) : PartialDiffeomorph I I X M n := by
  let q := projectionChart (M := M) (X := X) (p := p) H x
  have hq : ContMDiffOn I I n q q.source :=
    contMDiffOn_chart_symm.comp (contMDiffOn_chart.mono inter_subset_left)
      inter_subset_right
  have hq_symm : ContMDiffOn I I n q.symm q.target :=
    contMDiffOn_chart_symm.comp (contMDiffOn_chart.mono inter_subset_left)
      inter_subset_right
  have hqp : EqOn p q q.source := projectionChart_eqOn hp hc x
  exact
    { toFun := p
      invFun := q.symm
      source := q.source
      target := q.target
      map_source' := fun y hy ↦ hqp hy ▸ q.map_source hy
      map_target' := fun {_} hz ↦ q.map_target hz
      left_inv' := fun y hy ↦ by rw [hqp hy]; exact q.left_inv hy
      right_inv' := fun z hz ↦ by
        rw [hqp (q.symm.map_source hz)]
        exact q.right_inv hz
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := hq.congr hqp
      contMDiffOn_invFun := hq_symm }

/-- With the induced charted structure, a covering projection is a local diffeomorphism. -/
theorem induced_isLocalDiffeomorph {n : WithTop ℕ∞} [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) :
    IsLocalDiffeomorph I I n p := by
  have hX : IsManifold I n X := hp.induced_isManifold hc
  let _ := hX
  rw [isLocalDiffeomorph_iff]
  intro x
  exact (projectionPartialDiffeomorph hp hc x).isLocalDiffeomorphAt I I n
    (projectionChart_self_mem_source hp hc x)

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- A continuous map is smooth within a set at a point when its composition with a local
diffeomorphism is smooth there. -/
theorem _root_.ContMDiffWithinAt.of_comp_isLocalDiffeomorph {n : WithTop ℕ∞}
    [ChartedSpace H X] {p : X → M} {f : N → X} {s : Set N} {y : N}
    (hp : IsLocalDiffeomorphAt I I n p (f y)) (hf : ContinuousWithinAt f s y)
    (hpf : ContMDiffWithinAt J I n (p ∘ f) s y) : ContMDiffWithinAt J I n f s y := by
  have hcomp : ContMDiffWithinAt J I n (hp.localInverse ∘ (p ∘ f)) s y :=
    hp.contMDiffAt_localInverse.comp_contMDiffWithinAt y hpf
  have heq : Filter.EventuallyEq (nhdsWithin y s) (hp.localInverse ∘ (p ∘ f)) f := by
    filter_upwards [hf.preimage_mem_nhdsWithin
      (hp.localInverse.open_target.mem_nhds hp.localInverse_mem_target)] with z hz
    exact hp.localInverse_left_inv hz
  exact hcomp.congr_of_eventuallyEq heq.symm
    (hp.localInverse_left_inv hp.localInverse_mem_target).symm

/-- A continuous map on a set is smooth there when its composition with a local diffeomorphism is
smooth on that set. -/
theorem _root_.ContMDiffOn.of_comp_isLocalDiffeomorph {n : WithTop ℕ∞}
    [ChartedSpace H X] {p : X → M} (hp : IsLocalDiffeomorph I I n p)
    {f : N → X} {s : Set N}
    (hf : ContinuousOn f s) (hpf : ContMDiffOn J I n (p ∘ f) s) :
    ContMDiffOn J I n f s := by
  intro y hy
  exact (hpf y hy).of_comp_isLocalDiffeomorph (hp (f y)) (hf y hy)

/-- A continuous map is smooth when its composition with a local diffeomorphism is smooth. -/
theorem _root_.ContMDiff.of_comp_isLocalDiffeomorph {n : WithTop ℕ∞}
    [ChartedSpace H X] {p : X → M} (hp : IsLocalDiffeomorph I I n p)
    {f : N → X} (hf : Continuous f)
    (hpf : ContMDiff J I n (p ∘ f)) : ContMDiff J I n f := by
  rw [← contMDiffOn_univ]
  exact hpf.contMDiffOn.of_comp_isLocalDiffeomorph hp hf.continuousOn

/-- A continuous lift through a covering projection with its induced smooth structure is smooth
whenever its composition with the projection is smooth. -/
theorem _root_.ContMDiff.of_comp_isCoveringMap {n : WithTop ℕ∞}
    [IsManifold I n M] {p : X → M} (hp : IsCoveringMap p)
    [c : ChartedSpace H X] (hc : c = hp.inducedChartedSpace H) {f : N → X}
    (hf : Continuous f) (hpf : ContMDiff J I n (p ∘ f)) : ContMDiff J I n f := by
  let _ : IsManifold I n X := hp.induced_isManifold hc
  exact hpf.of_comp_isLocalDiffeomorph (hp.induced_isLocalDiffeomorph hc) hf

/-- Any manifold structure on the total space for which a covering projection is a local
diffeomorphism is compatible with the structure induced from the base. -/
theorem induced_unique {n : WithTop ℕ∞} [IsManifold I n M] {p : X → M}
    (hp : IsCoveringMap p) [c : ChartedSpace H X] [IsManifold I n X]
    (hpc : IsLocalDiffeomorph I I n p) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (hp.inducedChartedSpace H).atlas,
      e.symm.trans e' ∈ contDiffGroupoid n I := by
  rintro e he e' ⟨x, rfl⟩
  let a := hp.inducedChart (H := H) x
  have hpmap : MapsTo p a.source (chartAt H (p x)).source := by
    intro y hy
    simpa only [a, inducedChart, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      mem_preimage, hp.isLocalHomeomorph.localInverseAt_symm,
      OpenPartialHomeomorph.symm_symm] using hy.2
  have ha : ContMDiffOn I I n a a.source :=
    (contMDiffOn_chart.comp (hpc.contMDiff.contMDiffOn.mono (subset_univ _)) hpmap).congr
      (hp.inducedChart_eqOn x)
  have hatarget : a.target ⊆ (chartAt H (p x)).target := by
    intro z hz
    exact hz.1
  have hcomp : ContMDiffOn I I n (p ∘ a.symm) a.target := by
    refine (contMDiffOn_chart_symm.mono hatarget).congr ?_
    intro z hz
    simp only [Function.comp_apply, a, inducedChart,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_symm]
    exact hp.isLocalHomeomorph.apply_localInverseAt_of_mem hz.2
  have ha_symm : ContMDiffOn I I n a.symm a.target :=
    hcomp.of_comp_isLocalDiffeomorph hpc a.symm.continuousOn
  have hamax : a ∈ IsManifold.maximalAtlas I n X :=
    a.mem_maximalAtlas_of_contMDiffOn ha ha_symm
  exact (hamax e he).2

end IsCoveringMap
