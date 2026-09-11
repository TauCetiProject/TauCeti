/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Weak Whitney jets on manifold chart domains

For a vector-valued smooth map on a manifold, differentiate its coordinate representative within
the target of each extended source chart. These derivatives are continuous on that target, even
when the manifold has boundary or corners: the model with corners supplies unique derivatives
within the chart target. Bundling them as compact-open continuous maps gives the chart jet and
its induced weak Whitney topology.

This construction allows a source covered by many charts, rather than requiring one global
chart. It is the vector-valued coordinate-map space needed when treating maps between manifolds
locally in the target. The topology is supplied explicitly, so it can coexist with the existing
global-chart instance; on normed spaces the two topologies agree.

The construction follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, and extends
the global-chart construction in `ContMDiffMap.WeakWhitney` using Mathlib's extended charts and
iterated derivatives within sets. No boundaryless or compactness assumption is needed here.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- The derivative of order `m` of a vector-valued map in the source chart at `x`, as a
continuous map on the extended chart target. Derivatives are taken within that target. -/
noncomputable def chartIteratedFDeriv
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : ℕ) (hm : m ≤ n) :
    C((extChartAt I x).target, E [×m]→L[𝕜] F) := by
  refine ⟨fun y ↦ iteratedFDerivWithin 𝕜 m
    (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f)
    (extChartAt I x).target y, ?_⟩
  have hf : ContDiffOn 𝕜 n (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f)
      (extChartAt I x).target :=
    (f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  exact (hf.continuousOn_iteratedFDerivWithin hm
    (uniqueDiffOn_extChartAt_target x)).domRestrict

-- Spell out the chart target in the coercion type so these simp lemmas are in normal form.
@[simp]
theorem chartIteratedFDeriv_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : ℕ) (hm : m ≤ n)
    (y : (extChartAt I x).target) :
    DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×m]→L[𝕜] F))
      (chartIteratedFDeriv f x m hm) y = iteratedFDerivWithin 𝕜 m
      (writtenInExtChartAt I (modelWithCornersSelf 𝕜 F) x f) (extChartAt I x).target y := by
  rfl

/-- Order zero of the chart jet recovers the map in source coordinates. -/
@[simp]
theorem chartIteratedFDeriv_zero_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M)
    (y : (extChartAt I x).target) (v : Fin 0 → E) :
    DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×0]→L[𝕜] F))
      (chartIteratedFDeriv f x 0 (by simp)) y v =
        f ((extChartAt I x).symm y) := by
  simp only [chartIteratedFDeriv_apply, iteratedFDerivWithin_zero_apply]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe]
  rfl

/-- All source-chart derivatives, with a compact-open topology on each derivative space. -/
noncomputable def chartWeakWhitneyJet
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) :
    (x : M) → (m : {m : ℕ // m ≤ n}) →
      C((extChartAt I x).target, E [×(m : ℕ)]→L[𝕜] F) :=
  fun x m ↦ chartIteratedFDeriv f x m m.property

@[simp]
theorem chartWeakWhitneyJet_apply
    (f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯) (x : M) (m : {m : ℕ // m ≤ n}) :
    chartWeakWhitneyJet f x m = chartIteratedFDeriv f x m m.property := (rfl)

/-- The weak Whitney topology on vector-valued `C^n` maps from a manifold: the initial topology
for all derivatives on all preferred extended chart targets. -/
@[instance_reducible]
noncomputable def chartWeakWhitneyTopology :
    TopologicalSpace C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯ :=
  TopologicalSpace.induced chartWeakWhitneyJet inferInstance

section ChartTopology

attribute [local instance] chartWeakWhitneyTopology

/-- The chart jet induces exactly the chart weak Whitney topology. -/
theorem isInducing_chartWeakWhitneyJet :
    IsInducing (chartWeakWhitneyJet (I := I) (M := M) (F := F) (n := n)) := ⟨rfl⟩

/-- A map into the chart weak Whitney space is continuous exactly when each chart derivative
depends continuously on the parameter in the compact-open topology. -/
theorem continuous_chartWeakWhitney_iff {X : Type*} [TopologicalSpace X]
    {g : X → C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯} :
    Continuous g ↔ ∀ (x : M) (m : ℕ) (hm : m ≤ n),
      Continuous (fun a ↦ chartIteratedFDeriv (g a) x m hm) := by
  rw [isInducing_chartWeakWhitneyJet.continuous_iff]
  simp only [continuous_pi_iff, Function.comp_apply, chartWeakWhitneyJet_apply, Subtype.forall]

/-- Projection to a fixed chart and derivative order is continuous. -/
theorem continuous_chartIteratedFDeriv (x : M) (m : ℕ) (hm : m ≤ n) :
    Continuous (fun f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯ ↦
      chartIteratedFDeriv f x m hm) :=
  continuous_chartWeakWhitney_iff.mp continuous_id x m hm

/-- Convergence in the chart weak Whitney topology is compact-open convergence of every
derivative on every extended chart target. -/
theorem tendsto_chartWeakWhitney_iff {X : Type*} {l : Filter X}
    {g : X → C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯}
    {f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯} :
    Tendsto g l (𝓝 f) ↔ ∀ (x : M) (m : ℕ) (hm : m ≤ n),
      Tendsto (fun a ↦ chartIteratedFDeriv (g a) x m hm) l
        (𝓝 (chartIteratedFDeriv f x m hm)) := by
  rw [isInducing_chartWeakWhitneyJet.tendsto_nhds_iff]
  simp only [tendsto_pi_nhds, Function.comp_apply, chartWeakWhitneyJet_apply, Subtype.forall]

/-- The zero-order chart derivatives determine the original map. -/
theorem chartWeakWhitneyJet_injective :
    Function.Injective (chartWeakWhitneyJet (I := I) (M := M) (F := F) (n := n)) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  have hx := DFunLike.congr_fun (congrFun (congrFun h x) ⟨0, by simp⟩)
    ⟨extChartAt I x x, mem_extChartAt_target x⟩
  have hvalue := congrArg (fun A : E [×0]→L[𝕜] F ↦ A 0) hx
  simpa only [extChartAt_to_inv] using
    (chartIteratedFDeriv_zero_apply f x _ 0).symm.trans
      (hvalue.trans (chartIteratedFDeriv_zero_apply g x _ 0))

/-- The chart jet embeds the weak Whitney map space into the product of its derivative spaces. -/
theorem isEmbedding_chartWeakWhitneyJet :
    IsEmbedding (chartWeakWhitneyJet (I := I) (M := M) (F := F) (n := n)) :=
  ⟨isInducing_chartWeakWhitneyJet, chartWeakWhitneyJet_injective⟩

/-- The chart weak Whitney topology is Hausdorff. -/
theorem t2Space_chartWeakWhitney :
    T2Space C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯ :=
  isEmbedding_chartWeakWhitneyJet.t2Space

/-- Evaluation at a fixed source point is continuous in the chart weak Whitney topology. -/
theorem continuous_eval_chartWeakWhitney (x : M) :
    Continuous (fun f : C^n⟮I, M; modelWithCornersSelf 𝕜 F, F⟯ ↦ f x) := by
  have h := (continuousMultilinearCurryFin0 𝕜 E F).continuous.comp
    ((continuous_eval_const ⟨extChartAt I x x, mem_extChartAt_target x⟩).comp
      (continuous_chartIteratedFDeriv (I := I) (F := F) (n := n) x 0 (by simp)))
  convert h using 1
  funext f
  have hvalue := chartIteratedFDeriv_zero_apply f x
    ⟨extChartAt I x x, mem_extChartAt_target x⟩ 0
  simp only [extChartAt_to_inv] at hvalue
  simp only [Function.comp_def, continuousMultilinearCurryFin0_apply]
  convert hvalue.symm using 1
  rfl

end ChartTopology

section NormedSpace

omit [IsManifold I n M]

/-- For the identity chart of a normed space, the chart derivative is the ordinary iterated
derivative, evaluated on the subtype representing the whole chart target. -/
@[simp]
theorem chartIteratedFDeriv_self_apply
    (f : C^n⟮modelWithCornersSelf 𝕜 E, E; modelWithCornersSelf 𝕜 F, F⟯)
    (x : E) (m : ℕ) (hm : m ≤ n)
    (y : (extChartAt (modelWithCornersSelf 𝕜 E) x).target) :
    DFunLike.coe (F := C(↥(Set.univ ∩ (chartAt E x).target), E [×m]→L[𝕜] F))
      (chartIteratedFDeriv f x m hm) y =
        f.iteratedFDerivContinuousMap m hm y := by
  refine (chartIteratedFDeriv_apply f x m hm y).trans ?_
  simp only [extChartAt_model_space_eq_id,
    PartialEquiv.refl_target, iteratedFDerivWithin_univ,
    ContMDiffMap.iteratedFDerivContinuousMap_apply]
  have hw : writtenInExtChartAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F) x f = f := by
    funext z
    simp [writtenInExtChartAt, chartAt_self_eq, Function.comp_apply]
  rw [hw]

/-- On a normed space, source-chart weak Whitney topology agrees with the existing topology
defined using global iterated derivatives. Thus adding chart domains does not change the
global-chart construction. -/
@[simp] theorem chartWeakWhitneyTopology_self :
    chartWeakWhitneyTopology (I := modelWithCornersSelf 𝕜 E) (M := E) (F := F) (n := n) =
      ContMDiffMap.weakWhitneyTopology := by
  have hglobal : ContMDiffMap.weakWhitneyTopology (k := 𝕜) (E := E) (F := F) (n := n) =
      TopologicalSpace.induced ContMDiffMap.weakWhitneyJet inferInstance :=
    ContMDiffMap.isInducing_weakWhitneyJet.eq_induced
  apply le_antisymm
  · rw [hglobal]
    apply continuous_iff_le_induced.mp
    let : TopologicalSpace C^n⟮modelWithCornersSelf 𝕜 E, E; modelWithCornersSelf 𝕜 F, F⟯ :=
      chartWeakWhitneyTopology
    apply continuous_pi
    intro m
    let toTarget : C(E, (extChartAt (modelWithCornersSelf 𝕜 E) (0 : E)).target) :=
      ⟨fun y ↦ ⟨y, by simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target,
        mem_univ]⟩, continuous_id.subtype_mk (fun _ ↦ by
          simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target, mem_univ])⟩
    have h := (ContinuousMap.continuous_precomp toTarget).comp
      (continuous_chartIteratedFDeriv (I := modelWithCornersSelf 𝕜 E)
        (F := F) (n := n) 0 m m.property)
    convert h using 1
    funext f
    apply ContinuousMap.ext
    intro y
    simp only [ContMDiffMap.weakWhitneyJet_apply, Function.comp_apply, ContinuousMap.comp_apply]
    convert (chartIteratedFDeriv_self_apply f 0 m m.property (toTarget y)).symm using 1 <;> rfl
  · rw [chartWeakWhitneyTopology]
    apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro x
    apply continuous_pi
    intro m
    have h := (ContinuousMap.continuous_restrict
      (extChartAt (modelWithCornersSelf 𝕜 E) x).target).comp
      (ContMDiffMap.continuous_iteratedFDerivContinuousMap (k := 𝕜)
        (E := E) (F := F) (n := n) m m.property)
    convert h using 1 <;> try rfl
    funext f
    apply ContinuousMap.ext
    intro y
    simp only [ContinuousMap.restrict_apply, Function.comp_apply]
    exact chartIteratedFDeriv_self_apply f x m m.property y

end NormedSpace

end TauCeti
