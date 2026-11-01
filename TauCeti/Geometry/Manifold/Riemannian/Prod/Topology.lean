/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Products of continuous families of metrics

The chart Cᵏ topology on smooth metrics respects products: if `g p` and `h p` are families of
metrics on `M` and `N` which are continuous in the chart Cᵏ topology, then so is the family of
product metrics `g p × h p` on `M × N`. This holds for every derivative order, including the
chart C² and C∞ topologies, and requires no compactness of either manifold or of the parameter
space.

In the product chart at `(x, y)`, the product metric reads as the block-diagonal form
`((u₁, u₂), (w₁, w₂)) ↦ g_x(z₁)(u₁, w₁) + h_y(z₂)(u₂, w₂)` at `(z₁, z₂)`
(`Bundle.ContMDiffRiemannianMetric.chartMetric_prodTangentSpace`). Each block depends on only one
coordinate and is obtained from the chart metric of a factor by a fixed continuous linear
operation, so the coordinate derivatives of the product metric are continuous linear images of
those of the factors.

The topology and its family criterion are those of
`Bundle.ContMDiffRiemannianMetric.chartCkTopology` and `continuous_chartCk_iff`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.chartMetric_prodTangentSpace`: the product metric read in a
  product chart.
* `Bundle.ContMDiffRiemannianMetric.continuous_prodTangentSpace`: the product of two continuous
  families of metrics is continuous, for every chart Cᵏ topology.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- In the product chart at `p`, the product metric pairs `(u₁, u₂)` and `(w₁, w₂)` at `(z₁, z₂)`
as the chart metric of `g₁` at `p.1` pairs `u₁` and `w₁` at `z₁`, plus the chart metric of `g₂`
at `p.2` pairing `u₂` and `w₂` at `z₂`. -/
theorem chartMetric_prodTangentSpace
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (p : M × N) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) p).target) :
    (g₁.prodTangentSpace g₂).toNondegenerateMetric.chartMetric p z =
      (g₁.toNondegenerateMetric.chartMetric p.1 z.1).bilinearComp
          (ContinuousLinearMap.fst ℝ E F) (ContinuousLinearMap.fst ℝ E F) +
        (g₂.toNondegenerateMetric.chartMetric p.2 z.2).bilinearComp
          (ContinuousLinearMap.snd ℝ E F) (ContinuousLinearMap.snd ℝ E F) := by
  have hz' : z.1 ∈ (extChartAt I p.1).target ∧ z.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, mem_prod] using hz
  have hinv : (extChartAt (I.prod J) p).symm z =
      ((extChartAt I p.1).symm z.1, (extChartAt J p.2).symm z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
  have hq : (extChartAt (I.prod J) p).symm z ∈ (chartAt (ModelProd H G) p).source := by
    simpa only [extChartAt_source] using (extChartAt (I.prod J) p).map_target hz
  have hq' : (extChartAt (I.prod J) p).symm z ∈
      (trivializationAt (E × F) (TangentSpace (I.prod J) : M × N → Type _) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hq
  have hq₁ : (extChartAt I p.1).symm z.1 ∈
      (trivializationAt E (TangentSpace I : M → Type _) p.1).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I p.1).map_target hz'.1
  have hq₂ : (extChartAt J p.2).symm z.2 ∈
      (trivializationAt F (TangentSpace J : N → Type _) p.2).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt J p.2).map_target hz'.2
  refine ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun w ↦ ?_
  simp only [add_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [(g₁.prodTangentSpace g₂).toNondegenerateMetric.chartMetric_apply hz,
    g₁.toNondegenerateMetric.chartMetric_apply hz'.1,
    g₂.toNondegenerateMetric.chartMetric_apply hz'.2]
  simp only [toNondegenerateMetric_apply, prodTangentSpace_inner,
    ← Trivialization.symmL_apply (R := ℝ) _ hq', ← Trivialization.symmL_apply (R := ℝ) _ hq₁,
    ← Trivialization.symmL_apply (R := ℝ) _ hq₂,
    TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq]
  rw [hinv]

section Topology

variable [I.Boundaryless] [J.Boundaryless]

-- Cache the canonical operator-space instances, as in the definition of the chart Cᵏ topology:
-- searching for the topology on iterated multilinear maps into nested operator spaces otherwise
-- exhausts instance-search heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E × F →L[ℝ] E × F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E × F →L[ℝ] E × F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The coordinate derivatives of the product metric are those of its two blocks, for any continuous
linear maps `A₁` and `A₂` realising the blocks as pullbacks of bilinear forms along the two
projections. -/
private theorem iteratedFDeriv_chartMetric_prodTangentSpace
    {A₁ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E × F →L[ℝ] E × F →L[ℝ] ℝ}
    {A₂ : (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] E × F →L[ℝ] E × F →L[ℝ] ℝ}
    (hA₁ : ∀ B, A₁ B = B.bilinearComp (ContinuousLinearMap.fst ℝ E F)
      (ContinuousLinearMap.fst ℝ E F))
    (hA₂ : ∀ B, A₂ B = B.bilinearComp (ContinuousLinearMap.snd ℝ E F)
      (ContinuousLinearMap.snd ℝ E F))
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (p : M × N) (m : ℕ) {z : E × F} (hz₁ : z.1 ∈ (extChartAt I p.1).target)
    (hz₂ : z.2 ∈ (extChartAt J p.2).target) :
    iteratedFDeriv ℝ m ((g₁.prodTangentSpace g₂).toNondegenerateMetric.chartMetric p) z =
      A₁.compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m (g₁.toNondegenerateMetric.chartMetric p.1) z.1)
            |>.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.fst ℝ E F) +
        A₂.compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m (g₂.toNondegenerateMetric.chartMetric p.2) z.2)
            |>.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.snd ℝ E F) := by
  have hc₁ : ContDiffAt ℝ ∞ (g₁.toNondegenerateMetric.chartMetric p.1) z.1 :=
    (g₁.toNondegenerateMetric.contDiffOn_chartMetric p.1).contDiffAt
      ((isOpen_extChartAt_target p.1).mem_nhds hz₁)
  have hc₂ : ContDiffAt ℝ ∞ (g₂.toNondegenerateMetric.chartMetric p.2) z.2 :=
    (g₂.toNondegenerateMetric.contDiffOn_chartMetric p.2).contDiffAt
      ((isOpen_extChartAt_target p.2).mem_nhds hz₂)
  have hd₁ : ContDiffAt ℝ ∞ (g₁.toNondegenerateMetric.chartMetric p.1 ∘
      ContinuousLinearMap.fst ℝ E F) z := hc₁.comp z contDiffAt_fst
  have hd₂ : ContDiffAt ℝ ∞ (g₂.toNondegenerateMetric.chartMetric p.2 ∘
      ContinuousLinearMap.snd ℝ E F) z := hc₂.comp z contDiffAt_snd
  -- Near `z` the product chart metric is the sum of the two blocks.
  have hz : z ∈ (extChartAt (I.prod J) p).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, mem_prod] using ⟨hz₁, hz₂⟩
  have heq : (g₁.prodTangentSpace g₂).toNondegenerateMetric.chartMetric p =ᶠ[𝓝 z]
      A₁ ∘ (g₁.toNondegenerateMetric.chartMetric p.1 ∘ ContinuousLinearMap.fst ℝ E F) +
        A₂ ∘ (g₂.toNondegenerateMetric.chartMetric p.2 ∘ ContinuousLinearMap.snd ℝ E F) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
    simp only [chartMetric_prodTangentSpace _ _ p hw, Pi.add_apply, Function.comp_apply, hA₁, hA₂,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hm : ((m : ℕ∞) : WithTop ℕ∞) ≤ ∞ := mod_cast le_top
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds,
    iteratedFDeriv_add_apply ((A₁.contDiff.contDiffAt.comp z hd₁).of_le hm)
      ((A₂.contDiff.contDiffAt.comp z hd₂).of_le hm),
    A₁.iteratedFDeriv_comp_left hd₁ hm, A₂.iteratedFDeriv_comp_left hd₂ hm,
    ContinuousLinearMap.iteratedFDeriv_comp_right_of_contDiffAt _ hc₁ hm,
    ContinuousLinearMap.iteratedFDeriv_comp_right_of_contDiffAt _ hc₂ hm,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

variable [LocallyCompactSpace E] [LocallyCompactSpace F] (k : ℕ∞)

/-- Product preserves continuity of families for every chart Cᵏ topology. Both metrics may vary,
and the parameter space is arbitrary. -/
theorem continuous_prodTangentSpace {P : Type*} [TopologicalSpace P]
    {g₁ : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₂ : P → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (hg₁ : @Continuous _ _ _ (chartCkTopology k) g₁)
    (hg₂ : @Continuous _ _ _ (chartCkTopology k) g₂) :
    @Continuous _ _ _ (chartCkTopology k) (fun p ↦ (g₁ p).prodTangentSpace (g₂ p)) := by
  rw [continuous_chartCk_iff] at hg₁ hg₂ ⊢
  intro p m hm
  have hmem {z : E × F} (hz : z ∈ (extChartAt (I.prod J) p).target) :
      z.1 ∈ (extChartAt I p.1).target ∧ z.2 ∈ (extChartAt J p.2).target := by
    simpa only [extChartAt_prod, PartialEquiv.prod_target, mem_prod] using hz
  -- The blocks of the product chart metric, as continuous linear maps in the bilinear forms.
  set A₁ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E × F →L[ℝ] E × F →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (E × F) (E →L[ℝ] ℝ) (E × F →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip (ContinuousLinearMap.fst ℝ E F))).comp
      ((ContinuousLinearMap.compL ℝ (E × F) E (E →L[ℝ] ℝ)).flip (ContinuousLinearMap.fst ℝ E F))
  set A₂ : (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] E × F →L[ℝ] E × F →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (E × F) (F →L[ℝ] ℝ) (E × F →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip (ContinuousLinearMap.snd ℝ E F))).comp
      ((ContinuousLinearMap.compL ℝ (E × F) F (F →L[ℝ] ℝ)).flip (ContinuousLinearMap.snd ℝ E F))
  have hA₁ (B : E →L[ℝ] E →L[ℝ] ℝ) : A₁ B = B.bilinearComp (ContinuousLinearMap.fst ℝ E F)
      (ContinuousLinearMap.fst ℝ E F) :=
    ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ by simp [A₁]
  have hA₂ (B : F →L[ℝ] F →L[ℝ] ℝ) : A₂ B = B.bilinearComp (ContinuousLinearMap.snd ℝ E F)
      (ContinuousLinearMap.snd ℝ E F) :=
    ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ by simp [A₂]
  refine Continuous.congr ?_ fun q ↦ (iteratedFDeriv_chartMetric_prodTangentSpace hA₁ hA₂
    (g₁ q.1) (g₂ q.1) p m (hmem q.2.2).1 (hmem q.2.2).2).symm
  -- The derivatives of the factors are continuous, and so are their images under fixed
  -- continuous linear operations.
  have h₁ : Continuous fun q : P × (extChartAt (I.prod J) p).target ↦
      iteratedFDeriv ℝ m ((g₁ q.1).toNondegenerateMetric.chartMetric p.1) (q.2 : E × F).1 :=
    (hg₁ p.1 m hm).comp (continuous_fst.prodMk
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk
        fun q ↦ (hmem q.2.2).1))
  have h₂ : Continuous fun q : P × (extChartAt (I.prod J) p).target ↦
      iteratedFDeriv ℝ m ((g₂ q.1).toNondegenerateMetric.chartMetric p.2) (q.2 : E × F).2 :=
    (hg₂ p.2 m hm).comp (continuous_fst.prodMk
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk
        fun q ↦ (hmem q.2.2).2))
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _ A₁).continuous.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp h₁)).add
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _ A₂).continuous.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp h₂))

end Topology

end Bundle.ContMDiffRiemannianMetric
