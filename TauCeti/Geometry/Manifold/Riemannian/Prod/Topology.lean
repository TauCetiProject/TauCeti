/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
public import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Products of continuous families of metrics

In the product chart at `(x, y)`, the product metric `g × h` on `M × N` is the orthogonal sum of
the coordinate metric of `g` in the chart at `x`, read on the first coordinate, and that of `h` in
the chart at `y`, read on the second. Each of its coordinate derivatives is therefore the sum of
the corresponding derivatives of the two factors, taken in the directions of their own coordinates
(`iteratedFDeriv_chartMetric_prodTangentSpace_apply`).

Consequently the product of metrics respects the chart Cᵏ topologies: a family of product metrics
is continuous exactly when both factor families are (`continuous_prodTangentSpace_iff`), for every
derivative order, including the chart C² and C∞ topologies. The parameter space is arbitrary, and
neither manifold needs to be compact; the converse direction only needs both manifolds to be
nonempty, so that a coordinate derivative of one factor can be read off along a slice through a
point of the other.

The topology and its family criterion are those of
`Bundle.ContMDiffRiemannianMetric.chartCkTopology` and `continuous_chartCk_iff`.
-/

public section

noncomputable section

open Bundle Set Filter Topology TauCeti.Manifold
open ContinuousLinearMap (pullbackBilinL pullbackBilinL_apply)
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

-- Cache the canonical operator-space instances, as in the definition of the chart Cᵏ topology:
-- searching for the structure on nested operator spaces otherwise exhausts instance-search
-- heartbeats.
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
private local instance : NormedAddCommGroup (E × F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E × F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E × F →L[ℝ] E × F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E × F →L[ℝ] E × F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- In the product chart at `(x, y)`, the product metric pairs two vectors of `E × F` as the sum
of the pairings of their components by the coordinate metrics of the factors. -/
theorem chartMetric_prodTangentSpace_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (x : M) (y : N) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) (x, y)).target)
    (v w : E × F) :
    (g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y) z v w =
      g.toNondegenerateMetric.chartMetric x z.1 v.1 w.1 +
        h.toNondegenerateMetric.chartMetric y z.2 v.2 w.2 := by
  have hzt : z ∈ (extChartAt I x).target ×ˢ (extChartAt J y).target :=
    (TauCeti.extChartAt_prod_target (x, y)).subset hz
  have hinv : (extChartAt (I.prod J) (x, y)).symm z =
      ((extChartAt I x).symm z.1, (extChartAt J y).symm z.2) := by
    rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
  have hx : (extChartAt I x).symm z.1 ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hzt.1
  have hy : (extChartAt J y).symm z.2 ∈ (chartAt G y).source := by
    simpa using (extChartAt J y).map_target hzt.2
  have hq : ((extChartAt I x).symm z.1, (extChartAt J y).symm z.2) ∈
      (chartAt (ModelProd H G) (x, y)).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source] using
      mk_mem_prod hx hy
  rw [(g.prodTangentSpace h).toNondegenerateMetric.chartMetric_apply hz,
    g.toNondegenerateMetric.chartMetric_apply hzt.1,
    h.toNondegenerateMetric.chartMetric_apply hzt.2, hinv]
  simp only [toNondegenerateMetric_apply, prodTangentSpace_inner]
  have hbase : ((extChartAt I x).symm z.1, (extChartAt J y).symm z.2) ∈
      (trivializationAt (E × F) (TangentSpace (I.prod J)) (x, y)).baseSet := by simpa using hq
  have hbx : (extChartAt I x).symm z.1 ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    simpa using hx
  have hby : (extChartAt J y).symm z.2 ∈ (trivializationAt F (TangentSpace J) y).baseSet := by
    simpa using hy
  simp only [← Trivialization.symmL_apply (R := ℝ) _ hbase,
    ← Trivialization.symmL_apply (R := ℝ) _ hbx, ← Trivialization.symmL_apply (R := ℝ) _ hby,
    tangentSpaceProdEquiv_symmL_trivializationAt hq]

variable [I.Boundaryless] [J.Boundaryless]

/-- The coordinate derivatives of the product metric, as continuous multilinear maps: the
derivatives of the two factors, read on the respective coordinates. -/
private theorem iteratedFDeriv_chartMetric_prodTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (x : M) (y : N) (m : ℕ) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) (x, y)).target) :
    iteratedFDeriv ℝ m ((g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y)) z =
      (pullbackBilinL (.fst ℝ E F)).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z.1).compContinuousLinearMap
            fun _ ↦ .fst ℝ E F) +
        (pullbackBilinL (.snd ℝ E F)).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric y) z.2).compContinuousLinearMap
            fun _ ↦ .snd ℝ E F) := by
  set Bg := g.toNondegenerateMetric.chartMetric x
  set Bh := h.toNondegenerateMetric.chartMetric y
  have hU := isOpen_extChartAt_target (I := I) x
  have hV := isOpen_extChartAt_target (I := J) y
  have hz' := hz
  rw [TauCeti.extChartAt_prod_target] at hz'
  -- Near `z` the product chart metric is the sum of the pullbacks of `Bg` and `Bh` along the
  -- coordinate projections.
  have heq : (g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y) =ᶠ[𝓝 z]
      (pullbackBilinL (.fst ℝ E F) ∘ (Bg ∘ ContinuousLinearMap.fst ℝ E F)) +
        (pullbackBilinL (.snd ℝ E F) ∘ (Bh ∘ ContinuousLinearMap.snd ℝ E F)) := by
    filter_upwards [(isOpen_extChartAt_target (I := I.prod J) (x, y)).mem_nhds hz] with w hw
    refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
    simp only [chartMetric_prodTangentSpace_apply g h x y hw, Pi.add_apply, Function.comp_apply,
      add_apply, pullbackBilinL_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Bg, Bh]
  have hi : ((m : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have h₁ : ContDiffAt ℝ m (pullbackBilinL (.fst ℝ E F) ∘ (Bg ∘ ContinuousLinearMap.fst ℝ E F)) z :=
    ((((g.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt (hU.mem_nhds hz'.1)).comp z
      (ContinuousLinearMap.fst ℝ E F).contDiff.contDiffAt).of_le hi).continuousLinearMap_comp _
  have h₂ : ContDiffAt ℝ m (pullbackBilinL (.snd ℝ E F) ∘ (Bh ∘ ContinuousLinearMap.snd ℝ E F)) z :=
    ((((h.toNondegenerateMetric.contDiffOn_chartMetric y).contDiffAt (hV.mem_nhds hz'.2)).comp z
      (ContinuousLinearMap.snd ℝ E F).contDiff.contDiffAt).of_le hi).continuousLinearMap_comp _
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_add_apply h₁ h₂,
    ContinuousLinearMap.iteratedFDeriv_pullbackBilinL_comp hU
      (g.toNondegenerateMetric.contDiffOn_chartMetric x) _ hz'.1 hi,
    ContinuousLinearMap.iteratedFDeriv_pullbackBilinL_comp hV
      (h.toNondegenerateMetric.contDiffOn_chartMetric y) _ hz'.2 hi]
  -- The two sides differ only in writing `ContinuousLinearMap.fst ℝ E F z` for `z.1`, and
  -- similarly for the second coordinate.
  rfl

/-- In the product chart at `(x, y)`, every coordinate derivative of the product metric is the sum
of the coordinate derivatives of the factors, taken in the directions of their own coordinates. -/
theorem iteratedFDeriv_chartMetric_prodTangentSpace_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (x : M) (y : N) (m : ℕ) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) (x, y)).target)
    (v : Fin m → E × F) (a b : E × F) :
    iteratedFDeriv ℝ m ((g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y)) z v a b =
      iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z.1 (fun i ↦ (v i).1) a.1 b.1 +
        iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric y) z.2
          (fun i ↦ (v i).2) a.2 b.2 := by
  rw [iteratedFDeriv_chartMetric_prodTangentSpace g h x y m hz]
  simp only [add_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, pullbackBilinL_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

/-- Along the slice through a point of the chart target of `y`, the coordinate derivatives of a
metric `g` on the first factor are recovered from those of `g × h`. -/
private theorem iteratedFDeriv_chartMetric_eq_of_prodTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (x : M) (y : N) (m : ℕ) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) (x, y)).target) :
    iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z.1 =
      (pullbackBilinL (.inl ℝ E F)).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m ((g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y))
          z).compContinuousLinearMap fun _ ↦ .inl ℝ E F) := by
  ext v a b
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, pullbackBilinL_apply,
    iteratedFDeriv_chartMetric_prodTangentSpace_apply g h x y m hz, ContinuousLinearMap.inl_apply,
    map_zero, add_zero]

/-- Along the slice through a point of the chart target of `x`, the coordinate derivatives of a
metric `h` on the second factor are recovered from those of `g × h`. -/
private theorem iteratedFDeriv_chartMetric_eq_of_prodTangentSpace'
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (x : M) (y : N) (m : ℕ) {z : E × F} (hz : z ∈ (extChartAt (I.prod J) (x, y)).target) :
    iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric y) z.2 =
      (pullbackBilinL (.inr ℝ E F)).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m ((g.prodTangentSpace h).toNondegenerateMetric.chartMetric (x, y))
          z).compContinuousLinearMap fun _ ↦ .inr ℝ E F) := by
  ext v a b
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, pullbackBilinL_apply,
    iteratedFDeriv_chartMetric_prodTangentSpace_apply g h x y m hz, ContinuousLinearMap.inr_apply,
    map_zero, zero_add]

variable [LocallyCompactSpace E] [LocallyCompactSpace F] (k : ℕ∞)

/-- The product of metrics preserves continuity of families for every chart Cᵏ topology. Both
metrics may vary, and the parameter space is arbitrary. -/
@[fun_prop]
theorem continuous_prodTangentSpace {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {h : P → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (hg : @Continuous _ _ _ (chartCkTopology k) g)
    (hh : @Continuous _ _ _ (chartCkTopology k) h) :
    @Continuous _ _ _ (chartCkTopology k) (fun p ↦ (g p).prodTangentSpace (h p)) := by
  rw [continuous_chartCk_iff] at hg hh ⊢
  rintro ⟨x, y⟩ m hm
  have hmem (q : P × (extChartAt (I.prod J) (x, y)).target) :
      (q.2 : E × F) ∈ (extChartAt I x).target ×ˢ (extChartAt J y).target :=
    (TauCeti.extChartAt_prod_target (x, y)).subset q.2.2
  have h₁ : Continuous fun q : P × (extChartAt (I.prod J) (x, y)).target ↦
      iteratedFDeriv ℝ m ((g q.1).toNondegenerateMetric.chartMetric x) (q.2 : E × F).1 :=
    (hg x m hm).comp (continuous_fst.prodMk
      ((continuous_fst.comp continuous_subtype_val.snd').subtype_mk fun q ↦ (hmem q).1))
  have h₂ : Continuous fun q : P × (extChartAt (I.prod J) (x, y)).target ↦
      iteratedFDeriv ℝ m ((h q.1).toNondegenerateMetric.chartMetric y) (q.2 : E × F).2 :=
    (hh y m hm).comp (continuous_fst.prodMk
      ((continuous_snd.comp continuous_subtype_val.snd').subtype_mk fun q ↦ (hmem q).2))
  refine Continuous.congr ?_ fun q ↦
    (iteratedFDeriv_chartMetric_prodTangentSpace (g q.1) (h q.1) x y m q.2.2).symm
  exact (h₁.pullbackBilinL_compContinuousMultilinearMap (.fst ℝ E F)).add
    (h₂.pullbackBilinL_compContinuousMultilinearMap (.snd ℝ E F))

/-- A family of product metrics is continuous in the chart Cᵏ topology if and only if both
factor families are continuous in that topology. Both manifolds are nonempty: otherwise the
product is empty and carries no information on the other factor. -/
theorem continuous_prodTangentSpace_iff [Nonempty M] [Nonempty N] {P : Type*}
    [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {h : P → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)} :
    @Continuous _ _ _ (chartCkTopology k) (fun p ↦ (g p).prodTangentSpace (h p)) ↔
      @Continuous _ _ _ (chartCkTopology k) g ∧ @Continuous _ _ _ (chartCkTopology k) h := by
  refine ⟨fun hgh ↦ ?_, fun ⟨hg, hh⟩ ↦ continuous_prodTangentSpace k hg hh⟩
  rw [continuous_chartCk_iff] at hgh
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  constructor
  · rw [continuous_chartCk_iff]
    intro x m hm
    have hmem (q : P × (extChartAt I x).target) :
        ((q.2 : E), extChartAt J y₀ y₀) ∈ (extChartAt (I.prod J) (x, y₀)).target := by
      rw [TauCeti.extChartAt_prod_target]
      exact ⟨q.2.2, mem_extChartAt_target y₀⟩
    have hc := (hgh (x, y₀) m hm).comp (continuous_fst.prodMk
      ((continuous_subtype_val.snd'.prodMk continuous_const).subtype_mk hmem))
    refine Continuous.congr ?_ fun q ↦
      (iteratedFDeriv_chartMetric_eq_of_prodTangentSpace (g q.1) (h q.1) x y₀ m (hmem q)).symm
    exact hc.pullbackBilinL_compContinuousMultilinearMap (.inl ℝ E F)
  · rw [continuous_chartCk_iff]
    intro y m hm
    have hmem (q : P × (extChartAt J y).target) :
        (extChartAt I x₀ x₀, (q.2 : F)) ∈ (extChartAt (I.prod J) (x₀, y)).target := by
      rw [TauCeti.extChartAt_prod_target]
      exact ⟨mem_extChartAt_target x₀, q.2.2⟩
    have hc := (hgh (x₀, y) m hm).comp (continuous_fst.prodMk
      ((continuous_const.prodMk continuous_subtype_val.snd').subtype_mk hmem))
    refine Continuous.congr ?_ fun q ↦
      (iteratedFDeriv_chartMetric_eq_of_prodTangentSpace' (g q.1) (h q.1) x₀ y m (hmem q)).symm
    exact hc.pullbackBilinL_compContinuousMultilinearMap (.inr ℝ E F)

end Bundle.ContMDiffRiemannianMetric
