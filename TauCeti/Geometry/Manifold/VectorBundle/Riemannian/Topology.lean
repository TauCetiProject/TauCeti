/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic

/-!
# The chart Cᵏ topologies on smooth Riemannian metrics

`Bundle.ContMDiffRiemannianMetric.chartCkTopology k` equips the native smooth metric carrier
with the initial topology of its coordinate derivatives of every order `m ≤ k`, for
`k : ℕ∞`. Each derivative is a continuous map on an extended chart target, with its
compact-open topology. Thus convergence means uniform convergence of all these derivatives on
every compact subset of every chart target. Derivatives take values in continuous multilinear
maps with the operator norm; no basis of the model space is chosen.

The family criterion `continuous_chartCk_iff` expresses continuity by joint continuity of the
coordinate derivatives in the parameter and chart variable; in particular each coordinate
derivative is jointly continuous in the metric and the chart variable
(`continuousAt_iteratedFDeriv_chartMetric`). Conversely, for a family whose chart metrics depend
smoothly on a continuous parameter, `continuousAt_chartMetric_jets` gives joint continuity of the
Gram matrices and their first two partial derivatives in a basis. Evaluation of the metric at a
fixed point is continuous, and these evaluations separate metrics. The topologies decrease as
`k` grows (`antitone_chartCkTopology`), so a quantity that is continuous in the chart C²
topology, such as a second-order curvature expression, is continuous in every chart Cᵏ topology
with `2 ≤ k`. Likewise a set of metrics compact in a chart Cˡ topology is compact in every chart
Cᵏ topology with `k ≤ l` (`IsCompact.chartCk_of_le`).

The chart C² topology `chartC2Topology` and the chart C∞ topology `chartCInftyTopology` are the
cases `k = 2` and `k = ⊤`. They are selected by `open scoped TauCeti.MetricC2` and
`open scoped TauCeti.MetricCInfty` respectively, rather than by global instances, so that they
can coexist on the same carrier; the C∞ one is finer (`chartCInftyTopology_le_chartC2Topology`).

This construction uses the compact-open derivative convention of M. Hirsch,
*Differential Topology*, GTM 33, Chapter 2, §1, also used by
`ContMDiffMap.manifoldWeakWhitneyTopology`. Comparison with other atlases or with a topology
on smooth tensor sections is not established here.
-/

open Bundle Set Filter Topology
open scoped ContDiff Manifold

public section

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

-- Public signatures cannot use private cached instances. Insert the canonical instances
-- directly into each signature involving nested operator spaces, avoiding instance-search
-- timeouts without exporting duplicate instances or changing the global search priorities.
local macro "withMetricOperatorNorms " E:term " in " t:term : term =>
  `(letI : NormedAddCommGroup ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup ($E →L[ℝ] $E →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] $E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    $t)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Cache the canonical operator-space instances: searching for the topology on iterated
-- multilinear maps into nested operator spaces otherwise exhausts instance-search heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The order-`m` derivative of a metric in the chart at `x`, as a continuous map on its
target. The derivative is of the full bilinear form, not of a chosen matrix representation. -/
def chartMetricDerivative
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (m : ℕ) : withMetricOperatorNorms E in
    C((extChartAt I x).target, E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
  ⟨fun z ↦ iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z,
    (ContinuousOn.continuousOn_iteratedFDeriv
      (g.toNondegenerateMetric.contDiffOn_chartMetric x)
      (isOpen_extChartAt_target x) (by simp)).domRestrict⟩

/-- Evaluation of a bundled chart derivative is the ordinary iterated Fréchet derivative. -/
-- Spell out the target in the coercion type, as in `ContMDiffMap.chartIteratedFDeriv_apply`,
-- so the left side is in simp normal form even in this dependent continuous-map space.
@[simp]
theorem chartMetricDerivative_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (m : ℕ) (z : (extChartAt I x).target) : withMetricOperatorNorms E in
    DFunLike.coe (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target),
      E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))) (g.chartMetricDerivative x m) z =
      iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z := (rfl)

/-! ### The chart Cᵏ topologies -/

section ChartCk

/-- The topology of uniform convergence on compact chart sets of coordinate derivatives of order
at most `k` on the native smooth Riemannian metric carrier. Orders `k = 2` and `k = ⊤` give the
chart C² and C∞ topologies `chartC2Topology` and `chartCInftyTopology`. -/
@[instance_reducible]
def chartCkTopology (k : ℕ∞) :
    TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  .induced (fun g ↦ fun (x : M) (m : {m : ℕ // (m : ℕ∞) ≤ k}) ↦ g.chartMetricDerivative x m)
    inferInstance

variable (k : ℕ∞)

/-- A family is Cᵏ-continuous exactly when all chart derivatives of order at most `k` are
continuous as maps into compact-open continuous-map spaces. -/
theorem continuous_chartCk_iff_continuous_chartMetricDerivative
    {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous g ↔ ∀ (x : M) (m : ℕ), (m : ℕ∞) ≤ k →
      Continuous (fun p ↦ (g p).chartMetricDerivative x m) := by
  simp only [continuous_induced_rng, continuous_pi_iff, Function.comp_def, Subtype.forall]

/-- Each coordinate derivative of order at most `k` varies continuously in the chart Cᵏ
topology. -/
theorem continuous_chartMetricDerivative (x : M) {m : ℕ} (hm : (m : ℕ∞) ≤ k) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.chartMetricDerivative x m) :=
  let _ := chartCkTopology (I := I) (M := M) k
  (continuous_chartCk_iff_continuous_chartMetricDerivative (I := I) (M := M) k).mp
    continuous_id x m hm

/-- The chart Cᵏ topologies decrease as `k` grows: a topology controlling derivatives of higher
order is finer. -/
theorem antitone_chartCkTopology :
    Antitone (chartCkTopology (I := I) (M := M)) := fun _ l hkl ↦
  let _ := chartCkTopology (I := I) (M := M) l
  continuous_iff_le_induced.1 (continuous_pi fun x ↦ continuous_pi fun m ↦
    continuous_chartMetricDerivative l x (m.2.trans hkl))

/-- A family is continuous in the chart Cᵏ topology exactly when its coordinate derivatives of
order at most `k` depend jointly continuously on the parameter and chart variable. -/
theorem continuous_chartCk_iff [LocallyCompactSpace E] {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    withMetricOperatorNorms E in
    letI := chartCkTopology (I := I) (M := M) k
    Continuous g ↔ ∀ (x : M) (m : ℕ), (m : ℕ∞) ≤ k →
      Continuous (fun q : P × (extChartAt I x).target ↦
        iteratedFDeriv ℝ m ((g q.1).toNondegenerateMetric.chartMetric x) q.2) := by
  rw [continuous_chartCk_iff_continuous_chartMetricDerivative]
  constructor
  · intro h x m hm
    let _ := (isOpen_extChartAt_target (I := I) x).locallyCompactSpace
    exact continuous_eval.comp ((h x m hm).prodMap continuous_id)
  · intro h x m hm
    exact ContinuousMap.continuous_of_continuous_uncurry _ (h x m hm)

/-- A coordinate derivative of order at most `k`, as a function of the metric and of a point of
the model space, is continuous at every point of the chart target. Away from the chart target the
iterated derivative is still defined, but carries no information about the metric. -/
theorem continuousAt_iteratedFDeriv_chartMetric [LocallyCompactSpace E] (x : M) {m : ℕ}
    (hm : (m : ℕ∞) ≤ k)
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I x).target) : withMetricOperatorNorms E in
    letI := chartCkTopology (I := I) (M := M) k
    ContinuousAt (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × E ↦
      iteratedFDeriv ℝ m (q.1.toNondegenerateMetric.chartMetric x) q.2) (g₀, z₀) := by
  let _ := chartCkTopology (I := I) (M := M) k
  have h := (continuous_chartCk_iff (I := I) (M := M) k (g := id)).1 continuous_id x m hm
  -- The chart target is open, so neighbourhoods of `z₀` in it are its neighbourhoods in `E`.
  have hmap : map (Prod.map id Subtype.val) (𝓝 (g₀, (⟨z₀, hz₀⟩ : (extChartAt I x).target))) =
      𝓝 (g₀, z₀) := by
    rw [nhds_prod_eq, nhds_prod_eq, ← prod_map_map_eq', map_id,
      map_nhds_subtype_coe_eq_nhds hz₀ ((isOpen_extChartAt_target x).mem_nhds hz₀)]
  rw [ContinuousAt, ← hmap, tendsto_map'_iff]
  exact h.continuousAt

/-- Convergence of metrics in the chart Cᵏ topology is uniform convergence on every compact
chart set of each coordinate derivative of order at most `k`. -/
theorem tendsto_chartCk_iff {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    withMetricOperatorNorms E in
    letI := chartCkTopology (I := I) (M := M) k
    Tendsto g l (𝓝 g₀) ↔ ∀ (x : M) (m : ℕ), (m : ℕ∞) ≤ k →
      ∀ (K : Set (extChartAt I x).target), IsCompact K →
        TendstoUniformlyOn
          (fun p (z : (extChartAt I x).target) ↦
            iteratedFDeriv ℝ m ((g p).toNondegenerateMetric.chartMetric x) z)
          (fun (z : (extChartAt I x).target) ↦
            iteratedFDeriv ℝ m (g₀.toNondegenerateMetric.chartMetric x) z) l K := by
  simp only [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds,
    Function.comp_def, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn,
    Subtype.forall, chartMetricDerivative]
  -- The coercions of the unfolded chart derivatives are taken on the spelled-out chart target
  -- `I.target ∩ I.symm ⁻¹' (chartAt H x).target`, which is `(extChartAt I x).target` by
  -- definition; `rfl` identifies the two forms, as the `change` in `continuous_inner_apply` does.
  rfl

/-- Evaluation of a metric on two fixed tangent vectors is continuous in the chart Cᵏ
topology. -/
theorem continuous_inner_apply (x : M) (v w : TangentSpace I x) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.inner x v w) := by
  let _ := chartCkTopology (I := I) (M := M) k
  let z : (extChartAt I x).target := ⟨extChartAt I x x, mem_extChartAt_target x⟩
  let e := (trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt E (TangentSpace I) x)
  have h := (continuous_eval_const z).comp
    (continuous_chartMetricDerivative (I := I) k x (m := 0) (by simp))
  have heval : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x) ↦ g.chartMetricDerivative x 0 z 0 (e v) (e w)) := by
    fun_prop
  convert heval using 1
  funext g
  -- Normalize the dependent coercion's chart target to match the simp-normal computation rule.
  change g.inner x v w = DFunLike.coe
    (F := C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target),
      E [×0]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))) (g.chartMetricDerivative x 0) z 0 (e v) (e w)
  rw [chartMetricDerivative_apply, iteratedFDeriv_zero_apply,
    g.toNondegenerateMetric.chartMetric_extChartAt_apply (mem_extChartAt_source x)]
  have hinv (u : TangentSpace I x) :
      (trivializationAt E (TangentSpace I) x).symm x (e u) = u := by
    simpa only [e, Trivialization.linearEquivAt_symm_apply] using e.symm_apply_apply u
  simp only [toNondegenerateMetric_apply, hinv]

/-- Each chart Cᵏ topology on smooth Riemannian metrics is Hausdorff: evaluation of the metric,
already controlled in order zero, separates metrics. -/
theorem t2Space_chartCk :
    @T2Space (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
      (chartCkTopology k) :=
  let _ := chartCkTopology (I := I) (M := M) k
  T2Space.of_injective_continuous
    (f := fun g ↦ fun x v w ↦ g.inner x v w)
    (fun _ _ heq ↦ ext fun x v w ↦ congrFun (congrFun (congrFun heq x) v) w)
    (continuous_pi fun x ↦ continuous_pi fun v ↦ continuous_pi fun w ↦
      continuous_inner_apply k x v w)

/-- The chart C² topology `chartCkTopology 2`, controlling coordinate derivatives through order
two. It is selected by `open scoped TauCeti.MetricC2`. -/
abbrev chartC2Topology :
    TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  chartCkTopology 2

/-- The chart C∞ topology `chartCkTopology ⊤`, controlling coordinate derivatives of every order.
It is selected by `open scoped TauCeti.MetricCInfty`. -/
abbrev chartCInftyTopology :
    TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  chartCkTopology ⊤

end ChartCk

/-- The chart C∞ topology is finer than the chart C² topology. -/
theorem chartCInftyTopology_le_chartC2Topology :
    chartCInftyTopology (I := I) (M := M) ≤ chartC2Topology :=
  antitone_chartCkTopology le_top

/-- A set of metrics that is compact in a chart Cˡ topology is compact in every coarser chart Cᵏ
topology, `k ≤ l`. The two topologies on the same carrier are given explicitly, since instance
search would supply only one of them. -/
theorem _root_.IsCompact.chartCk_of_le {k l : ℕ∞}
    {K : Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))}
    (hK : @IsCompact _ (chartCkTopology l) K) (hkl : k ≤ l) :
    @IsCompact _ (chartCkTopology k) K := by
  have h := @IsCompact.image _ _ (chartCkTopology l) (chartCkTopology k) K id hK
    (continuous_id_of_le (antitone_chartCkTopology hkl))
  rwa [image_id] at h

end Bundle.ContMDiffRiemannianMetric

/-! ### Jets of smoothly parametrised families

These statements are outside the namespace block above, so their public signatures do not use
its cached private operator-space instances. -/

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {P V : Type*} [TopologicalSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)

/-- Suppose that on the chart target at `x` the chart metrics of `g p` are `F (ψ p, ·)`, for a
continuous map `ψ` of the parameter space into a normed space and a function `F` smooth on the
product of that space with the chart target. Then the Gram matrices and the first and second
derivatives of the chart metrics vary continuously with the parameter and the chart point, as
required by `TauCeti.Manifold.exists_pos_eventually_forall_le_scalarCurvature`. -/
theorem continuousAt_chartMetric_jets
    (g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x : M)
    {ψ : P → V} (hψ : Continuous ψ) {F : V × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ (extChartAt I x).target))
    (hgF : ∀ p, ∀ z ∈ (extChartAt I x).target,
      (g p).toNondegenerateMetric.chartMetric x z = F (ψ p, z)) (p₀ : P) :
    ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm) (p₀, extChartAt I x x) ∧
    ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (p₀, extChartAt I x x) ∧
    ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j))
        z (b k)) r.2 (b m)) (p₀, extChartAt I x x) := by
  set T := (extChartAt I x).target
  have hT : IsOpen T := isOpen_extChartAt_target x
  have hU : IsOpen (univ ×ˢ T) := (isOpen_univ (X := V)).prod hT
  have hq₀ : (ψ p₀, extChartAt I x x) ∈ univ ×ˢ T := ⟨trivial, mem_extChartAt_target x⟩
  -- The parameter and chart point enter through `Φ`, and near the base point the chart point
  -- stays in the open chart target.
  set Φ : P × E → V × E := fun r ↦ (ψ r.1, r.2)
  have hΦ : ContinuousAt Φ (p₀, extChartAt I x x) :=
    ((hψ.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hev : ∀ᶠ r : P × E in 𝓝 (p₀, extChartAt I x x), r.2 ∈ T :=
    continuousAt_snd.preimage_mem_nhds (hT.mem_nhds (mem_extChartAt_target x))
  have hcont {G : V × E → ℝ} (hG : ContDiffOn ℝ ∞ G (univ ×ˢ T)) :
      ContinuousAt (fun r ↦ G (Φ r)) (p₀, extChartAt I x x) :=
    ContinuousAt.comp (f := Φ) (hG.continuousOn.continuousAt (hU.mem_nhds hq₀)) hΦ
  -- Partial derivatives in the chart point of functions smooth on `univ ×ˢ T` are smooth there.
  have hD {G : V × E → ℝ} (hG : ContDiffOn ℝ ∞ G (univ ×ˢ T)) (w : E) :
      ContDiffOn ℝ ∞ (fun q : V × E ↦ fderiv ℝ (fun z ↦ G (q.1, z)) q.2 w) (univ ×ˢ T) := by
    intro q hq
    have hGq : ContDiffAt ℝ ∞ (fun r : (V × E) × E ↦ G (r.1.1, r.2)) (q, q.2) :=
      (hG.contDiffAt (hU.mem_nhds hq)).comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact ((ContDiffAt.fderiv (f := fun (q : V × E) z ↦ G (q.1, z)) hGq contDiffAt_snd
      (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  -- The entries of `F` and their first two partial derivatives in the chart point.
  have hF₀ (i j : ι) : ContDiffOn ℝ ∞ (fun q ↦ F q (b i) (b j)) (univ ×ˢ T) :=
    (hF.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hF₁ (k i j : ι) := hD (hF₀ i j) (b k)
  have hF₂ (m k i j : ι) := hD (hF₁ k i j) (b m)
  -- Near a point of the chart target, the entries of the chart metric are those of `F`.
  have heq (p : P) {z : E} (hz : z ∈ T) (i j : ι) :
      (fun z' ↦ (g p).toNondegenerateMetric.chartMetric x z' (b i) (b j)) =ᶠ[𝓝 z]
        fun z' ↦ F (ψ p, z') (b i) (b j) := by
    filter_upwards [hT.mem_nhds hz] with z' hz'
    rw [hgF p z' hz']
  refine ⟨?_, ?_, ?_⟩
  · refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    refine (hcont (hF₀ i j)).congr ?_
    filter_upwards [hev] with r hr
    simp [LinearMap.toMatrix₂_apply, hgF r.1 r.2 hr, Φ]
  · refine continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    refine (hcont (hF₁ k i j)).congr ?_
    filter_upwards [hev] with r hr
    rw [(heq r.1 hr i j).fderiv_eq]
  · refine continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
      continuousAt_pi.2 fun j ↦ ?_
    refine (hcont (hF₂ m k i j)).congr ?_
    filter_upwards [hev] with r hr
    have heq₁ : (fun z ↦ fderiv ℝ
        (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j)) z (b k)) =ᶠ[𝓝 r.2]
        fun z ↦ fderiv ℝ (fun z' ↦ F (ψ r.1, z') (b i) (b j)) z (b k) := by
      filter_upwards [hT.mem_nhds hr] with z hz
      rw [(heq r.1 hz i j).fderiv_eq]
    rw [heq₁.fderiv_eq]

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

scoped[TauCeti.MetricC2] attribute [instance] Bundle.ContMDiffRiemannianMetric.chartC2Topology

scoped[TauCeti.MetricC2] attribute [instance] Bundle.ContMDiffRiemannianMetric.t2Space_chartCk

scoped[TauCeti.MetricCInfty] attribute [instance]
  Bundle.ContMDiffRiemannianMetric.chartCInftyTopology

scoped[TauCeti.MetricCInfty] attribute [instance]
  Bundle.ContMDiffRiemannianMetric.t2Space_chartCk

end TauCeti
