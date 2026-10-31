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
# The chart C² topology on smooth Riemannian metrics

`Bundle.ContMDiffRiemannianMetric.chartC2Topology` equips the native smooth metric carrier
with the initial topology of its coordinate derivatives of orders zero, one and two. Each
derivative is a continuous map on an extended chart target, with its compact-open topology.
Thus convergence means uniform convergence of all three derivatives on every compact subset
of every chart target. Derivatives take values in continuous multilinear maps with the
operator norm; no basis of the model space is chosen.

The family criterion `continuous_chartC2_iff` expresses continuity by joint continuity of the
coordinate derivatives in the parameter and chart variable; in particular each coordinate
derivative is jointly continuous in the metric and the chart variable
(`continuousAt_iteratedFDeriv_chartMetric`). Conversely, for a family whose chart metrics depend
smoothly on a continuous parameter, `continuousAt_chartMetric_jets` gives joint continuity of the
Gram matrices and their first two partial derivatives in a basis. Evaluation of the metric at a
fixed point is continuous, and these evaluations separate metrics. The topology is selected
by `open scoped TauCeti.MetricC2`, rather than a global instance, so it can coexist with
topologies controlling higher derivatives.

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

/-- The topology of uniform convergence on compact chart sets of coordinate derivatives
through order two on the native smooth Riemannian metric carrier. -/
@[instance_reducible]
def chartC2Topology :
    TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  .induced (fun g ↦ fun (x : M) (m : Fin 3) ↦ g.chartMetricDerivative x m) inferInstance

attribute [local instance] chartC2Topology

/-- A family is C²-continuous exactly when all chart derivatives through order two are
continuous as maps into compact-open continuous-map spaces. -/
theorem continuous_chartC2_iff_continuous_chartMetricDerivative
    {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    Continuous g ↔ ∀ (x : M) (m : Fin 3),
      Continuous (fun p ↦ (g p).chartMetricDerivative x m) := by
  simp only [continuous_induced_rng, continuous_pi_iff, Function.comp_def]

/-- Each coordinate derivative through order two varies continuously in the chart C² topology. -/
theorem continuous_chartMetricDerivative (x : M) (m : Fin 3) :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.chartMetricDerivative x m) :=
  (continuous_chartC2_iff_continuous_chartMetricDerivative (I := I) (M := M)).mp
    continuous_id x m

/-- A family is continuous in the chart C² topology exactly when its coordinate derivatives
through order two depend jointly continuously on the parameter and chart variable. -/
theorem continuous_chartC2_iff [LocallyCompactSpace E] {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    withMetricOperatorNorms E in
    Continuous g ↔ ∀ (x : M) (m : Fin 3),
      Continuous (fun q : P × (extChartAt I x).target ↦
        iteratedFDeriv ℝ m ((g q.1).toNondegenerateMetric.chartMetric x) q.2) := by
  rw [continuous_chartC2_iff_continuous_chartMetricDerivative]
  constructor
  · intro h x m
    let _ := (isOpen_extChartAt_target (I := I) x).locallyCompactSpace
    exact continuous_eval.comp ((h x m).prodMap continuous_id)
  · intro h x m
    exact ContinuousMap.continuous_of_continuous_uncurry _ (h x m)

/-- A coordinate derivative through order two, as a function of the metric and of a point of the
model space, is continuous at every point of the chart target. Away from the chart target the
iterated derivative is still defined, but carries no information about the metric. -/
theorem continuousAt_iteratedFDeriv_chartMetric [LocallyCompactSpace E] (x : M) (m : Fin 3)
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I x).target) : withMetricOperatorNorms E in
    ContinuousAt (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × E ↦
      iteratedFDeriv ℝ m (q.1.toNondegenerateMetric.chartMetric x) q.2) (g₀, z₀) := by
  have h := (continuous_chartC2_iff (I := I) (M := M) (g := id)).1 continuous_id x m
  -- The chart target is open, so neighbourhoods of `z₀` in it are its neighbourhoods in `E`.
  have hmap : map (Prod.map id Subtype.val) (𝓝 (g₀, (⟨z₀, hz₀⟩ : (extChartAt I x).target))) =
      𝓝 (g₀, z₀) := by
    rw [nhds_prod_eq, nhds_prod_eq, ← prod_map_map_eq', map_id,
      map_nhds_subtype_coe_eq_nhds hz₀ ((isOpen_extChartAt_target x).mem_nhds hz₀)]
  rw [ContinuousAt, ← hmap, tendsto_map'_iff]
  exact h.continuousAt

/-- Convergence of metrics in the chart C² topology is uniform convergence on every compact
chart set of each coordinate derivative of order at most two. -/
theorem tendsto_chartC2_iff {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    withMetricOperatorNorms E in
    Tendsto g l (𝓝 g₀) ↔ ∀ (x : M) (m : Fin 3)
      (K : Set (extChartAt I x).target), IsCompact K →
        TendstoUniformlyOn
          (fun p (z : (extChartAt I x).target) ↦
            iteratedFDeriv ℝ m ((g p).toNondegenerateMetric.chartMetric x) z)
          (fun (z : (extChartAt I x).target) ↦
            iteratedFDeriv ℝ m (g₀.toNondegenerateMetric.chartMetric x) z) l K := by
  simp only [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds,
    Function.comp_def, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn,
    chartMetricDerivative]
  rfl

/-- Evaluation of a metric on two fixed tangent vectors is continuous in the chart C² topology. -/
theorem continuous_inner_apply (x : M) (v w : TangentSpace I x) :
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.inner x v w) := by
  let z : (extChartAt I x).target := ⟨extChartAt I x x, mem_extChartAt_target x⟩
  let e := (trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt E (TangentSpace I) x)
  have h := (continuous_eval_const z).comp
    (continuous_chartMetricDerivative (I := I) x 0)
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

/-- The chart C² topology on smooth Riemannian metrics is Hausdorff. -/
theorem t2Space_chartC2 :
    T2Space (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  T2Space.of_injective_continuous
    (f := fun g ↦ fun x v w ↦ g.inner x v w)
    (fun _ _ heq ↦ ext fun x v w ↦ congrFun (congrFun (congrFun heq x) v) w)
    (continuous_pi fun x ↦ continuous_pi fun v ↦ continuous_pi fun w ↦
      continuous_inner_apply x v w)

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

scoped[TauCeti.MetricC2] attribute [instance] Bundle.ContMDiffRiemannianMetric.t2Space_chartC2

end TauCeti
