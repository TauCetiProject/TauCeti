/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology

/-!
# Constant rescaling in families of Riemannian metrics

Positive constant rescaling is jointly continuous in the metric and the scale for every chart
Cᵏ topology, including C² and C∞. The scale may vary continuously with the parameter of a family;
it is constant only in the spatial variable. In coordinates, every derivative of the rescaled
metric is the same scalar multiple of the original derivative.

For a fixed positive scale, `Bundle.ContMDiffRiemannianMetric.rescaleHomeomorph` is the resulting
homeomorphism of the native smooth metric space, with inverse given by reciprocal scaling.
These results concern boundaryless manifolds, as do the chart Cᵏ topologies. They require neither
compactness of the manifold nor a bound on the order `k`.

The topology and coordinate-derivative argument follow
`Bundle.ContMDiffRiemannianMetric.continuous_convexCombination`.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- As in the chart topology module, cache the canonical operator norms to keep inference for
-- iterated multilinear maps into the space of bilinear forms within the instance-search limit.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Constant rescaling multiplies the coordinate bilinear form by the same constant. -/
theorem chartMetric_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)).toNondegenerateMetric.chartMetric x z =
      c • g.toNondegenerateMetric.chartMetric x z := by
  ext v w
  simp only [TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_apply _ hz,
    toNondegenerateMetric_apply, rescale_inner, smul_apply, smul_eq_mul]

variable [I.Boundaryless]

/-- Each spatial coordinate derivative of a constantly rescaled metric is multiplied by the
scale, in every order. -/
theorem iteratedFDeriv_chartMetric_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (m : ℕ) {z : E}
    (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m
        ((g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)).toNondegenerateMetric.chartMetric x)
        z = c • iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z := by
  have heq :
      (g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)).toNondegenerateMetric.chartMetric x
      =ᶠ[𝓝 z] fun y ↦ c • g.toNondegenerateMetric.chartMetric x y := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartMetric_rescale_const g hc x hy
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' ((g.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz) |>.of_le (by simp))]

/-- Constant rescaling of a Cᵏ-continuous family by a continuous positive scale remains
Cᵏ-continuous. The scale may depend on the family parameter, and `k = ⊤` gives C∞ continuity. -/
@[fun_prop]
theorem continuous_rescale_const_chartCk (k : ℕ∞)
    {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {c : P → ℝ} (hc : ∀ p, 0 < c p) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous g → Continuous c →
      Continuous (fun p ↦ (g p).rescale (fun _ ↦ c p) contMDiff_const (fun _ ↦ hc p)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  intro hg hc'
  rw [continuous_chartCk_iff_continuous_chartMetricDerivative] at hg ⊢
  intro x m hm
  -- Cache the derivative-space instances for scalar multiplication of continuous maps.
  let _ : NormedAddCommGroup (E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
  let _ : NormedSpace ℝ (E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
  let _ : SMul ℝ (E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
  let _ : ContinuousSMul ℝ (E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
  let _ : SMul ℝ C((extChartAt I x).target,
    E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
  have heq : (fun p : P ↦ ((g p).rescale (fun _ ↦ c p) contMDiff_const
      (fun _ ↦ hc p)).chartMetricDerivative x m) =
      (fun p : P ↦ c p • (g p).chartMetricDerivative x m) := by
    funext p
    apply ContinuousMap.ext
    intro z
    rw [ContinuousMap.smul_apply]
    exact (chartMetricDerivative_apply _ x m z).trans
      ((iteratedFDeriv_chartMetric_rescale_const (g p) (hc p) x m z.property).trans
        (congrArg (fun d : E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) ↦ c p • d)
          (chartMetricDerivative_apply (g p) x m z).symm))
  rw [heq]
  exact Continuous.smul (M := ℝ) hc' (hg x m hm)

/-- Rescaling by a fixed positive constant is a homeomorphism for every chart Cᵏ topology.
Its inverse rescales by the reciprocal constant. -/
def rescaleHomeomorph (k : ℕ∞) {c : ℝ} (hc : 0 < c) :
    letI := chartCkTopology (I := I) (M := M) k
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ≃ₜ
      ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) := by
  letI := chartCkTopology (I := I) (M := M) k
  exact
    { toFun := fun g ↦ g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)
      invFun := fun g ↦ g.rescale (fun _ ↦ c⁻¹) contMDiff_const (fun _ ↦ inv_pos.mpr hc)
      left_inv := fun g ↦ g.rescale_inv_rescale
      right_inv := fun g ↦ g.rescale_rescale_inv
      continuous_toFun := continuous_rescale_const_chartCk k (fun _ ↦ hc)
        continuous_id continuous_const
      continuous_invFun := continuous_rescale_const_chartCk k (fun _ ↦ inv_pos.mpr hc)
        continuous_id continuous_const }

/-- The rescaling homeomorphism acts by the original native rescaling operation. -/
@[simp]
theorem rescaleHomeomorph_apply (k : ℕ∞) {c : ℝ} (hc : 0 < c)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    letI := chartCkTopology (I := I) (M := M) k
    rescaleHomeomorph k hc g = g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) := (rfl)

/-- The inverse rescaling homeomorphism acts by reciprocal scaling. -/
@[simp]
theorem rescaleHomeomorph_symm_apply (k : ℕ∞) {c : ℝ} (hc : 0 < c)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    letI := chartCkTopology (I := I) (M := M) k
    (rescaleHomeomorph k hc).symm g =
      g.rescale (fun _ ↦ c⁻¹) contMDiff_const (fun _ ↦ inv_pos.mpr hc) := (rfl)

end Bundle.ContMDiffRiemannianMetric
