/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Convex interpolation of Riemannian metrics

`Bundle.ContMDiffRiemannianMetric.convexCombination g h t` is the metric
`(1 - t) g + t h`, for `t` in the unit interval. It is the constant-weight case of
`Bundle.ContMDiffRiemannianMetric.convexCombinationFun g h f`, the metric `(1 - f) g + f h` for
a `C^n` weight `f` on the base with values in `[0, 1]`; for instance, a weight depending only on
`t` interpolates two cylinder metrics on `M × ℝ` along the cylinder. The construction uses the
positive symmetric bilinear sections, and allows arbitrary regularity and boundary charts.
It preserves the metric at every point where the two input metrics agree.

For smooth tangent metrics on a boundaryless manifold, interpolation is jointly continuous
in both metrics and the interval parameter for the chart C² topology. The coordinate
derivatives of every order interpolate linearly. For a fixed smooth weight `f`, interpolation
is jointly continuous in both metrics for every chart Cᵏ topology
(`Bundle.ContMDiffRiemannianMetric.continuous_convexCombinationFun`): the Leibniz rule bounds
the derivatives of `(1 - f) (g - g₀) + f (h - h₀)` on compact chart sets by those of `g - g₀`
and `h - h₀` of no larger order. These facts allow local combinations of metrics in
approximation arguments, including arguments relative to a fixed spatial region.
They do not assert that scalar positivity is preserved by convex combinations.

The ambient section space and its positive cone are those of
`Bundle.ContMDiffRiemannianMetric.positiveDefiniteSectionEquiv`.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

section VectorBundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Convex interpolation of two finite-rank Riemannian metrics with a weight varying over the
base: over `x` it is `(1 - f x) g + f x h`, for a `C^n` function `f` with values in `[0, 1]`.
This preserves positive definiteness, not necessarily positive scalar curvature. -/
def convexCombinationFun (g h : ContMDiffRiemannianMetric IB n F V) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    ContMDiffRiemannianMetric IB n F V :=
  ofPositiveDefiniteSection
    ⟨fun x ↦ (1 - f x) • g.inner x + f x • h.inner x,
      ((contMDiff_const.sub hf).smul_section g.contMDiff).add_section
        (hf.smul_section h.contMDiff)⟩
    ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ by
          simp [g.symm x v w, h.symm x v w],
        fun x v hv ↦ by
          simpa using ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).1
            (TauCeti.Manifold.convex_positiveDefiniteBilinearSections
              g.toBilinearSection_mem h.toBilinearSection_mem (sub_nonneg.2 (hf₁ x)) (hf₀ x)
              (sub_add_cancel 1 (f x)))).2 x v hv⟩)

/-- The inner product of a metric interpolated with a varying weight is the weighted sum of
inner products. -/
@[simp]
theorem convexCombinationFun_inner (g h : ContMDiffRiemannianMetric IB n F V) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) (x : B)
    (v w : V x) :
    (g.convexCombinationFun h f hf hf₀ hf₁).inner x v w =
      (1 - f x) * g.inner x v w + f x * h.inner x v w := by
  simp [convexCombinationFun]

/-- Convex interpolation of two finite-rank Riemannian metrics, with weights `1 - t` and `t`.
This preserves positive definiteness, not necessarily positive scalar curvature. -/
def convexCombination (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    ContMDiffRiemannianMetric IB n F V :=
  g.convexCombinationFun h (fun _ ↦ (t : ℝ)) contMDiff_const (fun _ ↦ t.property.1)
    (fun _ ↦ t.property.2)

/-- Interpolation with a constant weight is `convexCombination`. -/
@[simp]
theorem convexCombinationFun_const (g h : ContMDiffRiemannianMetric IB n F V)
    (t : unitInterval) :
    g.convexCombinationFun h (fun _ ↦ (t : ℝ)) contMDiff_const (fun _ ↦ t.property.1)
      (fun _ ↦ t.property.2) = g.convexCombination h t :=
  (rfl)

/-- The inner product of an interpolated metric is the weighted sum of inner products. -/
@[simp]
theorem convexCombination_inner
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) (x : B) (v w : V x) :
    (g.convexCombination h t).inner x v w =
      (1 - (t : ℝ)) * g.inner x v w + (t : ℝ) * h.inner x v w := by
  rw [← convexCombinationFun_const, convexCombinationFun_inner]

/-- The underlying section of an interpolated metric is the same convex combination. -/
@[simp]
theorem toBilinearSection_convexCombination
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    (g.convexCombination h t).toBilinearSection =
      (1 - (t : ℝ)) • g.toBilinearSection + (t : ℝ) • h.toBilinearSection := by
  ext x v w
  simp

/-- Interpolation starts at the first metric. -/
@[simp]
theorem convexCombination_zero (g h : ContMDiffRiemannianMetric IB n F V) :
    g.convexCombination h 0 = g := by
  ext x v w
  simp

/-- Interpolation ends at the second metric. -/
@[simp]
theorem convexCombination_one (g h : ContMDiffRiemannianMetric IB n F V) :
    g.convexCombination h 1 = h := by
  ext x v w
  simp

/-- Interpolating a metric with itself, with any weight, leaves it unchanged. -/
@[simp]
theorem convexCombinationFun_self (g : ContMDiffRiemannianMetric IB n F V) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    g.convexCombinationFun g f hf hf₀ hf₁ = g := by
  ext x v w
  simp only [convexCombinationFun_inner]
  ring

/-- Interpolating a metric with itself leaves it unchanged. -/
@[simp]
theorem convexCombination_self (g : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) :
    g.convexCombination g t = g := by
  rw [← convexCombinationFun_const, convexCombinationFun_self]

/-- At any point where the two metrics agree, interpolation fixes their common inner product.
In particular, interpolation preserves prescribed data on a neighbourhood of a closed subset. -/
theorem convexCombination_inner_eq_of_eq
    (g h : ContMDiffRiemannianMetric IB n F V) (t : unitInterval) {x : B}
    (hx : g.inner x = h.inner x) : (g.convexCombination h t).inner x = g.inner x := by
  ext v w
  rw [convexCombination_inner, ← hx]
  ring

end VectorBundle

section TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Cache the canonical operator norms, as in the chart C² topology module: inference for
-- iterated multilinear maps into nested operator spaces otherwise exhausts heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] in
/-- On a chart target, the coordinate bilinear form of a metric interpolated with a varying
weight is the interpolation of the coordinate bilinear forms, with the weight read through the
inverse chart. -/
theorem chartMetric_convexCombinationFun
    (g h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) (x : M) {z : E}
    (hz : z ∈ (extChartAt I x).target) :
    (g.convexCombinationFun h f hf hf₀ hf₁).toNondegenerateMetric.chartMetric x z =
      (1 - f ((extChartAt I x).symm z)) • g.toNondegenerateMetric.chartMetric x z +
        f ((extChartAt I x).symm z) • h.toNondegenerateMetric.chartMetric x z := by
  ext v w
  simp only [(g.convexCombinationFun h f hf hf₀ hf₁).toNondegenerateMetric.chartMetric_apply hz,
    g.toNondegenerateMetric.chartMetric_apply hz, h.toNondegenerateMetric.chartMetric_apply hz,
    toNondegenerateMetric_apply, convexCombinationFun_inner, add_apply, smul_apply,
    smul_eq_mul]

omit [I.Boundaryless] in
/-- On a chart target, the coordinate bilinear form of an interpolated metric is the
interpolation of the coordinate bilinear forms. -/
theorem chartMetric_convexCombination
    (g h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (t : unitInterval) (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.convexCombination h t).toNondegenerateMetric.chartMetric x z =
      (1 - (t : ℝ)) • g.toNondegenerateMetric.chartMetric x z +
        (t : ℝ) • h.toNondegenerateMetric.chartMetric x z :=
  chartMetric_convexCombinationFun g h _ _ _ _ x hz

/-- Every coordinate derivative of an interpolated metric is the corresponding weighted sum.
The weights are constant in the spatial variable. -/
theorem iteratedFDeriv_chartMetric_convexCombination
    (g h : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (t : unitInterval) (x : M) (m : ℕ) {z : E} (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m ((g.convexCombination h t).toNondegenerateMetric.chartMetric x) z =
      (1 - (t : ℝ)) • iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z +
        (t : ℝ) • iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric x) z := by
  have hg := (g.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hz)
  have hh := (h.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hz)
  have heq : (g.convexCombination h t).toNondegenerateMetric.chartMetric x =ᶠ[𝓝 z]
      (fun y ↦ (1 - (t : ℝ)) • g.toNondegenerateMetric.chartMetric x y +
        (t : ℝ) • h.toNondegenerateMetric.chartMetric x y) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartMetric_convexCombination g h t x hy
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds,
    fun_iteratedFDeriv_add_apply ((hg.of_le (by simp)).const_smul _)
      ((hh.of_le (by simp)).const_smul _),
    iteratedFDeriv_const_smul_apply' (hg.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hh.of_le (by simp))]

open scoped TauCeti.MetricC2

/-- C²-continuous families remain C²-continuous under convex interpolation with a continuous
interval-valued parameter. Both endpoint metrics may vary. -/
@[fun_prop]
theorem continuous_convexCombination {P : Type*} [TopologicalSpace P]
    {g h : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {t : P → unitInterval} (hg : Continuous g) (hh : Continuous h) (ht : Continuous t) :
    Continuous (fun p ↦ (g p).convexCombination (h p) (t p)) := by
  rw [continuous_chartCk_iff] at hg hh ⊢
  intro x m hm
  have hformula : (fun q : P × (extChartAt I x).target ↦
      iteratedFDeriv ℝ m ((g q.1).convexCombination (h q.1) (t q.1)
        |>.toNondegenerateMetric.chartMetric x) q.2) =
      (fun q : P × (extChartAt I x).target ↦
        (1 - (t q.1 : ℝ)) • iteratedFDeriv ℝ m ((g q.1).toNondegenerateMetric.chartMetric x) q.2 +
        (t q.1 : ℝ) • iteratedFDeriv ℝ m ((h q.1).toNondegenerateMetric.chartMetric x) q.2) := by
    funext q
    exact iteratedFDeriv_chartMetric_convexCombination _ _ _ _ _ q.2.property
  rw [hformula]
  have hc : Continuous (fun q : P × (extChartAt I x).target ↦ (t q.1 : ℝ)) :=
    ht.subtype_val.comp continuous_fst
  have hleft := ((continuous_const (y := (1 : ℝ))).sub hc).smul (hg x m hm)
  have hright := hc.smul (hh x m hm)
  exact hleft.add hright

omit [FiniteDimensional ℝ E] in
/-- For a coefficient `c` that is smooth on a chart target, the coordinate derivatives of order
`m ≤ k` of `c (g - g₀)` tend to zero uniformly on compact subsets of the target as `g` tends to `g₀`
in the chart Cᵏ topology. This is the Leibniz bound
`ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp`. -/
private theorem tendstoUniformlyOn_iteratedFDerivWithin_smul_chartMetric_sub (k : ℕ∞)
    {ι : Type*} {l : Filter ι}
    {g : ι → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : letI := chartCkTopology (I := I) (M := M) k; Tendsto g l (𝓝 g₀)) (x : M) {m : ℕ}
    (hm : (m : ℕ∞) ≤ k) {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c (extChartAt I x).target)
    {K : Set E} (hKU : K ⊆ (extChartAt I x).target) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i z ↦ iteratedFDerivWithin ℝ m (fun y ↦
        c y • ((g i).toNondegenerateMetric.chartMetric x y -
          g₀.toNondegenerateMetric.chartMetric x y)) (extChartAt I x).target z)
      (fun _ ↦ 0) l K := by
  have hU : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  -- The map `y ↦ c y • (g i - g₀) y` is `y ↦ L y ((g i - g₀) (id y))` for `L y = c y • id`.
  have hL := contDiffOn_infty.mp (hc.smul (contDiffOn_const
    (c := ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)))) m
  have hform (i : ι) : (fun y ↦ (c y • ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ))
      (((g i).toNondegenerateMetric.chartMetric x - g₀.toNondegenerateMetric.chartMetric x)
        (id y))) = fun y ↦ c y • ((g i).toNondegenerateMetric.chartMetric x y -
          g₀.toNondegenerateMetric.chartMetric x y) := by
    funext y
    simp only [smul_apply, ContinuousLinearMap.id_apply, id, Pi.sub_apply]
  simp_rw [← hform]
  refine hL.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp contDiffOn_id hU.uniqueDiffOn
    hU.uniqueDiffOn (mapsTo_id _) hK hKU (Eventually.of_forall fun i ↦ contDiffOn_infty.mp
      (((g i).toNondegenerateMetric.contDiffOn_chartMetric x).sub
        (g₀.toNondegenerateMetric.contDiffOn_chartMetric x)) m) fun j hj ↦ ?_
  refine Metric.tendstoUniformlyOn_iff.mpr fun δ hδ ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ((tendsto_chartCk_iff k).mp hg x j
    ((Nat.cast_le.2 hj).trans hm) K hKU hK) δ hδ] with i hi z hzK
  have hz := hU.mem_nhds (hKU hzK)
  rw [id, iteratedFDerivWithin_of_isOpen j hU (hKU hzK), iteratedFDeriv_sub_apply
      (contDiffAt_infty.mp (((g i).toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt hz) j)
      (contDiffAt_infty.mp ((g₀.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt hz) j),
    dist_zero_left, ← dist_eq_norm, dist_comm]
  exact hi z hzK

/-- On a chart target, the coordinate derivatives of two interpolations with the same weight `f`
differ by those of `(1 - f) (g - g₀) + f (h - h₀)`, with the weight read through the inverse
chart. -/
private theorem iteratedFDeriv_chartMetric_convexCombinationFun_sub
    (g h g₀ h₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) (x : M) (m : ℕ)
    {z : E} (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m ((g.convexCombinationFun h f hf hf₀ hf₁).toNondegenerateMetric.chartMetric
        x) z -
      iteratedFDeriv ℝ m
        ((g₀.convexCombinationFun h₀ f hf hf₀ hf₁).toNondegenerateMetric.chartMetric x) z =
    iteratedFDerivWithin ℝ m (fun y ↦ (1 - f ((extChartAt I x).symm y)) •
        (g.toNondegenerateMetric.chartMetric x y - g₀.toNondegenerateMetric.chartMetric x y))
        (extChartAt I x).target z +
      iteratedFDerivWithin ℝ m (fun y ↦ f ((extChartAt I x).symm y) •
        (h.toNondegenerateMetric.chartMetric x y - h₀.toNondegenerateMetric.chartMetric x y))
        (extChartAt I x).target z := by
  have hU : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  have hnhds := hU.mem_nhds hz
  have hw : ContDiffOn ℝ ∞ (fun y ↦ f ((extChartAt I x).symm y)) (extChartAt I x).target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
  have hchart (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
      ContDiffOn ℝ ∞ (g.toNondegenerateMetric.chartMetric x) (extChartAt I x).target :=
    g.toNondegenerateMetric.contDiffOn_chartMetric x
  have heq : (g.convexCombinationFun h f hf hf₀ hf₁).toNondegenerateMetric.chartMetric x -
      (g₀.convexCombinationFun h₀ f hf hf₀ hf₁).toNondegenerateMetric.chartMetric x =ᶠ[𝓝 z]
      fun y ↦ (1 - f ((extChartAt I x).symm y)) •
          (g.toNondegenerateMetric.chartMetric x y - g₀.toNondegenerateMetric.chartMetric x y) +
        f ((extChartAt I x).symm y) •
          (h.toNondegenerateMetric.chartMetric x y - h₀.toNondegenerateMetric.chartMetric x y) := by
    filter_upwards [hnhds] with y hy
    simp only [Pi.sub_apply, chartMetric_convexCombinationFun _ _ _ _ _ _ _ hy]
    module
  have h₁ : ContDiffAt ℝ m (fun y ↦ (1 - f ((extChartAt I x).symm y)) •
      (g.toNondegenerateMetric.chartMetric x y - g₀.toNondegenerateMetric.chartMetric x y)) z :=
    contDiffAt_infty.mp ((((contDiffOn_const (c := (1 : ℝ))).sub hw).smul
      ((hchart g).sub (hchart g₀))).contDiffAt hnhds) m
  have h₂ : ContDiffAt ℝ m (fun y ↦ f ((extChartAt I x).symm y) •
      (h.toNondegenerateMetric.chartMetric x y - h₀.toNondegenerateMetric.chartMetric x y)) z :=
    contDiffAt_infty.mp ((hw.smul ((hchart h).sub (hchart h₀))).contDiffAt hnhds) m
  rw [iteratedFDerivWithin_of_isOpen m hU hz, iteratedFDerivWithin_of_isOpen m hU hz,
    ← iteratedFDeriv_sub_apply (contDiffAt_infty.mp ((hchart _).contDiffAt hnhds) m)
      (contDiffAt_infty.mp ((hchart _).contDiffAt hnhds) m),
    ← fun_iteratedFDeriv_add_apply h₁ h₂]
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

/-- For a fixed smooth weight `f` with values in `[0, 1]`, interpolation `(1 - f) g + f h` is
jointly continuous in the two metrics `g` and `h` for every chart Cᵏ topology. -/
theorem continuous_convexCombinationFun (k : ℕ∞) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ×
        ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      q.1.convexCombinationFun q.2 f hf hf₀ hf₁) := by
  let _ := chartCkTopology (I := I) (M := M) k
  refine continuous_iff_continuousAt.mpr fun q₀ ↦ (tendsto_chartCk_iff k).mpr
    fun x m hm K hKU hK ↦ ?_
  have hw : ContDiffOn ℝ ∞ (fun y ↦ f ((extChartAt I x).symm y)) (extChartAt I x).target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
  have h₁ := tendstoUniformlyOn_iteratedFDerivWithin_smul_chartMetric_sub k
    (continuous_fst.tendsto q₀) x hm ((contDiffOn_const (c := (1 : ℝ))).sub hw) hKU hK
  have h₂ := tendstoUniformlyOn_iteratedFDerivWithin_smul_chartMetric_sub k
    (continuous_snd.tendsto q₀) x hm hw hKU hK
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h₁ (ε / 2) (half_pos hε),
    Metric.tendstoUniformlyOn_iff.mp h₂ (ε / 2) (half_pos hε)] with q hq₁ hq₂ z hz
  have hz₁ := hq₁ z hz
  have hz₂ := hq₂ z hz
  rw [dist_zero_left] at hz₁ hz₂
  rw [dist_comm, dist_eq_norm,
    iteratedFDeriv_chartMetric_convexCombinationFun_sub _ _ _ _ f hf hf₀ hf₁ x m (hKU hz)]
  calc _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hz₁ hz₂
    _ = ε := add_halves ε

end TangentBundle

end Bundle.ContMDiffRiemannianMetric
