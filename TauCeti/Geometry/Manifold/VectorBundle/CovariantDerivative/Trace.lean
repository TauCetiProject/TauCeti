/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant differentiation commutes with the metric trace

Let `∇` be a connection on the tangent bundle of a Riemannian manifold which is compatible with
the metric, and let `b` be a field of bilinear forms on the tangent spaces. The metric trace
`tr_g b` is then a function on the manifold whose derivative is the metric trace of the covariant
derivative of `b`:

`d (tr_g b)(v) = ∑ᵢ (∇_v b)(eᵢ, eᵢ)`

for every orthonormal basis `eᵢ` of the tangent space at the point. Since the metric is parallel,
the contraction against it commutes with covariant differentiation. This is the identity that
turns the contracted second Bianchi identity into `2 div Ric = d Scal`, and more generally
computes the derivative of any metric trace of a covariant two-tensor.

The proof works in the chart-local frame `Fᵢ` and its metric-dual frame
`Dᵢ = ∑ⱼ (G⁻¹)ᵢⱼ Fⱼ`, where `G` is the Gram matrix of `Fᵢ`. Near the point,
`tr_g b = ∑ᵢ b(Fᵢ, Dᵢ)`. Differentiating `⟪Dᵢ, Fⱼ⟫ = δᵢⱼ` with the metric shows that the terms of
`d (∑ᵢ b(Fᵢ, Dᵢ))` involving `∇Fᵢ` and `∇Dᵢ` cancel, which leaves `∑ᵢ (∇_v b)(Fᵢ, Dᵢ)`.

The same argument applies to a field `B` of bilinear maps on the tangent spaces with values in a
vector bundle `V` with a connection `∇`: if `B` is differentiable as a section of
`Hom(TM, Hom(TM, V))`, then `∇_v (tr_g B) = tr_g (∇_v B)` for the connection on
`Hom(TM, Hom(TM, V))` induced by the metric connection and `∇`.

## Main results

* `CovariantDerivative.IsMetricCompatible.mvfderiv_metricTrace`: the derivative of the metric
  trace of a field of bilinear forms is the metric trace of its covariant derivative.
* `CovariantDerivative.IsMetricCompatible.covariantDerivative_metricTrace`: the covariant
  derivative of the metric trace of a differentiable field of bundle-valued bilinear maps is the
  metric trace of its covariant derivative, and `CovariantDerivative.mdifferentiableAt_metricTrace`
  records that this metric trace is differentiable.
* `CovariantDerivative.IsMetricCompatible.mvfderiv_metricTrace_apply_eq_sum`: the same identity
  along a tangent vector, in an orthonormal basis.
* `CovariantDerivative.IsMetricCompatible.sum_apply_chartDualFrame_cancel`: for a metric
  connection, the derivatives of the chart-local frame and of its metric-dual frame cancel in a
  trace `∑ᵢ b(Fᵢ, Dᵢ)` of a vector-valued bilinear map `b`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 4:
  covariant derivatives of tensor fields commute with contractions, and the metric is parallel.
-/

public section

open Bundle FiberBundle Riemannian.Tensor
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The chart-local frame at `x` is differentiable at `x`. -/
private theorem mdifferentiableAt_chartLocalFrame (x : M) (i : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (chartLocalFrame (I := I) x i)) x := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  exact (contMDiffAt_chartLocalFrame (n := 1) x i).mdifferentiableAt one_ne_zero

/-- The metric-dual frame of the chart-local frame at `x` is differentiable at `x`. -/
private theorem mdifferentiableAt_chartDualFrame (x : M) (i : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (chartDualFrame (I := I) x i)) x := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  exact (contMDiffAt_chartDualFrame (n := 1) x (mem_baseSet_trivializationAt E _ x) i)
    |>.mdifferentiableAt one_ne_zero

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Near `x`, the metric trace of a field of bilinear maps `B` is `∑ᵢ B(Fᵢ, Dᵢ)`, where `Fᵢ` is the
chart-local frame at `x` and `Dᵢ` its metric-dual frame. -/
private theorem eventually_metricTrace_eq_sum_chartDualFrame {W : M → Type*}
    [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
    [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
    (B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] W y) (x : M) :
    ∀ᶠ y in 𝓝 x, LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y)) =
      ∑ i, B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y) := by
  have hU := (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x)
  filter_upwards [hU] with y hy
  rw [metricTrace_eq_sum_chartDualFrame x
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- For a metric connection, the terms of `∑ᵢ b(Fᵢ, Dᵢ)` involving `∇Fᵢ` and `∇Dᵢ` cancel at `x`,
where `Fᵢ` is the chart-local frame at `x` and `Dᵢ` its metric-dual frame:
`∑ᵢ b(Fᵢ, ∇_v Dᵢ) = -∑ᵢ b(∇_v Fᵢ, Dᵢ)`. The bilinear map `b` takes values in any real topological
vector space, such as `ℝ` or a fibre of a vector bundle. -/
theorem IsMetricCompatible.sum_apply_chartDualFrame_cancel {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (b : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] W) (v : TangentSpace I x) :
    ∑ i, b (chartLocalFrame (I := I) x i x) (cov (chartDualFrame (I := I) x i) x v) =
      -∑ i, b (cov (chartLocalFrame (I := I) x i) x v) (chartDualFrame (I := I) x i x) := by
  -- Differentiating `⟪Dᵢ, Fⱼ⟫ = δᵢⱼ` near `x` relates `∇Dᵢ` to `∇Fⱼ`.
  set F := chartLocalFrame (I := I) x with hFdef
  set D := chartDualFrame (I := I) x with hDdef
  have hxc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hU := (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x)
  have hdual (i j : Fin (Module.finrank ℝ E)) :
      inner ℝ (F j x) (cov (D i) x v) = -inner ℝ (D i x) (cov (F j) x v) := by
    have hconst : (fun y ↦ inner ℝ (D i y) (F j y)) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then (1 : ℝ) else 0 := by
      filter_upwards [hU] with y hy
      exact inner_chartDualFrame x
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hy) i j
    have h := hcov.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
      (mdifferentiableAt_chartDualFrame x i) (mdifferentiableAt_chartLocalFrame x j) hconst v
    rw [real_inner_comm]
    linarith
  have hexp (i : Fin (Module.finrank ℝ E)) : b (F i x) (cov (D i) x v) =
      -∑ j, inner ℝ (D i x) (cov (F j) x v) • b (F i x) (D j x) := by
    conv_lhs => rw [← (sum_inner_chartDualFrame_smul x hxc (cov (D i) x v)).2]
    simp only [← hFdef, ← hDdef, hdual, neg_smul, Finset.sum_neg_distrib, map_neg, map_sum,
      map_smul]
  simp only [hexp, Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  conv_rhs => rw [← (sum_inner_chartDualFrame_smul x hxc (cov (F j) x v)).1]
  simp only [← hFdef, ← hDdef, map_sum, map_smul, FunLike.coe_sum,
    FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply]

/-- **Covariant differentiation commutes with the metric trace.** For a connection compatible
with the metric and a field of bilinear forms `b` pairing sections differentiable at `x` to
functions differentiable at `x`, the derivative at `x` of the metric trace of `b` is the metric
trace of `∇b`, a covector-valued bilinear form on the tangent space at `x`. For fields of bilinear
maps with values in a vector bundle, see
`CovariantDerivative.IsMetricCompatible.covariantDerivative_metricTrace`. -/
theorem IsMetricCompatible.mvfderiv_metricTrace
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hb : ∀ ⦃σ τ : Π x : M, TangentSpace I x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x) :
    mvfderiv I
        (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (b y))) x =
      LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂ (cov.derivBilinearTensor b x)) := by
  have hF := mdifferentiableAt_chartLocalFrame (I := I) x
  have hD := mdifferentiableAt_chartDualFrame (I := I) x
  ext v
  -- Near `x`, the metric trace of `b` is `∑ᵢ b(Fᵢ, Dᵢ)`; differentiate it by the Leibniz rule.
  -- The terms involving `∇Fᵢ` and `∇Dᵢ` cancel.
  have hcancel := hcov.sum_apply_chartDualFrame_cancel x (b x) v
  have hterm (i : Fin (Module.finrank ℝ E)) := cov.derivBilinearTensor_apply hb (hF i) (hD i) v
  -- At `x`, the metric trace of `∇b` is `∑ᵢ (∇b)(Fᵢ, Dᵢ)`.
  have htr : (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (b y)))
      =ᶠ[𝓝 x] fun y ↦ ∑ i, b y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y) :=
    eventually_metricTrace_eq_sum_chartDualFrame b x
  rw [htr.mvfderiv_eq,
    TauCeti.mvfderiv_fun_sum fun i _ ↦ hb (hF i) (hD i), sum_apply,
    metricTrace_eq_sum_chartDualFrame x (mem_chart_source H x), sum_apply]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, hterm, Finset.sum_sub_distrib,
    hcancel]
  ring

/-- **Covariant differentiation commutes with the metric trace**, in an orthonormal basis: the
derivative of the metric trace of `b` along `v` is `∑ᵢ (∇_v b)(eᵢ, eᵢ)` for every orthonormal basis
`eᵢ` of the tangent space at `x`. -/
theorem IsMetricCompatible.mvfderiv_metricTrace_apply_eq_sum
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hb : ∀ ⦃σ τ : Π x : M, TangentSpace I x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I x))
    (v : TangentSpace I x) :
    mvfderiv I
        (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (b y))) x v =
      ∑ i, cov.derivBilinearTensor b x (e i) (e i) v := by
  rw [hcov.mvfderiv_metricTrace hb, LinearMap.BilinMap.metricTrace_eq_sum _ e, sum_apply]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-! ### Fields of bilinear maps with values in a vector bundle -/

section BundleValued

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] V y} {x : M}

/-- The metric trace of a field `B` of `V`-valued bilinear maps on the tangent spaces is a section
of `V` which is differentiable wherever `B` is differentiable as a section of the bundle
`Hom(TM, Hom(TM, V))` of bilinear maps. -/
theorem mdifferentiableAt_metricTrace
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x) :
    MDiffAt (T% fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y)))
      x := by
  have hsum := MDifferentiableAt.sum_section (s := Finset.univ)
    (t := fun i (y : M) ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))
    fun i _ ↦ (hB.clm_bundle_apply (mdifferentiableAt_chartLocalFrame x i)).clm_bundle_apply
      (mdifferentiableAt_chartDualFrame x i)
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.mono
    (eventually_metricTrace_eq_sum_chartDualFrame B x) fun y hy ↦ by simp only [hy])

/-- **Covariant differentiation commutes with the metric trace**, for a field `B` of bilinear maps
on the tangent spaces with values in a vector bundle `V`. If the connection `∇ᵀ` on the tangent
bundle is compatible with the metric and `B` is differentiable at `x` as a section of
`Hom(TM, Hom(TM, V))`, then for every connection `∇` on `V`, the covariant derivative at `x` of the
section `tr_g B` along `v` is the metric trace of `∇_v B`, the covariant derivative of `B` for the
connection induced by `∇ᵀ` and `∇`. -/
theorem IsMetricCompatible.covariantDerivative_metricTrace
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (covV : CovariantDerivative I F V)
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x)
    (v : TangentSpace I x) :
    covV (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y))) x v =
      LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂ (cov.hom (cov.hom covV) B x v)) := by
  have hF := mdifferentiableAt_chartLocalFrame (I := I) x
  have hD := mdifferentiableAt_chartDualFrame (I := I) x
  have hterm (i : Fin (Module.finrank ℝ E)) : MDiffAt
      (T% fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) x :=
    (hB.clm_bundle_apply (hF i)).clm_bundle_apply (hD i)
  have hsum : MDiffAt (T% (∑ i, fun y ↦
      B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))) x := by
    simpa [Finset.sum_apply] using MDifferentiableAt.sum_section (s := Finset.univ)
      (t := fun i (y : M) ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))
      fun i _ ↦ hterm i
  -- Near `x`, `tr_g B` is `∑ᵢ B(Fᵢ, Dᵢ)` in the chart frame `Fᵢ` and its metric-dual frame `Dᵢ`.
  have hloc : ∀ᶠ y in 𝓝 x,
      LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y)) =
        (∑ i, fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) y :=
    Filter.Eventually.mono (eventually_metricTrace_eq_sum_chartDualFrame B x) fun y hy ↦ by
      rw [hy, Finset.sum_apply]
  rw [covV.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (mdifferentiableAt_metricTrace hB)
      hsum Filter.univ_mem hloc,
    TauCeti.Manifold.covariantDerivative_sum covV.isCovariantDerivativeOnUniv (Set.mem_univ x)
      fun i _ ↦ hterm i, sum_apply, metricTrace_eq_sum_chartDualFrame x (mem_chart_source H x)]
  -- Differentiate each term by the Leibniz rule; the terms with `∇Fᵢ` and `∇Dᵢ` cancel.
  have hexp (i : Fin (Module.finrank ℝ E)) :
      covV (fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) x v =
        cov.hom (cov.hom covV) B x v (chartLocalFrame (I := I) x i x)
            (chartDualFrame (I := I) x i x) +
          B x (cov (chartLocalFrame (I := I) x i) x v) (chartDualFrame (I := I) x i x) +
          B x (chartLocalFrame (I := I) x i x) (cov (chartDualFrame (I := I) x i) x v) := by
    rw [hom_hom_apply cov cov covV hB (hF i) (hD i)]
    abel
  simp only [hexp, Finset.sum_add_distrib, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [hcov.sum_apply_chartDualFrame_cancel x (B x) v, add_neg_cancel_right]

end BundleValued

end CovariantDerivative
