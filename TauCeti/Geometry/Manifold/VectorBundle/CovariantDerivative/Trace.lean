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
  metric trace of its covariant derivative; `MDifferentiableAt.metricTrace` and
  `ContMDiffAt.metricTrace` record that this metric trace is differentiable, respectively `C^n`.
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

/-- For a metric connection, the terms of `∑ᵢ b(Fᵢ, Dᵢ)` involving `∇Fᵢ` and `∇Dᵢ` cancel at `x`,
where `Fᵢ` is the chart-local frame at `x` and `Dᵢ` its metric-dual frame:
`∑ᵢ b(Fᵢ, ∇_v Dᵢ) = -∑ᵢ b(∇_v Fᵢ, Dᵢ)`. The bilinear map `b` takes values in any real vector
space, such as `ℝ` or a fibre of a vector bundle. -/
theorem IsMetricCompatible.sum_apply_chartDualFrame_cancel {W : Type*} [AddCommGroup W] [Module ℝ W]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (x : M) (b : LinearMap.BilinMap ℝ (TangentSpace I x) W) (v : TangentSpace I x) :
    ∑ i, b (chartLocalFrame (I := I) x i x) (cov (chartDualFrame (I := I) x i) x v) =
      -∑ i, b (cov (chartLocalFrame (I := I) x i) x v) (chartDualFrame (I := I) x i x) := by
  -- Differentiating `⟪Dᵢ, Fⱼ⟫ = δᵢⱼ` near `x` relates `∇Dᵢ` to `∇Fⱼ`.
  set F := chartLocalFrame (I := I) x with hFdef
  set D := chartDualFrame (I := I) x with hDdef
  have hxc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hU := (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hxb
  have hdual (i j : Fin (Module.finrank ℝ E)) :
      inner ℝ (F j x) (cov (D i) x v) = -inner ℝ (D i x) (cov (F j) x v) := by
    have hconst : (fun y ↦ inner ℝ (D i y) (F j y)) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then (1 : ℝ) else 0 := by
      filter_upwards [hU] with y hy
      exact inner_chartDualFrame x
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hy) i j
    have h := hcov.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
      (mdifferentiableAt_chartDualFrame x hxb i) (mdifferentiableAt_chartLocalFrame x hxb j)
      hconst v
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
  simp only [← hFdef, ← hDdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Near `x`, the metric trace of a field of continuous bilinear maps equals the finite sum of
sections obtained by pairing it with the chart-local frame and its metric-dual frame. -/
private theorem eventually_metricTrace_toLinearMap₁₂_eq_sum_chartDualFrame
    {N : M → Type*} [∀ y, AddCommGroup (N y)] [∀ y, Module ℝ (N y)]
    [∀ y, TopologicalSpace (N y)] [∀ y, IsTopologicalAddGroup (N y)]
    [∀ y, ContinuousSMul ℝ (N y)]
    (B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] N y) (x : M) :
    ∀ᶠ y in 𝓝 x,
      LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y)) =
        (∑ i, fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) y :=
  (eventually_metricTrace_eq_sum_chartDualFrame x (mem_chart_source H x)
    (fun y ↦ ContinuousLinearMap.toLinearMap₁₂ (B y))).mono fun y hy ↦ by
      simp only [hy, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, Finset.sum_apply]

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
  have hxb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hF := mdifferentiableAt_chartLocalFrame (I := I) x hxb
  have hD := mdifferentiableAt_chartDualFrame (I := I) x hxb
  ext v
  -- Near `x`, the metric trace of `b` is `∑ᵢ b(Fᵢ, Dᵢ)`; differentiate it by the Leibniz rule.
  -- The terms involving `∇Fᵢ` and `∇Dᵢ` cancel.
  have hcancel :=
    hcov.sum_apply_chartDualFrame_cancel x (ContinuousLinearMap.toLinearMap₁₂ (b x)) v
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at hcancel
  have hterm (i : Fin (Module.finrank ℝ E)) := cov.derivBilinearTensor_apply hb (hF i) (hD i) v
  -- At `x`, the metric trace of `∇b` is `∑ᵢ (∇b)(Fᵢ, Dᵢ)`.
  have htr : (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (b y)))
      =ᶠ[𝓝 x] fun y ↦ ∑ i, b y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y) :=
    (eventually_metricTrace_toLinearMap₁₂_eq_sum_chartDualFrame b x).mono fun y hy ↦ by
      simpa only [Finset.sum_apply] using hy
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

/-- Pairing a differentiable field `B` of `V`-valued bilinear maps with the chart-local frame and
its metric-dual frame gives a differentiable section of `V`. -/
private theorem mdifferentiableAt_apply_chartDualFrame
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x)
    (i : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) x :=
  (hB.clm_bundle_apply
    (mdifferentiableAt_chartLocalFrame x (mem_baseSet_trivializationAt E _ x) i)).clm_bundle_apply
    (mdifferentiableAt_chartDualFrame x (mem_baseSet_trivializationAt E _ x) i)

/-- The finite sum `∑ᵢ B(Fᵢ, Dᵢ)` of a differentiable field `B` paired with the chart frame and
its metric-dual frame is a differentiable section of `V`. -/
private theorem mdifferentiableAt_sum_apply_chartDualFrame
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x) :
    MDiffAt (T% (∑ i, fun y ↦
      B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))) x := by
  simpa [Finset.sum_apply] using MDifferentiableAt.sum_section (s := Finset.univ)
    (t := fun i (y : M) ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))
    fun i _ ↦ mdifferentiableAt_apply_chartDualFrame hB i

/-- The metric trace of a field `B` of `V`-valued bilinear maps on the tangent spaces is a section
of `V` which is differentiable wherever `B` is differentiable as a section of the bundle
`Hom(TM, Hom(TM, V))` of bilinear maps. -/
theorem _root_.MDifferentiableAt.metricTrace
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x) :
    MDiffAt (T% fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y)))
      x :=
  (mdifferentiableAt_sum_apply_chartDualFrame hB).congr_of_eventuallyEq
    ((eventually_metricTrace_toLinearMap₁₂_eq_sum_chartDualFrame B x).mono
      fun y hy ↦ congrArg (TotalSpace.mk' F y) hy)

omit [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The metric trace of a field `B` of `V`-valued bilinear maps on the tangent spaces, for a `C^n`
metric, is a section of `V` which is `C^n` wherever `B` is `C^n` as a section of the bundle
`Hom(TM, Hom(TM, V))` of bilinear maps. -/
theorem _root_.ContMDiffAt.metricTrace {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hB : CMDiffAt n (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z) y (B y)) x) :
    CMDiffAt n (T% fun y ↦
      LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (B y))) x := by
  refine (ContMDiffAt.sum_section (s := Finset.univ)
    (t := fun i (y : M) ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y))
    fun i _ ↦ (hB.clm_bundle_apply (contMDiffAt_chartLocalFrame x i)).clm_bundle_apply
      (contMDiffAt_chartDualFrame x (mem_baseSet_trivializationAt E _ x)
        i)).congr_of_eventuallyEq ?_
  refine (eventually_metricTrace_eq_sum_chartDualFrame x (mem_chart_source H x)
    (fun y ↦ ContinuousLinearMap.toLinearMap₁₂ (B y))).mono fun y hy ↦ ?_
  simp only [hy, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

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
  have hxb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hF := mdifferentiableAt_chartLocalFrame (I := I) x hxb
  have hD := mdifferentiableAt_chartDualFrame (I := I) x hxb
  -- Near `x`, `tr_g B` is `∑ᵢ B(Fᵢ, Dᵢ)` in the chart frame `Fᵢ` and its metric-dual frame `Dᵢ`.
  rw [covV.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hB.metricTrace
      (mdifferentiableAt_sum_apply_chartDualFrame hB) Filter.univ_mem
      (eventually_metricTrace_toLinearMap₁₂_eq_sum_chartDualFrame B x),
    covV.isCovariantDerivativeOnUniv.sum fun i _ ↦ mdifferentiableAt_apply_chartDualFrame hB i,
    sum_apply, metricTrace_eq_sum_chartDualFrame x (mem_chart_source H x)]
  -- Differentiate each term by the Leibniz rule; the terms with `∇Fᵢ` and `∇Dᵢ` cancel.
  have hexp (i : Fin (Module.finrank ℝ E)) :
      covV (fun y ↦ B y (chartLocalFrame (I := I) x i y) (chartDualFrame (I := I) x i y)) x v =
        cov.hom (cov.hom covV) B x v (chartLocalFrame (I := I) x i x)
            (chartDualFrame (I := I) x i x) +
          B x (cov (chartLocalFrame (I := I) x i) x v) (chartDualFrame (I := I) x i x) +
          B x (chartLocalFrame (I := I) x i x) (cov (chartDualFrame (I := I) x i) x v) := by
    rw [hom_hom_apply cov cov covV hB (hF i) (hD i)]
    abel
  have hcancel :=
    hcov.sum_apply_chartDualFrame_cancel x (ContinuousLinearMap.toLinearMap₁₂ (B x)) v
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at hcancel
  simp only [hexp, Finset.sum_add_distrib, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [hcancel, add_neg_cancel_right]

end BundleValued

end CovariantDerivative
