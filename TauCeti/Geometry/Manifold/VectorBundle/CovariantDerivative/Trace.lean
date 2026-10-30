/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

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

## Main results

* `CovariantDerivative.IsMetricCompatible.mvfderiv_bilinFormTrace`: the derivative of the metric
  trace of a field of bilinear forms is the trace of its covariant derivative.

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

section DualFrame

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The frame metric-dual to the chart-local frame at `α`: `Dᵢ = ∑ⱼ (G⁻¹)ᵢⱼ Fⱼ`, where `G` is the
Gram matrix of the chart-local frame `Fᵢ`. -/
private def chartDualFrame (α : M) (i : Fin (Module.finrank ℝ E)) :
    Π y : M, TangentSpace I y :=
  fun y ↦ ∑ j, chartInvGramMatrix (I := I) α y i j • chartLocalFrame (I := I) α j y

/-- On the chart domain, the dual frame pairs with the chart-local frame to the identity
matrix. -/
private theorem inner_chartDualFrame (α : M) {y : M} (hy : y ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    inner ℝ (chartDualFrame (I := I) α i y) (chartLocalFrame (I := I) α j y) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (chartInvGramMatrix_mul_chartGramMatrix (I := I) α hy) i) j
  simp only [Matrix.mul_apply, chartGramMatrix_apply, Matrix.one_apply] at h
  simp only [chartDualFrame, sum_inner, real_inner_smul_left, h]

/-- On the chart domain, the metric trace of a bilinear form is `∑ᵢ B(Fᵢ, Dᵢ)`. -/
private theorem bilinFormTrace_eq_sum_chartDualFrame (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source) (B : LinearMap.BilinForm ℝ (TangentSpace I y)) :
    TauCeti.bilinFormTrace B =
      ∑ i, B (chartLocalFrame (I := I) α i y) (chartDualFrame (I := I) α i y) := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hy'
  have hb : ⇑b = fun i ↦ chartLocalFrame (I := I) α i y :=
    funext fun i ↦ (chartLocalFrame_apply_of_mem_chart_source (I := I) α hy i).symm
  have hgram : Matrix.gram ℝ b = chartGramMatrix (I := I) α y := by
    ext i j
    rw [Matrix.gram_apply, chartGramMatrix_apply, hb]
  have hinv : (Matrix.gram ℝ b)⁻¹ = chartInvGramMatrix (I := I) α y :=
    Matrix.inv_eq_left_inv (hgram ▸ chartInvGramMatrix_mul_chartGramMatrix (I := I) α hy)
  rw [TauCeti.bilinFormTrace_eq_sum_inv_gram _ b, hinv, hb]
  simp only [chartDualFrame, map_sum, map_smul, smul_eq_mul]

/-- On the chart domain, every tangent vector expands in the chart-local frame with the dual
frame giving its coefficients, and in the dual frame with the chart-local frame giving its
coefficients. -/
private theorem sum_inner_chartDualFrame_smul (α : M) {y : M} (hy : y ∈ (chartAt H α).source)
    (w : TangentSpace I y) :
    ∑ j, inner ℝ (chartDualFrame (I := I) α j y) w • chartLocalFrame (I := I) α j y = w ∧
      ∑ j, inner ℝ (chartLocalFrame (I := I) α j y) w • chartDualFrame (I := I) α j y = w := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hy'
  have hb (i : Fin (Module.finrank ℝ E)) : b i = chartLocalFrame (I := I) α i y :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) α hy i).symm
  have hdual (i j : Fin (Module.finrank ℝ E)) :
      inner ℝ (chartDualFrame (I := I) α i y) (b j) = if i = j then 1 else 0 := by
    rw [hb]
    exact inner_chartDualFrame α hy i j
  constructor
  · -- Both sides have the same coefficients in the basis `b`.
    conv_rhs => rw [← b.sum_repr w]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hb]
    congr 1
    conv_lhs => rw [← b.sum_repr w]
    simp only [inner_sum, real_inner_smul_right, hdual, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · -- Both sides have the same inner products with the basis `b`.
    refine InnerProductSpace.ext_inner_right_basis b fun k ↦ ?_
    simp only [hb, sum_inner, real_inner_smul_left, inner_chartDualFrame α hy, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, real_inner_comm w]

end DualFrame

variable [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The dual frame is differentiable at every point of the chart domain. -/
private theorem mdifferentiableAt_chartDualFrame (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) (i : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (chartDualFrame (I := I) α i)) y := by
  have hU := (trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  refine MDifferentiableAt.sum_section fun j _ ↦ MDifferentiableAt.smul_section ?_ ?_
  · exact ((contMDiffOn_chartInvGramMatrix_entry (n := 1) α i j).contMDiffAt hU).mdifferentiableAt
      one_ne_zero
  · exact ((contMDiffOn_chartLocalFrame (n := 1) α j).contMDiffAt hU).mdifferentiableAt
      one_ne_zero

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- **Covariant differentiation commutes with the metric trace.** For a connection compatible
with the metric and a field of bilinear forms `b` pairing sections differentiable at `x` to
functions differentiable at `x`, the derivative of the metric trace of `b` along `v` is the
metric trace of `∇_v b`, computed in any orthonormal basis of the tangent space at `x`. -/
theorem IsMetricCompatible.mvfderiv_bilinFormTrace
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hb : ∀ ⦃σ τ : Π x : M, TangentSpace I x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I x))
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ TauCeti.bilinFormTrace (ContinuousLinearMap.toLinearMap₁₂ (b y))) x v =
      ∑ i, cov.derivBilinearTensor b x (e i) (e i) v := by
  set F := chartLocalFrame (I := I) x with hFdef
  set D := chartDualFrame (I := I) x with hDdef
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hxc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hU := (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hF (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (F i)) x :=
    ((contMDiffOn_chartLocalFrame (n := 1) x i).contMDiffAt hU).mdifferentiableAt one_ne_zero
  have hD (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (D i)) x :=
    mdifferentiableAt_chartDualFrame x hx i
  -- Near `x`, the metric trace of `b` is `∑ᵢ b(Fᵢ, Dᵢ)`.
  have htr : (fun y ↦ TauCeti.bilinFormTrace (ContinuousLinearMap.toLinearMap₁₂ (b y))) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, b y (F i y) (D i y) := by
    filter_upwards [hU] with y hy
    rw [bilinFormTrace_eq_sum_chartDualFrame x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, ← hFdef, ← hDdef]
  have hsum : mvfderiv I (fun y ↦ ∑ i, b y (F i y) (D i y)) x v =
      ∑ i, mvfderiv I (fun y ↦ b y (F i y) (D i y)) x v := by
    have hfun : (fun y ↦ ∑ i, b y (F i y) (D i y)) = ∑ i, fun y ↦ b y (F i y) (D i y) := by
      ext y; simp
    have hH : HasMFDerivAt I 𝓘(ℝ) (∑ i, fun y ↦ b y (F i y) (D i y)) x
        (∑ i, mvfderiv I (fun y ↦ b y (F i y) (D i y)) x) :=
      HasMFDerivAt.sum fun i _ ↦ (hb (hF i) (hD i)).hasMFDerivAt
    rw [hfun, mvfderiv_apply_eq_mfderiv_apply, hH.mfderiv]
    -- The tangent spaces of `ℝ` in which `mfderiv` takes values are `ℝ` itself.
    exact _root_.sum_apply ..
  -- Differentiating `⟪Dᵢ, Fⱼ⟫ = δᵢⱼ` near `x` relates `∇Dᵢ` to `∇Fⱼ`.
  have hdual (i j : Fin (Module.finrank ℝ E)) :
      inner ℝ (F j x) (cov (D i) x v) = -inner ℝ (D i x) (cov (F j) x v) := by
    have hconst : (fun y ↦ inner ℝ (D i y) (F j y)) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then (1 : ℝ) else 0 := by
      filter_upwards [hU] with y hy
      exact inner_chartDualFrame x
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hy) i j
    have h := hcov.mvfderiv_inner_eq (extend E v) (hD i) (hF j)
    rw [hconst.mvfderiv_eq, mvfderiv_const] at h
    simp only [extend_apply_self, zero_apply] at h
    rw [real_inner_comm]
    linarith
  -- The terms involving `∇Fᵢ` and `∇Dᵢ` cancel.
  have hcancel : ∑ i, b x (F i x) (cov (D i) x v) = -∑ i, b x (cov (F i) x v) (D i x) := by
    have hexp (i : Fin (Module.finrank ℝ E)) : b x (F i x) (cov (D i) x v) =
        -∑ j, inner ℝ (D i x) (cov (F j) x v) * b x (F i x) (D j x) := by
      conv_lhs => rw [← (sum_inner_chartDualFrame_smul x hxc (cov (D i) x v)).2]
      simp only [← hFdef, ← hDdef, map_sum, map_smul, smul_eq_mul, hdual, neg_mul,
        Finset.sum_neg_distrib]
    simp only [hexp, Finset.sum_neg_distrib, neg_inj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    conv_rhs => rw [← (sum_inner_chartDualFrame_smul x hxc (cov (F j) x v)).1]
    simp only [← hFdef, ← hDdef, map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- At `x`, both sides are metric traces of `∇_v b`.
  let β : LinearMap.BilinForm ℝ (TangentSpace I x) :=
    LinearMap.mk₂ ℝ (fun u w ↦ cov.derivBilinearTensor b x u w v) (by simp) (by simp)
      (by simp) (by simp)
  have hβ := bilinFormTrace_eq_sum_chartDualFrame x hxc β
  rw [TauCeti.bilinFormTrace_eq_sum β e] at hβ
  simp only [β, LinearMap.mk₂_apply, ← hFdef, ← hDdef] at hβ
  have hterm (i : Fin (Module.finrank ℝ E)) := cov.derivBilinearTensor_apply hb (hF i) (hD i) v
  rw [htr.mvfderiv_eq, hsum, hβ]
  simp only [hterm, Finset.sum_sub_distrib, hcancel]
  ring

end CovariantDerivative
