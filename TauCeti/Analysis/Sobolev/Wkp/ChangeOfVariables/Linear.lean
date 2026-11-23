/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Linear changes of variables in `W^{2,p}`

Let `e : E ≃L[ℝ] E` be a continuous linear automorphism of a finite-dimensional real inner product
space `E`, and let `U = e⁻¹(W)` for open sets `U, W ⊆ E`. For `1 ≤ p < ∞`, precomposition with `e`
maps `W^{2,p}(W)` to `W^{2,p}(U)` with weak Hessian `D²(u ∘ e)(x) = e† ∘ D²u(e x) ∘ e` almost
everywhere on `U`, and preserves zero boundary values of the first-order part
(`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). When `e e† = A` and
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`, this transfers an `Lᵖ` Hessian bound by the Laplacian to solutions of
`tr (A D²u) = f` (`TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`).

General `Cᵏ` changes of variables in `W^{k,p}` are treated in
`TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables`.

## The argument

The first-order part of `u ∘ e` comes from `TauCeti.W1p.compL`, each gradient component
`⟪∇u, e c⟫` lies in `W^{1,p}(W)` (`TauCeti.Wkp.exists_w1p_value_eq_inner_gradient`), and
precomposing those components with `e` places `u ∘ e` in `W^{2,p}(U)` via
`TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`. Uniqueness of weak derivatives
identifies the entries `⟪D²(u ∘ e) f, c⟫ = ⟪D²u(e ·) (e f), e c⟫`. Zero boundary values are
preserved because `e` is a homeomorphism (`TauCeti.W1p.compL_mem_w1p0Submodule`).

## Main declarations

* `TauCeti.Wkp.exists_w1p_value_eq_inner_gradient`: each gradient component of `u ∈ W^{2,p}` is a
  `W^{1,p}` function whose weak gradient is given by the weak Hessian of `u`.
* `TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`: precomposition with a linear
  automorphism in `W^{2,p}`, and the chain rule for the weak Hessian.
* `TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`: transferring a Hessian
  estimate for the Laplacian to a constant-coefficient operator along a linear change of variables.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2–§5.4.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U W : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Precomposition with a linear automorphism in `W^{1,p}` -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem mapsTo_of_coe_eq_preimage (e : E ≃L[ℝ] E) (hUW : (U : Set E) = e ⁻¹' W) :
    MapsTo e U W := hUW ▸ mapsTo_preimage e W

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_fderiv_le (e : E ≃L[ℝ] E) (x : E) :
    ‖fderiv ℝ e x‖ ≤ ‖(e : E →L[ℝ] E)‖ := by
  rw [e.fderiv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem abs_det_pos (e : E ≃L[ℝ] E) : 0 < |(e : E →L[ℝ] E).det| :=
  abs_pos.2 (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem abs_det_le (e : E ≃L[ℝ] E) (x : E) :
    |(e : E →L[ℝ] E).det| ≤ |(fderiv ℝ e x).det| := by
  rw [e.fderiv]

/-- Precomposition with a continuous linear automorphism `e` of `E`, as an operator
`W^{1,p}(W) → W^{1,p}(U)` for `U = e⁻¹(W)`. -/
private def compCLE (hp : p ≠ ⊤) (e : E ≃L[ℝ] E) (hUW : (U : Set E) = e ⁻¹' W) :
    W1p mu W p →L[ℝ] W1p mu U p :=
  W1p.compL e hp e.differentiable.differentiableOn e.injective.injOn
    (mapsTo_of_coe_eq_preimage e hUW) (fun x _ => norm_fderiv_le e x) (abs_det_pos e)
    (fun x _ => abs_det_le e x)

private theorem value_compCLE_ae (hp : p ≠ ⊤) (e : E ≃L[ℝ] E) (hUW : (U : Set E) = e ⁻¹' W)
    (u : W1p mu W p) :
    W1p.value (compCLE hp e hUW u) =ᵐ[mu.restrict U] fun x => W1p.value u (e x) :=
  W1p.value_compL_ae e hp e.differentiable.differentiableOn e.injective.injOn
    (mapsTo_of_coe_eq_preimage e hUW) (fun x _ => norm_fderiv_le e x) (abs_det_pos e)
    (fun x _ => abs_det_le e x) u

private theorem gradient_compCLE_ae (hp : p ≠ ⊤) (e : E ≃L[ℝ] E) (hUW : (U : Set E) = e ⁻¹' W)
    (u : W1p mu W p) :
    W1p.gradient (compCLE hp e hUW u) =ᵐ[mu.restrict U]
      fun x => (e : E →L[ℝ] E).adjoint (W1p.gradient u (e x)) := by
  filter_upwards [W1p.gradient_compL_ae e hp e.differentiable.differentiableOn e.injective.injOn
    (mapsTo_of_coe_eq_preimage e hUW) (fun x _ => norm_fderiv_le e x) (abs_det_pos e)
    (fun x _ => abs_det_le e x) u] with x hx
  rw [compCLE, hx, e.fderiv]

private theorem compCLE_mem_w1p0Submodule (hp : p ≠ ⊤) (e : E ≃L[ℝ] E)
    (hUW : (U : Set E) = e ⁻¹' W) {u : W1p mu W p} (hu : u ∈ w1p0Submodule mu W p) :
    compCLE hp e hUW u ∈ w1p0Submodule mu U p :=
  W1p.compL_mem_w1p0Submodule e hp e.differentiable.differentiableOn e.injective.injOn
    (mapsTo_of_coe_eq_preimage e hUW) (fun x _ => norm_fderiv_le e x) (abs_det_pos e)
    (fun x _ => abs_det_le e x) e.toHomeomorph.isProperMap hUW hu

/-! ### Precomposition with a linear automorphism in `W^{2,p}` -/

/-- Almost-everywhere statements on `W` pull back along a linear automorphism `e` to
`U = e⁻¹(W)`. -/
private theorem quasiMeasurePreserving_restrict_of_coe_eq_preimage (e : E ≃L[ℝ] E)
    (hUW : (U : Set E) = e ⁻¹' W) :
    QuasiMeasurePreserving e (mu.restrict U) (mu.restrict W) :=
  (Measure.ContinuousLinearMap.quasiMeasurePreserving mu (e : E →L[ℝ] E)
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero).restrict (mapsTo_of_coe_eq_preimage e hUW)

/-- Each component `⟪∇u, c⟫` of the weak gradient of `u ∈ W^{2,p}(W)` is the value of a function
`d ∈ W^{1,p}(W)` whose weak gradient has the components `⟪D²u f, c⟫`. -/
theorem Wkp.exists_w1p_value_eq_inner_gradient (u : Wkp mu W p 2) (c : E) :
    ∃ d : W1p mu W p,
      W1p.value d =ᵐ[mu.restrict W]
        (fun y => ⟪Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y, c⟫_ℝ) ∧
      ∀ f : E, (fun y => ⟪W1p.gradient d y, f⟫_ℝ) =ᵐ[mu.restrict W]
        fun y => ⟪Wkp.iteratedGradient 1 u y f, c⟫_ℝ := by
  set g := Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 u c
  have h1 : HasWeakLineDerivOn mu W (Wkp.value 2 u) (fun y => ⟪g y, c⟫_ℝ) c := by
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder 1 u)).hasWeakLineDerivOn c
    rw [Wkp.value_firstOrder, Wkp.gradient_firstOrder_one] at h
    simpa only [innerSL_apply_apply] using h
  have hvd : W1p.value d =ᵐ[mu.restrict W] (fun y => ⟪g y, c⟫_ℝ) := by
    rw [← Wkp.value_one]
    exact hd.ae_eq h1
  refine ⟨d, hvd, fun f => ?_⟩
  have h2 : HasWeakLineDerivOn mu W (fun y => ⟪g y, c⟫_ℝ)
      (fun y => ⟪Wkp.iteratedGradient 1 u y f, c⟫_ℝ) f := by
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm c] using
      ((Wkp.hasWeakFDerivOn_iteratedGradient 0 u).clm_comp (innerSL ℝ c)).hasWeakLineDerivOn f
  have h3 : HasWeakLineDerivOn mu W (fun y => ⟪g y, c⟫_ℝ)
      (fun y => ⟪W1p.gradient d y, f⟫_ℝ) f := by
    simpa only [innerSL_apply_apply] using
      ((W1p.hasWeakFDerivOn d).hasWeakLineDerivOn f).congr_ae hvd
  exact h3.ae_eq h2

/-- If the weak gradient of `d ∈ W^{1,p}(W)` has components `⟪D²u f, e c⟫`, then the weak gradient
of `d ∘ e` has components `⟪(e† ∘ D²u(e ·) ∘ e) f, c⟫`. -/
private theorem inner_gradient_compCLE_ae (hp : p ≠ ⊤) (e : E ≃L[ℝ] E)
    (hUW : (U : Set E) = e ⁻¹' W) (u : Wkp mu W p 2) (c : E) (d : W1p mu W p)
    (hd : ∀ f : E, (fun y => ⟪W1p.gradient d y, f⟫_ℝ) =ᵐ[mu.restrict W]
      fun y => ⟪Wkp.iteratedGradient 1 u y f, e c⟫_ℝ) (f : E) :
    (fun x => ⟪W1p.gradient (compCLE hp e hUW d) x, f⟫_ℝ) =ᵐ[mu.restrict U]
      fun x => ⟪((e : E →L[ℝ] E).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L
        (e : E →L[ℝ] E)) f, c⟫_ℝ := by
  filter_upwards [gradient_compCLE_ae hp e hUW d,
    quasiMeasurePreserving_restrict_of_coe_eq_preimage e hUW |>.ae (hd (e f))] with x h1 h2
  rw [h1, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, h2]

/-- **Linear changes of variables in `W^{2,p}`.** Let `e` be a continuous linear automorphism of
`E` and `U = e⁻¹(W)`. For `1 ≤ p < ∞` and `u ∈ W^{2,p}(W)`, the composition `u ∘ e` lies in
`W^{2,p}(U)`, with weak Hessian `e† ∘ D²u(e x) ∘ e`, where `e†` is the adjoint of `e` and `D²u`
is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. If the first-order part of `u` lies in
`W^{1,p}_0(W)`, then that of `u ∘ e` lies in `W^{1,p}_0(U)`. -/
theorem Wkp.exists_value_ae_eq_comp_continuousLinearEquiv (hp : p ≠ ⊤) (e : E ≃L[ℝ] E)
    (hUW : (U : Set E) = e ⁻¹' W) (u : Wkp mu W p 2) :
    ∃ w : Wkp mu U p 2,
      Wkp.value 2 w =ᵐ[mu.restrict U] (fun x => Wkp.value 2 u (e x)) ∧
      Wkp.iteratedGradient 1 w =ᵐ[mu.restrict U] (fun x =>
        (e : E →L[ℝ] E).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L (e : E →L[ℝ] E)) ∧
      (Wkp.firstOrder 1 u ∈ w1p0Submodule mu W p →
        Wkp.firstOrder 1 w ∈ w1p0Submodule mu U p) := by
  set T := compCLE (mu := mu) hp e hUW
  have hqmp := quasiMeasurePreserving_restrict_of_coe_eq_preimage (mu := mu) e hUW
  set u₁ := Wkp.firstOrder 1 u
  have hgrad : W1p.gradient u₁ = Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) :=
    Wkp.gradient_firstOrder_one u
  have hval := Wkp.value_firstOrder 1 u
  -- Each component `⟪∇u, c⟫` is the value of some `d c ∈ W^{1,p}(W)`, whose weak gradient has
  -- the components `⟪D²u f, c⟫`.
  choose d hdv hdg using Wkp.exists_w1p_value_eq_inner_gradient u
  set w₁ := T u₁
  -- The component `⟪∇(u ∘ e), c⟫ = ⟪∇u, e c⟫ ∘ e` is the value of `d (e c) ∘ e`.
  have hw₁ (c : E) : (fun x => ⟪W1p.gradient w₁ x, c⟫_ℝ) =ᵐ[mu.restrict U]
      W1p.value (T (d (e c))) := by
    filter_upwards [gradient_compCLE_ae hp e hUW u₁, value_compCLE_ae hp e hUW (d (e c)),
      hqmp.ae (hdv (e c))] with x h1 h2 h3
    rw [h1, ContinuousLinearMap.adjoint_inner_left, h2, h3, hgrad, ContinuousLinearEquiv.coe_coe]
  have hD (c f : E) : HasWeakLineDerivOn mu U (fun x => ⟪W1p.gradient w₁ x, c⟫_ℝ)
      (fun x => ⟪W1p.gradient (T (d (e c))) x, f⟫_ℝ) f := by
    simpa only [innerSL_apply_apply] using
      ((W1p.hasWeakFDerivOn (T (d (e c)))).hasWeakLineDerivOn f).congr_ae (hw₁ c).symm
  have hDe (c f : E) := inner_gradient_compCLE_ae hp e hUW u c (d (e c)) (hdg (e c)) f
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨w, hw⟩ := W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn w₁ b fun i j =>
    ⟨(innerSL ℝ (b i)).compLp (W1p.gradient (T (d (e (b j))))),
      (hD (b j) (b i)).congr_ae_deriv (by
        filter_upwards [(innerSL ℝ (b i)).coeFn_compLp (W1p.gradient (T (d (e (b j)))))]
          with x hx
        rw [hx, innerSL_apply_apply, real_inner_comm])⟩
  refine ⟨w, ?_, ?_, fun hu => ?_⟩
  · rw [Wkp.value_succ, hw]
    have h1 := Wkp.value_one (mu := mu) (Omega := U) (p := p) w₁
    rw [h1]
    filter_upwards [value_compCLE_ae hp e hUW u₁] with x hx
    rw [hx, hval]
  · -- The entries `⟪D²w f, c⟫` are the weak derivatives in direction `f` of `⟪∇w, c⟫`.
    have hentry (c f : E) : (fun x => ⟪Wkp.iteratedGradient 1 w x f, c⟫_ℝ) =ᵐ[mu.restrict U]
        fun x => ⟪((e : E →L[ℝ] E).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L
          (e : E →L[ℝ] E)) f, c⟫_ℝ := by
      have h := ((Wkp.hasWeakFDerivOn_iteratedGradient 0 w).clm_comp
        (innerSL ℝ c)).hasWeakLineDerivOn f
      rw [hw, Wkp.iteratedGradient_zero (mu := mu) (Omega := U) (p := p) w₁] at h
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm _ c] at h
      exact (h.ae_eq (hD c f)).trans (hDe c f)
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry (b j) (b i)] with x hx
    exact ContinuousLinearMap.coe_injective (b.toBasis.ext fun i =>
      InnerProductSpace.ext_inner_right_basis b.toBasis fun j => by simpa using hx i j)
  · rw [Wkp.firstOrder_one, hw]
    exact compCLE_mem_w1p0Submodule hp e hUW hu

/-! ### Transferring Hessian estimates along a linear change of variables -/

/-- **Transferring the estimate along a linear change of variables.** Let `e e† = A` with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`, let `U = e⁻¹(W)`, and let `v ∈ W^{2,p}(U)` have weak Hessian
`e† ∘ D²u(e ·) ∘ e`. If `u` solves `tr (A D²u) = f` on `W` and the Hessian of `v` is bounded by
`C` times the norm of its trace, then `‖D²u‖ ≤ (C / λ) ‖f‖`. -/
theorem Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp {A : E →L[ℝ] E} (e : E ≃L[ℝ] E)
    (hee : (e : E →L[ℝ] E) ∘L (e : E →L[ℝ] E).adjoint = A) {lam : ℝ}
    (he : ∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) (hUW : (U : Set E) = e ⁻¹' W)
    {u : Wkp mu W p 2} {v : Wkp mu U p 2}
    (hD : Wkp.iteratedGradient 1 v =ᵐ[mu.restrict U] fun x =>
      (e : E →L[ℝ] E).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L (e : E →L[ℝ] E))
    {f : Lp ℝ p (mu.restrict W)}
    (hf : ∀ᵐ x ∂(mu.restrict W), traceCLM ℝ E (A ∘L Wkp.iteratedGradient 1 u x) = f x)
    {C : ℝ} (hv : ∀ g : Lp ℝ p (mu.restrict U),
      (traceCLM ℝ E).compLpL p _ (Wkp.iteratedGradient 1 v) = g →
        ‖Wkp.iteratedGradient 1 v‖ ≤ C * ‖g‖) :
    ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  -- If `lam ≤ 0` then `he` forces `E` to be trivial and both norms vanish.
  by_cases hlam : 0 < lam
  swap
  · have hE : Subsingleton E := subsingleton_of_forall_eq 0 fun x => by
      have h := he (e x)
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hlam), inv_zero, zero_mul] at h
      simpa using h
    have hu : Wkp.iteratedGradient 1 u = 0 := Lp.eq_zero_iff_ae_eq_zero.2
      (Filter.Eventually.of_forall fun x => Subsingleton.elim _ _)
    have hf0 : f = 0 := Lp.eq_zero_iff_ae_eq_zero.2 (by
      filter_upwards [hf] with x hx
      rw [← hx, Subsingleton.elim (A ∘L Wkp.iteratedGradient 1 u x) 0, map_zero, Pi.zero_apply])
    simp [hu, hf0]
  have habs := abs_det_pos e
  have hmap : (mu.restrict U).map e ≤
      (ENNReal.ofReal |(e : E →L[ℝ] E).det|)⁻¹ • mu.restrict W :=
    map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen
      e.differentiable.differentiableOn e.injective.injOn (mapsTo_of_coe_eq_preimage e hUW) habs
      fun x _ => abs_det_le e x
  have hC' : (ENNReal.ofReal |(e : E →L[ℝ] E).det|)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 habs).ne'
  have hqmp := quasiMeasurePreserving_restrict_of_coe_eq_preimage (mu := mu) e hUW
  -- `v` solves Poisson's equation with forcing term `f ∘ e`
  set f' := Lp.compOfMapLeSmul ℝ e.continuous.aemeasurable hC' hmap f
  have hf'e := Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) e.continuous.aemeasurable hC' hmap f
  have hv' := hv f' <| Lp.ext <| by
    filter_upwards [(traceCLM ℝ E).coeFn_compLpL (Wkp.iteratedGradient 1 v), hD, hf'e,
      hqmp.ae hf] with y h1 h2 h3 h4
    -- `tr (e† M e) = tr (M e e†) = tr (M A) = tr (A M)`
    rw [h1, h2, h3, Function.comp_apply, ← h4, ContinuousLinearMap.traceCLM_comp_comm,
      ContinuousLinearMap.comp_assoc, hee, ContinuousLinearMap.traceCLM_comp_comm]
  -- Both sides change by the same Jacobian factor `δ` under the change of variables.
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal :=
    ⟨_, rfl⟩
  have hf' : eLpNorm f' p (mu.restrict U) = δ * eLpNorm f p (mu.restrict W) := by
    rw [eLpNorm_congr_ae hf'e, hUW, hδ]
    exact Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage mu _ e p
  have hDu : δ * eLpNorm (Wkp.iteratedGradient 1 u) p (mu.restrict W) ≤
      ENNReal.ofReal lam⁻¹ * eLpNorm (Wkp.iteratedGradient 1 v) p (mu.restrict U) := by
    have hcomp := Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage mu
      (⇑(Wkp.iteratedGradient 1 u)) e p (s := (W : Set E))
    rw [← hδ, ← hUW] at hcomp
    rw [← hcomp]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((Lp.aestronglyMeasurable _).comp_quasiMeasurePreserving hqmp) ?_ p
    filter_upwards [hD] with y hy
    rw [hy, Function.comp_apply]
    exact e.norm_le_inv_mul_norm_adjoint_comp_comp he (Wkp.iteratedGradient 1 u (e y))
  -- Back to real norms, cancelling `δ`.
  have hδr : 0 < δ.toReal := by
    rw [hδ, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]
    exact Real.rpow_pos_of_pos (abs_pos.2 (inv_ne_zero
      (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero)) _
  have h1 := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) hDu
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hlam.le),
    ← Lp.norm_def, ← Lp.norm_def] at h1
  have h2 : ‖f'‖ = δ.toReal * ‖f‖ := by
    rw [Lp.norm_def, Lp.norm_def, hf', ENNReal.toReal_mul]
  refine le_of_mul_le_mul_left ?_ hδr
  calc δ.toReal * ‖Wkp.iteratedGradient 1 u‖ ≤ lam⁻¹ * ‖Wkp.iteratedGradient 1 v‖ := h1
    _ ≤ lam⁻¹ * (C * (δ.toReal * ‖f‖)) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left hv' (inv_nonneg.2 hlam.le)
    _ = δ.toReal * (C / lam * ‖f‖) := by ring

end TauCeti
