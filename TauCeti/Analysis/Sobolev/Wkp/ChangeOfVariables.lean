/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Topology.Algebra.Module.Trace

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Linear changes of variables in `W^{2,p}`

Let `e` be a continuous linear automorphism of a finite-dimensional real inner product space `E`,
and let `U = e⁻¹(W)` for open sets `U, W ⊆ E`. For `1 ≤ p < ∞`, this file proves that
precomposition with `e` maps `W^{2,p}(W)` to `W^{2,p}(U)`, with the chain rule for the weak Hessian

`D²(u ∘ e)(x) = e† ∘ D²u(e x) ∘ e`

almost everywhere on `U`, where `e†` is the adjoint of `e`, and that it preserves zero boundary
values of the first-order part (`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`).

Linear changes of variables reduce constant-coefficient equations to the Laplacian: if
`e e† = A`, then `tr (D²(u ∘ e)) = tr (A D²u) ∘ e`. Hence an `Lᵖ` bound on the Hessian of `u ∘ e`
by its trace transfers to the bound `‖D²u‖ ≤ (C / λ) ‖f‖` for solutions of `tr (A D²u) = f`,
when `‖e⁻¹ x‖ ≤ ‖x‖ / √λ` (`TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`).
When `e⁻¹` maps a half-space onto a half-space, this transfers estimates for strong solutions of
Poisson's equation vanishing on the boundary hyperplane to constant-coefficient equations.

## The argument

The first-order part of `u ∘ e` is given by the change of variables in `W^{1,p}`
(`TauCeti.W1p.compL`), with weak gradient `e† (∇u ∘ e)`, so its component along a direction `c`
is `⟪∇u, e c⟫ ∘ e`. The component `⟪∇u, e c⟫` is itself a function in `W^{1,p}(W)` whose weak
gradient has components `⟪D²u f, e c⟫`, so its composition with `e` lies in `W^{1,p}(U)`. Thus
every component of the weak gradient of `u ∘ e` has `Lᵖ` weak derivatives, which places `u ∘ e`
in `W^{2,p}(U)` (`TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`), and uniqueness
of weak derivatives identifies the entries `⟪D²(u ∘ e) f, c⟫ = ⟪D²u(e ·) (e f), e c⟫`. Zero
boundary values are preserved because `e` is a homeomorphism
(`TauCeti.W1p.compL_mem_w1p0Submodule`).

## Main declarations

* `TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`: precomposition with a linear
  automorphism in `W^{2,p}`, and the chain rule for the weak Hessian.
* `TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`: transferring a Hessian
  estimate for the Laplacian to a constant-coefficient operator along a linear change of variables.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2–§5.4 (weak derivatives and changes
  of variables in Sobolev spaces).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6 (changes of variables in `W^{1,p}`).
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

private theorem value_firstOrder_one (u : Wkp mu W p 2) :
    W1p.value (Wkp.firstOrder 1 u) = Wkp.value 2 u := by
  rw [Wkp.value_succ, Wkp.value_one, (Wkp.firstOrder_succ 0 u).trans (Wkp.firstOrder_zero _)]

private theorem gradient_firstOrder_one (u : Wkp mu W p 2) :
    W1p.gradient (Wkp.firstOrder 1 u) = Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) :=
  (congrArg W1p.gradient ((Wkp.firstOrder_succ 0 u).trans (Wkp.firstOrder_zero _))).trans
    (Wkp.iteratedGradient_zero (Wkp.lowerOrder 1 u)).symm

/-- Almost-everywhere statements on `W` pull back along a linear automorphism `e` to
`U = e⁻¹(W)`. -/
private theorem quasiMeasurePreserving_restrict_of_coe_eq_preimage (e : E ≃L[ℝ] E)
    (hUW : (U : Set E) = e ⁻¹' W) :
    QuasiMeasurePreserving e (mu.restrict U) (mu.restrict W) :=
  (Measure.ContinuousLinearMap.quasiMeasurePreserving mu (e : E →L[ℝ] E)
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero).restrict (mapsTo_of_coe_eq_preimage e hUW)

/-- Each component `⟪∇u, c⟫` of the weak gradient of `u ∈ W^{2,p}(W)` is the value of a function
`d ∈ W^{1,p}(W)` whose weak gradient has the components `⟪D²u f, c⟫`. -/
private theorem exists_w1p_value_eq_inner_gradient (u : Wkp mu W p 2) (c : E) :
    ∃ d : W1p mu W p,
      W1p.value d =ᵐ[mu.restrict W]
        (fun y => ⟪Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y, c⟫_ℝ) ∧
      ∀ f : E, (fun y => ⟪W1p.gradient d y, f⟫_ℝ) =ᵐ[mu.restrict W]
        fun y => ⟪Wkp.iteratedGradient 1 u y f, c⟫_ℝ := by
  set g := Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 u c
  have h1 : HasWeakLineDerivOn mu W (Wkp.value 2 u) (fun y => ⟪g y, c⟫_ℝ) c := by
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder 1 u)).hasWeakLineDerivOn c
    rw [value_firstOrder_one, gradient_firstOrder_one] at h
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

/-- The weak gradient of `d ∘ e` has the components of the Hessian transformed by `e`. -/
private theorem ae_inner_gradient_compCLE (hp : p ≠ ⊤) (e : E ≃L[ℝ] E)
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
  have hgrad := gradient_firstOrder_one u
  have hval := value_firstOrder_one u
  -- Each component `⟪∇u, c⟫` is the value of some `d c ∈ W^{1,p}(W)`, whose weak gradient has
  -- the components `⟪D²u f, c⟫`.
  choose d hdv hdg using exists_w1p_value_eq_inner_gradient u
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
  have hDe (c f : E) := ae_inner_gradient_compCLE hp e hUW u c (d (e c)) (hdg (e c)) f
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
  · rw [Wkp.firstOrder_succ, Wkp.firstOrder_zero, hw]
    exact compCLE_mem_w1p0Submodule hp e hUW hu

/-! ### Transferring Hessian estimates along a linear change of variables -/

/-- **Transferring the estimate along a linear change of variables.** Let `e e† = A` with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`, let `U = e⁻¹(W)`, and let `v ∈ W^{2,p}(U)` have weak Hessian
`e† ∘ D²u(e ·) ∘ e`. If `u` solves `tr (A D²u) = f` on `W` and the Hessian of `v` is bounded by
`C` times the norm of its trace, then `‖D²u‖ ≤ (C / λ) ‖f‖`. -/
theorem Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp {A : E →L[ℝ] E} (e : E ≃L[ℝ] E)
    (hee : (e : E →L[ℝ] E) ∘L (e : E →L[ℝ] E).adjoint = A) {lam : ℝ} (hlam : 0 < lam)
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
  have habs := abs_det_pos e
  have hmap : (mu.restrict U).map e ≤
      (ENNReal.ofReal |(e : E →L[ℝ] E).det|)⁻¹ • mu.restrict W :=
    map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen
      e.differentiable.differentiableOn e.injective.injOn (mapsTo_of_coe_eq_preimage e hUW) habs
      fun x _ => abs_det_le e x
  have hC' : (ENNReal.ofReal |(e : E →L[ℝ] E).det|)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 habs).ne'
  have hqmp := QuasiMeasurePreserving.of_map_le_smul e.continuous.measurable hmap
  -- `v` solves Poisson's equation with forcing term `f ∘ e`
  set f' := Lp.compOfMapLeSmul ℝ e.continuous.measurable hC' hmap f
  have hf'e := Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) e.continuous.measurable hC' hmap f
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
    exact e.norm_le_inv_mul_norm_adjoint_comp_comp hlam he (Wkp.iteratedGradient 1 u (e y))
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

open scoped ENNReal ContDiff Topology

namespace TauCeti.Wkp

section Hypotheses

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {U V : Opens E} {Φ : E → E} {k : ℕ} {L c : ℝ}

/-- `Φ` is a change of variables of order `k` from `U` into `V`, with constants `L` and `c`: it is
`Cᵏ`, differentiable and injective on `U`, maps `U` into `V`, its derivatives of orders `1`
through `k` are bounded by `L` on `U`, and the absolute value of its Jacobian determinant is at
least `c > 0` on `U`. Differentiability is part of `Cᵏ` once `k ≥ 1`. -/
structure IsChangeOfVariables (k : ℕ) (U V : Opens E) (Φ : E → E) (L c : ℝ) : Prop where
  /-- `Φ` is `Cᵏ` on `U`. -/
  contDiffOn : ContDiffOn ℝ k Φ U
  /-- `Φ` is differentiable on `U`. -/
  differentiableOn : DifferentiableOn ℝ Φ U
  /-- `Φ` is injective on `U`. -/
  injOn : InjOn Φ U
  /-- `Φ` maps `U` into `V`. -/
  mapsTo : MapsTo Φ U V
  /-- The derivatives of `Φ` of orders `1` through `k` are bounded by `L` on `U`. -/
  norm_iteratedFDeriv_le : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L
  /-- The lower bound for the Jacobian is positive. -/
  pos : 0 < c
  /-- The absolute value of the Jacobian determinant of `Φ` is at least `c` on `U`. -/
  le_abs_det : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ Φ x).det|

namespace IsChangeOfVariables

/-- A change of variables of order `k` is one of every lower order. -/
theorem mono {j : ℕ} (h : IsChangeOfVariables k U V Φ L c) (hj : j ≤ k) :
    IsChangeOfVariables j U V Φ L c where
  contDiffOn := h.contDiffOn.of_le (by exact_mod_cast hj)
  differentiableOn := h.differentiableOn
  injOn := h.injOn
  mapsTo := h.mapsTo
  norm_iteratedFDeriv_le i hi hij := h.norm_iteratedFDeriv_le i hi (hij.trans hj)
  pos := h.pos
  le_abs_det := h.le_abs_det

/-- The derivative of a change of variables of order at least one is bounded by `L`. -/
theorem norm_fderiv_le (h : IsChangeOfVariables (k + 1) U V Φ L c) :
    ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L := fun x hx => by
  simpa only [norm_iteratedFDeriv_one] using h.norm_iteratedFDeriv_le 1 le_rfl (by omega) x hx

/-- An invertible continuous linear map `A` mapping `U` into `V` is a change of variables of every
order, with constants `‖A‖` and `|det A|`. -/
theorem continuousLinearEquiv (A : E ≃L[ℝ] E) (hA : MapsTo A U V) :
    IsChangeOfVariables k U V A ‖(A : E →L[ℝ] E)‖ |(A : E →L[ℝ] E).det| where
  contDiffOn := A.contDiff.contDiffOn
  differentiableOn := A.differentiable.differentiableOn
  injOn := A.injective.injOn
  mapsTo := hA
  norm_iteratedFDeriv_le i hi _ x _ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ A = fun _ => (A : E →L[ℝ] E) := funext fun _ => A.fderiv
    rcases n with _ | n
    · simp [hd]
    · rw [hd, iteratedFDeriv_const_of_ne n.succ_ne_zero]
      simp
  pos := abs_pos.2 (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  le_abs_det x _ := by rw [A.fderiv]

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E}

/-- A change of variables is almost everywhere measurable on `U`. -/
theorem aemeasurable (h : IsChangeOfVariables k U V Φ L c) : AEMeasurable Φ (mu.restrict U) :=
  h.differentiableOn.continuousOn.aemeasurable U.isOpen.measurableSet

variable [FiniteDimensional ℝ E]

/-- Precomposition with a change of variables is bounded on `Lᵖ`: the pushforward of the
restriction of `μ` to `U` is at most `c⁻¹` times its restriction to `V`. -/
theorem map_restrict_le (mu : Measure E) [mu.IsAddHaarMeasure]
    (h : IsChangeOfVariables k U V Φ L c) :
    (mu.restrict U).map Φ ≤ (ENNReal.ofReal c)⁻¹ • mu.restrict V :=
  map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen h.differentiableOn h.injOn
    h.mapsTo h.pos h.le_abs_det

/-- Almost-everywhere statements on `V` pull back along a change of variables to
almost-everywhere statements on `U`. -/
theorem ae_comp [mu.IsAddHaarMeasure] (h : IsChangeOfVariables k U V Φ L c) {P : E → Prop}
    (hP : ∀ᵐ y ∂mu.restrict V, P y) : ∀ᵐ x ∂mu.restrict U, P (Φ x) :=
  ae_comp_of_map_absolutelyContinuous h.aemeasurable
    (Measure.absolutelyContinuous_of_le_smul (h.map_restrict_le mu)) hP

end IsChangeOfVariables

end Hypotheses

/-- The constant `c^(-1/p) ∑_{i ≤ k} max 1 L ^ i · #{ordered partitions of i}` bounding the norm
of precomposition with a change of variables of order `k` and constants `L`, `c` on `W^{k,p}`. -/
def compLBound (p : ℝ≥0∞) (k : ℕ) (L c : ℝ) : ℝ :=
  c⁻¹ ^ (1 / p).toReal *
    ∑ i ∈ Finset.range (k + 1), max 1 L ^ i * (Fintype.card (OrderedFinpartition i) : ℝ)

/-- The constant `compLBound p k L c` is nonnegative. -/
theorem compLBound_nonneg (p : ℝ≥0∞) (k : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) :
    0 ≤ compLBound p k L c := by
  unfold compLBound
  have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  positivity

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V W : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ Ψ : E → E} {k : ℕ} {L L' c c' : ℝ}

/-! ### The smooth case -/

section Smooth

/-- The Faà di Bruno estimate integrated over `U`: the `Lᵖ(U)` seminorm of the `i`-th derivative of
`f ∘ Φ` is controlled by the `Lᵖ(V)` seminorms of the derivatives of `f` of order at most `i`. -/
private theorem eLpNorm_iteratedFDeriv_comp_le (h : IsChangeOfVariables k U V Φ L c)
    {f : E → ℝ} (hf : ContDiffOn ℝ k f V) {i : ℕ} (hi : i ≤ k) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) ≤
      ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
        (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ π.length f) p (mu.restrict V) := by
  have hi' : ((i : ℕ) : ℕ∞ω) ≤ k := by exact_mod_cast hi
  have hfΦ : ContDiffOn ℝ k (f ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  calc eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U)
      ≤ eLpNorm (fun x => max 1 L ^ i * ∑ π : OrderedFinpartition i,
          ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        refine eLpNorm_mono_ae_real ((ContinuousOn.continuousOn_iteratedFDeriv hfΦ U.isOpen
          hi').aestronglyMeasurable U.isOpen.measurableSet) ?_
        filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
        exact ((hf.contDiffAt (V.isOpen.mem_nhds (h.mapsTo hx))).of_le
          hi').norm_iteratedFDeriv_comp_le_sum
          ((h.contDiffOn.contDiffAt (U.isOpen.mem_nhds hx)).of_le hi')
          fun j hj1 hji => h.norm_iteratedFDeriv_le j hj1 (hji.trans hi) x hx
    _ = ENNReal.ofReal (max 1 L ^ i) * eLpNorm (∑ π : OrderedFinpartition i,
          fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        rw [← Real.enorm_of_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _),
          ← eLpNorm_const_smul]
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
          eLpNorm (fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        gcongr
        exact eLpNorm_sum_le Fact.out
    _ ≤ _ := by
        gcongr with π
        calc eLpNorm (fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U)
            = eLpNorm ((fun y => ‖iteratedFDeriv ℝ π.length f y‖) ∘ Φ) p (mu.restrict U) := rfl
          _ ≤ (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
              eLpNorm (fun y => ‖iteratedFDeriv ℝ π.length f y‖) p (mu.restrict V) :=
            eLpNorm_comp_le_of_map_le_smul h.aemeasurable (h.map_restrict_le mu) p
          _ = _ := by
            rw [eLpNorm_norm]
            exact (ContinuousOn.continuousOn_iteratedFDeriv hf V.isOpen
              (by exact_mod_cast π.length_le.trans hi)).aestronglyMeasurable
                V.isOpen.measurableSet

/-- If `u ∈ W^{k,p}(V)` has a `Cᵏ` representative `f`, every derivative of `f ∘ Φ` through order
`k` has `Lᵖ(U)` seminorm at most `max 1 L ^ i · #{ordered partitions of i} · c^(-1/p) · ‖u‖`. -/
private theorem eLpNorm_iteratedFDeriv_comp_le_norm (h : IsChangeOfVariables k U V Φ L c)
    (u : Wkp mu V p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f V)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict V] f) {i : ℕ} (hi : i ≤ k) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) ≤
      ENNReal.ofReal (max 1 L ^ i * Fintype.card (OrderedFinpartition i) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖) := by
  have hmem := memLp_iteratedFDeriv_of_contDiffOn k u hf hu
  have hC : (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal = ENNReal.ofReal (c⁻¹ ^ (1 / p).toReal) := by
    rw [← ENNReal.ofReal_inv_of_pos h.pos,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 h.pos.le) ENNReal.toReal_nonneg]
  have hc' : 0 ≤ c⁻¹ ^ (1 / p).toReal := by have := h.pos; positivity
  have hM : 0 ≤ max 1 L ^ i := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  refine (eLpNorm_iteratedFDeriv_comp_le h hf hi).trans ?_
  calc ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
        (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ π.length f) p (mu.restrict V)
      ≤ ENNReal.ofReal (max 1 L ^ i) *
          ∑ _π : OrderedFinpartition i, ENNReal.ofReal (c⁻¹ ^ (1 / p).toReal * ‖u‖) := by
        gcongr with π
        rw [hC, ENNReal.ofReal_mul hc', ← ofReal_lpNorm (hmem _ (π.length_le.trans hi))]
        gcongr
        exact lpNorm_iteratedFDeriv_le_of_contDiffOn k u hf hu _ (π.length_le.trans hi)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hM]
        congr 1
        ring

/-- **The smooth case.** If `u ∈ W^{k,p}(V)` has a `Cᵏ` representative `f`, then `f ∘ Φ`
represents an element of `W^{k,p}(U)` of norm at most `compLBound p k L c * ‖u‖`. -/
private theorem exists_comp_of_contDiffOn (h : IsChangeOfVariables k U V Φ L c)
    (u : Wkp mu V p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f V)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict V] f) :
    ∃ w : Wkp mu U p k, (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
      ‖w‖ ≤ compLBound p k L c * ‖u‖ := by
  have hfΦ : ContDiffOn ℝ k (f ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  have hbound := fun i (hi : i ≤ k) => eLpNorm_iteratedFDeriv_comp_le_norm h u hf hu hi
  have hmem : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) := fun i hi =>
    (hbound i hi).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨w, hw⟩ := exists_value_ae_eq_of_contDiffOn k hfΦ hmem
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw, h.ae_comp hu] with x hx hux
    rw [hx, Function.comp_apply, hux]
  · refine (norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k w hfΦ hw).trans ?_
    calc ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U)
        ≤ ∑ i ∈ Finset.range (k + 1), max 1 L ^ i * Fintype.card (OrderedFinpartition i) *
            c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
          refine Finset.sum_le_sum fun i hi => ENNReal.toReal_le_of_le_ofReal ?_
            (hbound i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
          have := h.pos
          have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
          positivity
      _ = compLBound p k L c * ‖u‖ := by
          rw [compLBound, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring

end Smooth

/-! ### Extension to all of `W^{k,p}` -/

section Extension

/-- The elements of `W^{k,p}(V)` with a representative that is `Cᵏ` on `V`. -/
private def smoothSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (V : Opens E) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (k : ℕ) : Submodule ℝ (Wkp mu V p k) where
  carrier := {u | ∃ f : E → ℝ, ContDiffOn ℝ k f V ∧ (value k u : E → ℝ) =ᵐ[mu.restrict V] f}
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    rw [value_add]
    filter_upwards [Lp.coeFn_add (value k u) (value k v), hu, hv] with x hx hux hvx
    rw [hx, Pi.add_apply, hux, hvx, Pi.add_apply]
  zero_mem' := ⟨0, contDiffOn_const, by
    rw [← valueL_apply, map_zero]
    exact Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro a u ⟨f, hf, hu⟩
    refine ⟨a • f, hf.const_smul a, ?_⟩
    rw [value_smul]
    filter_upwards [Lp.coeFn_smul a (value k u), hu] with x hx hux
    rw [hx, Pi.smul_apply, hux, Pi.smul_apply]

private theorem denseRange_smoothSubmodule_subtype (hp : p ≠ ⊤) :
    DenseRange (smoothSubmodule mu V p k).subtype := by
  refine (dense_contDiffOn_representatives hp k).mono ?_
  rintro u ⟨f, hf, hu⟩
  exact ⟨⟨u, f, hf.of_le (by exact_mod_cast le_top), hu⟩, rfl⟩

/-- Precomposition with `Φ` on the elements with a `Cᵏ` representative. -/
private def compSmooth (h : IsChangeOfVariables k U V Φ L c) (u : smoothSubmodule mu V p k) :
    Wkp mu U p k :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.2.choose_spec.1 u.2.choose_spec.2).choose

private theorem value_compSmooth_ae (h : IsChangeOfVariables k U V Φ L c)
    (u : smoothSubmodule mu V p k) :
    (value k (compSmooth h u) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value k (u : Wkp mu V p k) (Φ x) :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.2.choose_spec.1
    u.2.choose_spec.2).choose_spec.1

private theorem norm_compSmooth_le (h : IsChangeOfVariables k U V Φ L c)
    (u : smoothSubmodule mu V p k) :
    ‖compSmooth h u‖ ≤ compLBound p k L c * ‖(u : Wkp mu V p k)‖ :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.2.choose_spec.1
    u.2.choose_spec.2).choose_spec.2

/-- Precomposition with `Φ` on the elements with a `Cᵏ` representative, as a linear map. -/
private def compSmoothₗ (h : IsChangeOfVariables k U V Φ L c) :
    smoothSubmodule mu V p k →ₗ[ℝ] Wkp mu U p k where
  toFun := compSmooth h
  map_add' u v := by
    refine ext k (Lp.ext ?_)
    rw [value_add]
    filter_upwards [value_compSmooth_ae h (u + v), value_compSmooth_ae h u,
      value_compSmooth_ae h v, Lp.coeFn_add (value k (compSmooth h u)) (value k (compSmooth h v)),
      h.ae_comp (Lp.coeFn_add (value k (u : Wkp mu V p k)) (value k (v : Wkp mu V p k)))]
      with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, Submodule.coe_add, value_add, h5, Pi.add_apply]
  map_smul' a u := by
    refine ext k (Lp.ext ?_)
    rw [value_smul, RingHom.id_apply]
    filter_upwards [value_compSmooth_ae h (a • u), value_compSmooth_ae h u,
      Lp.coeFn_smul a (value k (compSmooth h u)),
      h.ae_comp (Lp.coeFn_smul a (value k (u : Wkp mu V p k)))] with x h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, Submodule.coe_smul, value_smul, h4, Pi.smul_apply]

/-- A measurable modification of `Φ` off `U`, used to express precomposition on `Lᵖ`. -/
private def measurableExtension (Φ : E → E) (U : Opens E) : E → E := by
  classical exact (U : Set E).piecewise Φ fun _ => 0

omit [FiniteDimensional ℝ E] in
private theorem measurable_measurableExtension (h : IsChangeOfVariables k U V Φ L c) :
    Measurable (measurableExtension Φ U) := by
  classical
  exact ContinuousOn.measurable_piecewise h.differentiableOn.continuousOn continuousOn_const
    U.isOpen.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem measurableExtension_ae_eq :
    measurableExtension Φ U =ᵐ[mu.restrict U] Φ := by
  classical
  filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem map_measurableExtension_le (h : IsChangeOfVariables k U V Φ L c) :
    (mu.restrict U).map (measurableExtension Φ U) ≤ (ENNReal.ofReal c)⁻¹ • mu.restrict V := by
  rw [Measure.map_congr measurableExtension_ae_eq]
  exact h.map_restrict_le mu

/-- Precomposition with `Φ` on `Lᵖ`. -/
private def compLp (h : IsChangeOfVariables k U V Φ L c) :
    Lp ℝ p (mu.restrict V) →L[ℝ] Lp ℝ p (mu.restrict U) :=
  Lp.compOfMapLeSmul ℝ (measurable_measurableExtension h)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h.pos).ne') (map_measurableExtension_le h)

private theorem compLp_ae (h : IsChangeOfVariables k U V Φ L c) (g : Lp ℝ p (mu.restrict V)) :
    compLp h g =ᵐ[mu.restrict U] fun x => g (Φ x) := by
  filter_upwards [Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) (measurable_measurableExtension h)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h.pos).ne') (map_measurableExtension_le h) g,
    measurableExtension_ae_eq (mu := mu) (Φ := Φ) (U := U)] with x hx hx'
  rw [compLp, hx, Function.comp_apply, hx']

/-- **Change of variables in `W^{k,p}`.** If `Φ` is a change of variables of order `k` from `U`
into `V` (`TauCeti.Wkp.IsChangeOfVariables`) and `1 ≤ p < ∞`, then precomposition with `Φ` is a
bounded linear operator `W^{k,p}(V) →L[ℝ] W^{k,p}(U)`. Its value is `u ∘ Φ`
(`TauCeti.Wkp.value_compL_ae`), which characterizes it (`TauCeti.Wkp.compL_eq_iff`). It is
constructed as the continuous extension of precomposition on the subspace of elements with `Cᵏ`
representatives, which is dense because `p < ∞`. -/
def compL (h : IsChangeOfVariables k U V Φ L c) (_hp : p ≠ ⊤) :
    Wkp mu V p k →L[ℝ] Wkp mu U p k :=
  (compSmoothₗ h).extendOfNorm (smoothSubmodule mu V p k).subtype

private theorem compL_apply_smooth (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : smoothSubmodule mu V p k) :
    compL h hp (u : Wkp mu V p k) = compSmooth h u :=
  LinearMap.extendOfNorm_eq (denseRange_smoothSubmodule_subtype hp)
    ⟨compLBound p k L c, norm_compSmooth_le h⟩ u

private theorem valueL_comp_compL (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) :
    (valueL k).comp (compL h hp) =
      (compLp h).comp (valueL (mu := mu) (Omega := V) (p := p) k) := by
  refine DFunLike.coe_injective (Continuous.ext_on (denseRange_smoothSubmodule_subtype hp)
    ((valueL k).comp (compL h hp)).continuous ((compLp h).comp (valueL k)).continuous ?_)
  rintro _ ⟨u, rfl⟩
  refine Lp.ext ?_
  simp only [Submodule.coe_subtype, ContinuousLinearMap.coe_comp, Function.comp_apply,
    valueL_apply, compL_apply_smooth h hp]
  exact (value_compSmooth_ae h u).trans (compLp_ae h _).symm

/-- The value of `compL h hp u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem value_compL_ae (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p k) :
    (value k (compL h hp u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) := by
  have he := congrArg (fun T => T u) (valueL_comp_compL h hp)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, valueL_apply] at he
  rw [he]
  exact compLp_ae h _

/-- An element of `W^{k,p}(U)` is `compL h hp u` exactly when its value is `u ∘ Φ` almost
everywhere on `U`. -/
theorem compL_eq_iff (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p k)
    (w : Wkp mu U p k) :
    compL h hp u = w ↔ (value k w : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  ⟨fun hw => hw ▸ value_compL_ae h hp u,
    fun hw => ext k (Lp.ext ((value_compL_ae h hp u).trans hw.symm))⟩

/-- `compL h hp` increases norms by at most the factor `compLBound p k L c`. -/
theorem norm_compL_le (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p k) :
    ‖compL h hp u‖ ≤ compLBound p k L c * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_smoothSubmodule_subtype hp) _
    (norm_compSmooth_le h) u

/-- `compL h hp` has operator norm at most `compLBound p k L c`. -/
theorem opNorm_compL_le (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) :
    ‖(compL h hp : Wkp mu V p k →L[ℝ] Wkp mu U p k)‖ ≤ compLBound p k L c :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_smoothSubmodule_subtype hp)
    (compLBound_nonneg p k L h.pos) (norm_compSmooth_le h)

end Extension

/-! ### Compatibility -/

section Compatibility

/-- Precomposition commutes with forgetting the highest weak derivative.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p (k + 1)) :
    lowerOrder k (compL h hp u) = compL (h.mono k.le_succ) hp (lowerOrder k u) := by
  refine ((compL_eq_iff _ hp _ _).2 ?_).symm
  filter_upwards [value_compL_ae h hp u] with x hx
  rw [← value_succ, hx, value_succ]

/-- **The chain rule.** The first-order part of `compL h hp u` is the first-order change of
variables `TauCeti.W1p.compL` of the first-order part of `u`. In particular its weak gradient is
`DΦ(x)* (∇u)(Φ x)` (`TauCeti.W1p.gradient_compL_ae`).
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem firstOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p (k + 1)) :
    firstOrder k (compL h hp u) =
      W1p.compL Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det
        (firstOrder k u) := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_compL_ae h hp u, W1p.value_compL_ae Φ hp h.differentiableOn h.injOn
    h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det (firstOrder k u)] with x h1 h2
  rw [h2, value_firstOrder, value_firstOrder, h1]

/-- **Functoriality.** Precomposing with `Φ` and then with `Ψ` is precomposing with `Φ ∘ Ψ`. -/
theorem compL_comp (hΦ : IsChangeOfVariables k V W Φ L c)
    (hΨ : IsChangeOfVariables k U V Ψ L' c') {L'' c'' : ℝ}
    (hΦΨ : IsChangeOfVariables k U W (Φ ∘ Ψ) L'' c'') (hp : p ≠ ⊤) (u : Wkp mu W p k) :
    compL hΨ hp (compL hΦ hp u) = compL hΦΨ hp u := by
  refine (compL_eq_iff _ hp _ _).2 ?_
  filter_upwards [value_compL_ae hΦΨ hp u, hΨ.ae_comp (value_compL_ae hΦ hp u)] with x h1 h2
  rw [h1, h2, Function.comp_apply]

end Compatibility

/-! ### Diffeomorphism invariance -/

section Equiv

/-- If `Ψ` maps `V` back to `U` inverse to `Φ`, precomposing with `Φ` and then with `Ψ` is the
identity of `W^{k,p}(V)`. -/
theorem compL_compL_of_rightInvOn (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hp : p ≠ ⊤) (u : Wkp mu V p k) :
    compL hΨ hp (compL hΦ hp u) = u := by
  refine (compL_eq_iff _ hp _ _).2 ?_
  filter_upwards [hΨ.ae_comp (value_compL_ae hΦ hp u), ae_restrict_mem V.isOpen.measurableSet]
    with y hy hyV
  rw [hy, hΦΨ hyV]

/-- **Diffeomorphism invariance of `W^{k,p}`.** If `Φ` is a change of variables of order `k` from
`U` into `V` and `Ψ` one from `V` into `U` with `Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`, then
for `1 ≤ p < ∞` precomposition with `Φ` is an isomorphism of Banach spaces
`W^{k,p}(V) ≃L[ℝ] W^{k,p}(U)`, with inverse precomposition with `Ψ`. -/
def compLEquiv (hΦ : IsChangeOfVariables k U V Φ L c) (hΨ : IsChangeOfVariables k V U Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hp : p ≠ ⊤) : Wkp mu V p k ≃L[ℝ] Wkp mu U p k :=
  ContinuousLinearEquiv.equivOfInverse (compL hΦ hp) (compL hΨ hp)
    (compL_compL_of_rightInvOn hΦ hΨ hΦΨ hp) (compL_compL_of_rightInvOn hΨ hΦ hΨΦ hp)

@[simp]
theorem compLEquiv_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (hp : p ≠ ⊤) (u : Wkp mu V p k) :
    compLEquiv hΦ hΨ hΦΨ hΨΦ hp u = compL hΦ hp u :=
  (rfl)

@[simp]
theorem compLEquiv_symm_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (hp : p ≠ ⊤) (u : Wkp mu U p k) :
    (compLEquiv hΦ hΨ hΦΨ hΨΦ hp).symm u = compL hΨ hp u :=
  (rfl)

end Equiv

end TauCeti.Wkp
