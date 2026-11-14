/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Normed.Affine.Isometry.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop

/-!
# Changes of variables in higher-order Sobolev spaces `W^{k,p}`

This file develops changes of variables in the weak Sobolev spaces `TauCeti.Wkp` on open subsets
of a finite-dimensional real inner product space `E`:

1. **Linear changes of variables in `W^{2,p}`** (`1 ≤ p < ∞`): for a continuous linear automorphism
   `e : E ≃L[ℝ] E` and `U = e⁻¹(W)`, precomposition with `e` maps `W^{2,p}(W)` to `W^{2,p}(U)` with
   weak Hessian `D²(u ∘ e)(x) = e† ∘ D²u(e x) ∘ e` almost everywhere on `U` and preserves zero
   boundary values of the first-order part
   (`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). When `e e† = A` and
   `‖e⁻¹ x‖ ≤ ‖x‖ / √λ`, this transfers an `Lᵖ` Hessian bound by the Laplacian to solutions of
   `tr (A D²u) = f` (`TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`).
2. **General `Cᵏ` changes of variables in `W^{k,p}`** (`1 ≤ p ≤ ∞`): if `Φ` is a change of
   variables of order `k` from `U` into `V` (`TauCeti.Wkp.IsChangeOfVariables`) — `Cᵏ`,
   differentiable and injective on `U`, mapping `U` into `V`, with derivatives of orders `1`
   through `k` bounded by `L` and `|det DΦ| ≥ c > 0` on `U` — then precomposition with `Φ` is a
   bounded linear operator `TauCeti.Wkp.compL : Wkp mu V p k →L[ℝ] Wkp mu U p k` of norm at most
   `TauCeti.Wkp.compLBound p k L c`. For a `Cᵏ` diffeomorphism with bounded derivatives in both
   directions this gives a Banach-space isomorphism `TauCeti.Wkp.compLEquiv`.
3. **Left-invertible `Cᵏ` maps** (`k : ℕ`, `1 ≤ p ≤ ∞`): when `Φ` is `Cᵏ` on `U` mapping `U` into
   `V` and admits a differentiable left inverse `Ψ` on `V` with `‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`,
   the Jacobian determinant of `Φ` (for `k ≥ 1`) or the pushforward of `mu` along `Φ` (for `k = 0`)
   is controlled by `max 1 L' ^ finrank ℝ E`, giving the precomposition operator
   `TauCeti.Wkp.compOfLeftInvOnL` and the uniform norm bound `TauCeti.Wkp.exists_norm_comp_le`.

## The argument

For `W^{2,p}` along a linear automorphism `e`, the first-order part of `u ∘ e` comes from
`TauCeti.W1p.compL`, each gradient component `⟪∇u, e c⟫` lies in `W^{1,p}(W)`, and precomposing
those components with `e` places `u ∘ e` in `W^{2,p}(U)` via
`TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`.

For `TauCeti.Wkp.compL`, the Faà di Bruno bound `ContDiffAt.norm_iteratedFDeriv_comp_le_sum`
controls the `Lᵖ(U)` seminorms of all derivatives through order `k` on elements with `Cᵏ`
representatives. When `p < ∞`, `Cᵏ` representatives are dense
(`TauCeti.Wkp.dense_contDiffOn_representatives`), so continuous extension gives the operator and
the top-derivative bound. At `p = ∞`, smooth functions are no longer dense in `W^{k,∞}`, so
precomposition is constructed inductively on `k`: at order `0` by
`MeasureTheory.Lp.compOfMapLeSmul`, at order `1` by the weak chain rule
`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`, and at order `m + 2` by restricting to small
balls with relatively compact target neighbourhoods, pulling back in `W^{m+2,q}` for `1 ≤ q < ∞`
via `TauCeti.Wkp.ofExponentLEL`, passing `q → ∞` with `TauCeti.eLpNorm_exponent_top_le_liminf`, and
gluing the local weak derivatives via `TauCeti.exists_hasWeakFDerivOn_iSup`.

## Main declarations

* `TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`,
  `TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`: linear changes of variables
  and transfer of Hessian estimates in `W^{2,p}`.
* `TauCeti.Wkp.IsChangeOfVariables`: bundled `Cᵏ` change-of-variables hypotheses, including
  `IsChangeOfVariables.of_leftInvOn`.
* `TauCeti.Wkp.compL`, `TauCeti.Wkp.compLEquiv`: bounded precomposition and diffeomorphism
  invariance on `W^{k,p}` for `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.compOfLeftInvOnL`, `TauCeti.Wkp.exists_norm_comp_le`: precomposition and uniform
  norm bound for left-invertible `Cᵏ` maps across all orders `k : ℕ` and exponents `1 ≤ p ≤ ∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2–§5.4.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.41.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Chapter 4.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
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

/-- A translation `x ↦ x + a` mapping `U` into `V` is a change of variables of every order, with
constants `1` and `1`. -/
theorem add_const (a : E) (hA : MapsTo (· + a) U V) :
    IsChangeOfVariables k U V (· + a) 1 1 := by
  have hd : fderiv ℝ (· + a) = fun _ : E ↦ ContinuousLinearMap.id ℝ E :=
    funext fun x ↦ by simp [fderiv_add_const]
  exact
    { contDiffOn := (contDiff_id.add contDiff_const).contDiffOn
      differentiableOn := (differentiable_id.add_const a).differentiableOn
      injOn := (add_left_injective a).injOn
      mapsTo := hA
      norm_iteratedFDeriv_le := fun i hi _ x _ ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
        rw [← norm_iteratedFDeriv_fderiv]
        rcases n with _ | n
        · simpa [hd] using ContinuousLinearMap.norm_id_le
        · rw [hd, iteratedFDeriv_const_of_ne n.succ_ne_zero]
          simp
      pos := one_pos
      le_abs_det := fun x _ ↦ by simp [ContinuousLinearMap.det] }

/-- Conjugating a change of variables `Φ` by an affine isometry equivalence `e` gives a change of
variables `e⁻¹ ∘ Φ ∘ e` with the same constants: its iterated derivatives have the same norms and
its Jacobian determinant is that of `Φ`. -/
theorem conj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {U' V' : Opens F}
    (h : IsChangeOfVariables k U V Φ L c) (e : F ≃ᵃⁱ[ℝ] E) (hU : MapsTo e U' U)
    (hV : MapsTo e.symm V V') : IsChangeOfVariables k U' V' (e.symm ∘ Φ ∘ e) L c := by
  set A := e.toAffineIsometry.toContinuousAffineMap
  set B := e.symm.toAffineIsometry.toContinuousAffineMap
  have hΦe : ContDiffOn ℝ k (Φ ∘ e) U' := h.contDiffOn.comp A.contDiff.contDiffOn hU
  refine
    { contDiffOn := B.contDiff.comp_contDiffOn hΦe
      differentiableOn :=
        B.differentiable.comp_differentiableOn (h.differentiableOn.comp A.differentiableOn hU)
      injOn := e.symm.injective.comp_injOn (h.injOn.comp e.injective.injOn hU)
      mapsTo := hV.comp (h.mapsTo.comp hU)
      norm_iteratedFDeriv_le := fun i hi hik x hx ↦ ?_
      pos := h.pos
      le_abs_det := fun x hx ↦ ?_ }
  · rw [AffineIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ (by omega),
      AffineIsometryEquiv.norm_iteratedFDeriv_comp_right]
    exact h.norm_iteratedFDeriv_le i hi hik (e x) (hU hx)
  · -- The derivative is `D(e⁻¹) ∘ DΦ(e x) ∘ De`, the conjugate of `DΦ(e x)` by the linear part
    -- of `e`, so it has the same determinant.
    have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (e x)) (e x) :=
      (h.differentiableOn.differentiableAt (U.isOpen.mem_nhds (hU hx))).hasFDerivAt
    have hd : HasFDerivAt (e.symm ∘ Φ ∘ e)
        (B.contLinear.comp ((fderiv ℝ Φ (e x)).comp A.contLinear)) x :=
      (B.hasFDerivAt (x := Φ (e x))).comp x (hΦ.comp x (A.hasFDerivAt (x := x)))
    have hconj : (B.contLinear.comp ((fderiv ℝ Φ (e x)).comp A.contLinear) : F →ₗ[ℝ] F) =
        (e.linearIsometryEquiv.symm.toLinearEquiv : E →ₗ[ℝ] F) ∘ₗ
          (fderiv ℝ Φ (e x) : E →ₗ[ℝ] E) ∘ₗ
            (e.linearIsometryEquiv.symm.toLinearEquiv.symm : F →ₗ[ℝ] E) := by
      -- The linear part of the continuous affine map underlying an affine isometry equivalence
      -- is its linear isometry equivalence by construction; Mathlib states no lemma for this.
      ext y
      rfl
    rw [hd.fderiv, ContinuousLinearMap.det, hconj, LinearMap.det_conj]
    exact h.le_abs_det (e x) (hU hx)

/-- **Changes of variables on relatively compact sets.** Let `Φ` be `Cᵏ` with `k ≥ 1` on an open
set `Ω`. If the closure of an open `U` is compact and contained in `Ω`, `Φ` is injective on `U`
with invertible derivative on `closure U`, and `Φ` maps `U` into `V`, then `Φ` is a change of
variables of order `k` from `U` into `V`. The constant `L` is a bound for the derivatives of
orders `1` through `k` on `closure U`, and `c` is a positive lower bound for the absolute value
of the Jacobian determinant there; both exist by compactness. -/
theorem exists_of_isCompact_closure {Ω : Set E} (hΩ : IsOpen Ω)
    (hk : 1 ≤ k) (hΦ : ContDiffOn ℝ k Φ Ω) (hinj : InjOn Φ U)
    (hdet : ∀ x ∈ closure (U : Set E), (fderiv ℝ Φ x).det ≠ 0)
    (hUc : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)
    (hUV : MapsTo Φ U V) : ∃ L c, IsChangeOfVariables k U V Φ L c := by
  have hk' : (1 : ℕ∞ω) ≤ k := by exact_mod_cast hk
  obtain ⟨L, -, hL⟩ := hΦ.exists_nonneg_bound_iteratedFDeriv_of_isOpen hΩ hUc hUΩ
  have hdetc : ContinuousOn (fun x => |(fderiv ℝ Φ x).det|) (closure (U : Set E)) :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      ((hΦ.continuousOn_fderiv_of_isOpen hΩ hk').mono hUΩ)).abs
  obtain ⟨c, hc, hcdet⟩ := hUc.exists_forall_le' hdetc fun x hx => abs_pos.2 (hdet x hx)
  refine ⟨L, c,
    { contDiffOn := hΦ.mono (subset_closure.trans hUΩ)
      differentiableOn :=
        (hΦ.mono (subset_closure.trans hUΩ)).differentiableOn (by positivity)
      injOn := hinj
      mapsTo := hUV
      norm_iteratedFDeriv_le := fun i _ hik x hx => hL i hik x (subset_closure hx)
      pos := hc
      le_abs_det := fun x hx => hcdet x (subset_closure hx) }⟩

/-- The identity map is a change of variables of every order from `U` to itself, with constants
`1` and `1`. -/
theorem id (k : ℕ) (U : Opens E) : IsChangeOfVariables k U U _root_.id 1 1 := by
  convert add_const (k := k) (U := U) (V := U) (0 : E) (fun _ hx => by simpa using hx) using 1
  ext x
  exact (add_zero x).symm

/-- Restricting the source and target of a change of variables preserves its constants. -/
theorem restrict {U' V' : Opens E} (h : IsChangeOfVariables k U V Φ L c)
    (hU : U' ≤ U) (hUV : MapsTo Φ U' V') : IsChangeOfVariables k U' V' Φ L c where
  contDiffOn := h.contDiffOn.mono hU
  differentiableOn := h.differentiableOn.mono hU
  injOn := h.injOn.mono hU
  mapsTo := hUV
  norm_iteratedFDeriv_le i hi hik x hx := h.norm_iteratedFDeriv_le i hi hik x (hU hx)
  pos := h.pos
  le_abs_det x hx := h.le_abs_det x (hU hx)

/-- **A `Cᵏ` map with a differentiable left inverse is a change of variables.** If `k ≥ 1`, `Φ` is
`Cᵏ` on `U` with derivatives of orders `1` through `k` bounded by `L` and maps `U` into `V`, and
`Ψ` is differentiable on `V` with `Ψ (Φ x) = x` and `‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, then `Φ` is
a change of variables of order `k` with Jacobian lower bound `(max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem of_leftInvOn {Ψ : E → E} {L' : ℝ} (hk : 1 ≤ k) (hΦ : ContDiffOn ℝ k Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    IsChangeOfVariables k U V Φ L (max 1 L' ^ Module.finrank ℝ E)⁻¹ := by
  have hdiff : DifferentiableOn ℝ Φ U :=
    hΦ.differentiableOn (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)
  refine
    { contDiffOn := hΦ
      differentiableOn := hdiff
      injOn := hΨΦ.injOn
      mapsTo := hmaps
      norm_iteratedFDeriv_le := hL
      pos := inv_pos.2 (pow_pos (zero_lt_one.trans_le (le_max_left 1 L')) _)
      le_abs_det := fun x hx => ?_ }
  have hΦx : DifferentiableAt ℝ Φ x := (hdiff x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hΨx : DifferentiableAt ℝ Ψ (Φ x) :=
    (hΨ (Φ x) (hmaps hx)).differentiableAt (V.isOpen.mem_nhds (hmaps hx))
  have hev : Ψ ∘ Φ =ᶠ[𝓝 x] _root_.id :=
    Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hx) fun y hy => hΨΦ hy
  exact hΦx.inv_pow_le_abs_det_fderiv_of_eventuallyEq hΨx hev
    ((hL' x hx).trans (le_max_right 1 L'))

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

section Calculus

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
        rw [← Real.eNorm_of_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _),
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

private theorem norm_iteratedGradient_compSmooth_le (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : smoothSubmodule mu V p (k + 1)) :
    ‖iteratedGradient k (compSmooth h u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖(u : Wkp mu V p (k + 1))‖ := by
  have hf := u.2.choose_spec.1
  have hu := u.2.choose_spec.2
  have hfΦ : ContDiffOn ℝ (k + 1) (u.2.choose ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  have hw : (value (k + 1) (compSmooth h u) : E → ℝ) =ᵐ[mu.restrict U] u.2.choose ∘ Φ :=
    (value_compSmooth_ae h u).trans (h.ae_comp hu)
  rw [norm_iteratedGradient_eq_lpNorm_of_contDiffOn k (compSmooth h u) hfΦ hw]
  refine ENNReal.toReal_le_of_le_ofReal ?_
    (eLpNorm_iteratedFDeriv_comp_le_norm h (u : Wkp mu V p (k + 1)) hf hu le_rfl)
  have := h.pos
  have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  positivity

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem measurable_measurableExtension_of_continuousOn (hΦ : ContinuousOn Φ U) :
    Measurable (measurableExtension Φ U) := by
  classical
  exact ContinuousOn.measurable_piecewise hΦ continuousOn_const U.isOpen.measurableSet

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem measurable_measurableExtension (h : IsChangeOfVariables k U V Φ L c) :
    Measurable (measurableExtension Φ U) :=
  measurable_measurableExtension_of_continuousOn h.differentiableOn.continuousOn

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

private theorem norm_compLp_le (h : IsChangeOfVariables k U V Φ L c)
    (g : Lp ℝ p (mu.restrict V)) :
    ‖compLp h g‖ ≤ c⁻¹ ^ (1 / p).toReal * ‖g‖ := by
  refine (Lp.norm_compOfMapLeSmul_le (measurable_measurableExtension h)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h.pos).ne') (map_measurableExtension_le h) g).trans
    (le_of_eq ?_)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_ofReal h.pos.le]

/-- Precomposition in `W^{k,p}` for finite exponent `p < ∞`, defined by continuous extension from
`Cᵏ` representatives. -/
private def compLFinite (h : IsChangeOfVariables k U V Φ L c) (_hp : p ≠ ⊤) :
    Wkp mu V p k →L[ℝ] Wkp mu U p k :=
  (compSmoothₗ h).extendOfNorm (smoothSubmodule mu V p k).subtype

private theorem compLFinite_apply_smooth (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : smoothSubmodule mu V p k) :
    compLFinite h hp (u : Wkp mu V p k) = compSmooth h u :=
  LinearMap.extendOfNorm_eq (denseRange_smoothSubmodule_subtype hp)
    ⟨compLBound p k L c, norm_compSmooth_le h⟩ u

private theorem valueL_comp_compLFinite (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) :
    (valueL k).comp (compLFinite h hp) =
      (compLp h).comp (valueL (mu := mu) (Omega := V) (p := p) k) := by
  refine DFunLike.coe_injective (Continuous.ext_on (denseRange_smoothSubmodule_subtype hp)
    ((valueL k).comp (compLFinite h hp)).continuous ((compLp h).comp (valueL k)).continuous ?_)
  rintro _ ⟨u, rfl⟩
  refine Lp.ext ?_
  simp only [Submodule.coe_subtype, ContinuousLinearMap.coe_comp, Function.comp_apply,
    valueL_apply, compLFinite_apply_smooth h hp]
  exact (value_compSmooth_ae h u).trans (compLp_ae h _).symm

private theorem value_compLFinite_ae (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p k) :
    (value k (compLFinite h hp u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) := by
  have he := congrArg (fun T => T u) (valueL_comp_compLFinite h hp)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, valueL_apply] at he
  rw [he]
  exact compLp_ae h _

private theorem norm_compLFinite_le (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p k) :
    ‖compLFinite h hp u‖ ≤ compLBound p k L c * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_smoothSubmodule_subtype hp) _
    (norm_compSmooth_le h) u

private theorem norm_iteratedGradient_compLFinite_le
    (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p (k + 1)) :
    ‖iteratedGradient k (compLFinite h hp u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
  let C := max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) * c⁻¹ ^ (1 / p).toReal
  have hclosed : IsClosed {b : Wkp mu V p (k + 1) |
      ‖iteratedGradientL k (compLFinite h hp b)‖ ≤ C * ‖b‖} :=
    isClosed_le (((iteratedGradientL k).comp (compLFinite h hp)).continuous.norm)
      (continuous_const.mul continuous_norm)
  rw [← iteratedGradientL_apply]
  refine (denseRange_smoothSubmodule_subtype hp).induction_on u hclosed fun v => ?_
  simp only [Submodule.coe_subtype, compLFinite_apply_smooth h hp]
  rw [iteratedGradientL_apply]
  exact norm_iteratedGradient_compSmooth_le h v

/-! ### The endpoint `p = ∞` -/

/-- Passing `q → ∞` on a family of `L^q` seminorm bounds `M * a ^ (1 / q)` yields a pointwise
almost-everywhere norm bound `M`. -/
private theorem ae_norm_le_of_forall_nnreal_eLpNorm_le {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {ν : Measure α} {f : α → F} {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (h : ∀ q : NNReal, 1 ≤ q → eLpNorm f q ν ≤ ENNReal.ofReal (M * a ^ (1 / (q : ℝ)))) :
    ∀ᵐ y ∂ν, ‖f y‖ ≤ M := by
  have hlim : Tendsto (fun q : NNReal => ENNReal.ofReal (M * a ^ (1 / (q : ℝ)))) atTop
      (𝓝 (ENNReal.ofReal M)) := by
    have h0 : Tendsto (fun q : NNReal => (1 : ℝ) / (q : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (NNReal.tendsto_coe_atTop.2 tendsto_id)
    rw [show ENNReal.ofReal M = ENNReal.ofReal (M * a ^ (0 : ℝ)) by simp]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((Real.continuousAt_const_rpow ha.ne').tendsto.comp h0))
  have htop : eLpNorm f ⊤ ν ≤ ENNReal.ofReal M :=
    eLpNorm_exponent_top_le_liminf.trans ((liminf_le_liminf
      ((eventually_ge_atTop (1 : NNReal)).mono h)).trans_eq hlim.liminf_eq)
  have hmem : MemLp f ⊤ ν := htop.trans_lt ENNReal.ofReal_lt_top
  filter_upwards [ae_le_lpNorm_exponent_top hmem] with y hy
  exact hy.trans (ENNReal.toReal_le_of_le_ofReal hM htop)

/-- First-order precomposition at `p = ∞`, built directly from the weak chain rule
`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`. -/
private theorem exists_comp_top_one (h : IsChangeOfVariables 1 U V Φ L c) (u : Wkp mu V ⊤ 1) :
    ∃ w : Wkp mu U ⊤ 1,
      (value 1 w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value 1 u (Φ x)) ∧
      ‖iteratedGradient 0 w‖ ≤ max 1 L * ‖u‖ ∧
      ‖w‖ ≤ compLBound ⊤ 1 L c * ‖u‖ := by
  set u₀ : Lp ℝ ⊤ (mu.restrict U) := compLp h (value 1 u)
  set g₀ : E → E := fun x => (fderiv ℝ Φ x).adjoint (iteratedGradient 0 u (Φ x))
  have hweak₀ : HasWeakFDerivOn mu U u₀ (fun x => innerSL ℝ (g₀ x)) := by
    have hc0 := (hasWeakFDerivOn_value u).comp_contDiffOn_diffeo h.contDiffOn h.injOn
      (fun x hx => abs_ne_zero.1 (h.pos.trans_le (h.le_abs_det x hx)).ne') h.mapsTo
    refine (hc0.congr_ae (compLp_ae h (value 1 u)).symm).congr_ae_deriv (.of_forall fun x => ?_)
    ext v
    simp [g₀, ContinuousLinearMap.adjoint_inner_left]
  have hg₀_ae : ∀ᵐ x ∂mu.restrict U, ‖g₀ x‖ ≤ max 1 L * ‖u‖ := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet,
      h.ae_comp (Lp.ae_norm_le_norm_top (iteratedGradient 0 u))] with x hxU hgu
    calc ‖g₀ x‖ ≤ ‖(fderiv ℝ Φ x).adjoint‖ * ‖iteratedGradient 0 u (Φ x)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ Φ x‖ * ‖iteratedGradient 0 u (Φ x)‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ max 1 L * ‖u‖ :=
          mul_le_mul ((h.norm_fderiv_le x hxU).trans (le_max_right 1 L))
            (hgu.trans (norm_iteratedGradient_le 0 u)) (norm_nonneg _)
            (zero_le_one.trans (le_max_left 1 L))
  have hg₀_mem : MemLp g₀ ⊤ (mu.restrict U) :=
    memLp_top_of_bound hweak₀.locallyIntegrableOn_gradient.aestronglyMeasurable _ hg₀_ae
  set g : Lp E ⊤ (mu.restrict U) := hg₀_mem.toLp g₀
  have hweak : HasWeakFDerivOn mu U u₀ (fun x => innerSL ℝ (g x)) :=
    hweak₀.congr_ae_deriv (by filter_upwards [hg₀_mem.coeFn_toLp] with x hx; rw [hx])
  set w : Wkp mu U ⊤ 1 := W1p.mk u₀ g hweak
  have hgn : ‖g‖ ≤ max 1 L * ‖u‖ := Lp.norm_top_le_of_ae_bound
    (mul_nonneg (zero_le_one.trans (le_max_left 1 L)) (norm_nonneg u))
    (hg₀_mem.coeFn_toLp.mp (hg₀_ae.mono fun _ hx hxy => hxy ▸ hx))
  have hu₀n : ‖u₀‖ ≤ ‖u‖ := by
    refine le_trans (norm_compLp_le h (value 1 u)) ?_
    simpa [ENNReal.div_top] using norm_value_le 1 u
  have hval : value 1 w = u₀ := (value_one w).trans (W1p.value_mk u₀ g hweak)
  have hgrad : iteratedGradient 0 w = g :=
    (iteratedGradient_zero w).trans (W1p.gradient_mk u₀ g hweak)
  have hlow : lowerOrder 0 w = u₀ := (lowerOrder_zero w).trans (W1p.value_mk u₀ g hweak)
  refine ⟨w, ?_, hgrad.symm ▸ hgn, ?_⟩
  · rw [hval]
    exact compLp_ae h (value 1 u)
  · have hsum : compLBound ⊤ 1 L c = 1 + max 1 L := by
      simp [compLBound, Finset.sum_range_succ, Fintype.card_unique]
    have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 w
    rw [hlow, hgrad] at hle
    rw [hsum, add_mul, one_mul]
    linarith

/-- On finite-measure open sets `B` and `V'`, pulling back `u ∈ W^{m+2,∞}(V')` in `W^{m+2,q}` for
`1 ≤ q < ∞` produces a weak derivative of `iteratedGradient m w_B` bounded almost everywhere by
`max 1 L ^ (m + 2) · #{ordered partitions of m + 2} · ‖u‖`. -/
private theorem exists_local_deriv_comp_top {m : ℕ} {B V' : Opens E}
    [IsFiniteMeasure (mu.restrict (B : Set E))] [IsFiniteMeasure (mu.restrict (V' : Set E))]
    (h : IsChangeOfVariables (m + 2) B V' Φ L c) (u : Wkp mu V' ⊤ (m + 2))
    (w_B : Wkp mu B ⊤ (m + 1))
    (hw_B : (value (m + 1) w_B : E → ℝ) =ᵐ[mu.restrict B] fun y => value (m + 2) u (Φ y)) :
    ∃ D_B : E → IteratedGradient E (m + 1),
      HasWeakFDerivOn mu B (iteratedGradient m w_B) D_B ∧
      ∀ᵐ y ∂mu.restrict B, ‖D_B y‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ := by
  set M : ℝ := max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2))
  have hM : 0 ≤ M := by have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _); positivity
  set v₁ : Wkp mu B 1 (m + 2) :=
    compLFinite h ENNReal.one_ne_top (ofExponentLEL le_top (m + 2) u)
  have hv₁_val : (value (m + 2) v₁ : E → ℝ) =ᵐ[mu.restrict B] fun y => value (m + 2) u (Φ y) :=
    (value_compLFinite_ae h ENNReal.one_ne_top _).trans
      (h.ae_comp (value_ofExponentLEL_ae le_top (m + 2) u))
  have hlow_eq : lowerOrder (m + 1) v₁ = ofExponentLEL le_top (m + 1) w_B :=
    ext (m + 1) (Lp.ext ((value_succ (m + 1) v₁ ▸ hv₁_val).trans
      (hw_B.symm.trans (value_ofExponentLEL_ae le_top (m + 1) w_B).symm)))
  have hweak : HasWeakFDerivOn mu B (iteratedGradient m w_B) (iteratedGradient (m + 1) v₁) :=
    (hasWeakFDerivOn_iteratedGradient m v₁).congr_ae
      (hlow_eq ▸ iteratedGradient_ofExponentLEL_ae le_top m w_B)
  refine ⟨iteratedGradient (m + 1) v₁, hweak, ?_⟩
  refine ae_norm_le_of_forall_nnreal_eLpNorm_le (mul_nonneg hM (norm_nonneg u))
    (mul_pos (inv_pos.2 h.pos) (zero_lt_one.trans_le (le_max_left 1 (mu.real (V' : Set E)))))
    fun q hq => ?_
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  set v_q : Wkp mu B q (m + 2) :=
    compLFinite h ENNReal.coe_ne_top (ofExponentLEL le_top (m + 2) u)
  have hvq_eq : ofExponentLEL (p := 1) (by exact_mod_cast hq) (m + 2) v_q = v₁ :=
    ext (m + 2) (Lp.ext ((value_ofExponentLEL_ae _ (m + 2) v_q).trans
      (((value_compLFinite_ae h ENNReal.coe_ne_top _).trans
        (h.ae_comp (value_ofExponentLEL_ae le_top (m + 2) u))).trans hv₁_val.symm)))
  have hD_ae : (iteratedGradient (m + 1) v₁ : E → _) =ᵐ[mu.restrict B]
      iteratedGradient (m + 1) v_q :=
    hvq_eq ▸ iteratedGradient_ofExponentLEL_ae (p := 1) (by exact_mod_cast hq) (m + 1) v_q
  rw [eLpNorm_congr_ae hD_ae, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := norm_iteratedGradient_compLFinite_le h ENNReal.coe_ne_top
    (ofExponentLEL (p := q) le_top (m + 2) u)
  have h2 := norm_ofExponentLEL_apply_le (mu := mu) (Omega := V') (p := q) le_top (m + 2) u
  have hmu : (mu V' ^ (1 / (q : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal)).toReal ≤
      max 1 (mu.real (V' : Set E)) ^ (1 / (q : ℝ)) := by
    simp only [ENNReal.coe_toReal, ENNReal.toReal_top, div_zero, sub_zero,
      ← ENNReal.toReal_rpow, ← measureReal_def]
    exact Real.rpow_le_rpow measureReal_nonneg (le_max_right 1 _) (by positivity)
  have hexp : (1 / (q : ℝ≥0∞)).toReal = 1 / (q : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.coe_toReal]
  rw [hexp] at h1
  calc ‖iteratedGradient (m + 1) v_q‖
      ≤ M * c⁻¹ ^ (1 / (q : ℝ)) *
          ((mu V' ^ (1 / (q : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal)).toReal * ‖u‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by have := h.pos; positivity))
    _ ≤ M * c⁻¹ ^ (1 / (q : ℝ)) * (max 1 (mu.real (V' : Set E)) ^ (1 / (q : ℝ)) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmu (norm_nonneg u))
          (mul_nonneg hM (Real.rpow_nonneg (inv_nonneg.2 h.pos.le) _))
    _ = M * ‖u‖ * (c⁻¹ * max 1 (mu.real (V' : Set E))) ^ (1 / (q : ℝ)) := by
        rw [Real.mul_rpow (inv_nonneg.2 h.pos.le) (zero_le_one.trans (le_max_left 1 _))]
        ring

private theorem exists_ball_deriv_comp_top {m : ℕ} (h : IsChangeOfVariables (m + 2) U V Φ L c)
    (u : Wkp mu V ⊤ (m + 2)) (w₀ : Wkp mu U ⊤ (m + 1))
    (hw₀ : (value (m + 1) w₀ : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value (m + 1) (lowerOrder (m + 1) u) (Φ x)) (x : U) :
    ∃ (B : Opens E) (D_B : E → IteratedGradient E (m + 1)),
      (x : E) ∈ B ∧ B ≤ U ∧ HasWeakFDerivOn mu B (iteratedGradient m w₀) D_B ∧
      ∀ᵐ y ∂mu.restrict B, ‖D_B y‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds x.2)
  set B : Opens E := ⟨Metric.ball (x : E) r, Metric.isOpen_ball⟩
  have hBU : B ≤ U := Metric.ball_subset_closedBall.trans hrU
  have hK : IsCompact (Φ '' Metric.closedBall (x : E) r) :=
    (isCompact_closedBall (x : E) r).image_of_continuousOn
      (h.differentiableOn.continuousOn.mono hrU)
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK V.isOpen
    ((Set.image_mono hrU).trans h.mapsTo.image_subset)
  set V' : Opens E := ⟨W, hWo⟩
  have hV'V : V' ≤ V := subset_closure.trans hWV
  have : IsFiniteMeasure (mu.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (V' : Set E)) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
  have hBV' : MapsTo Φ B V' := fun y hy => hKW ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
  have hw_B : (value (m + 1) (restrictL hBU (m + 1) w₀) : E → ℝ) =ᵐ[mu.restrict B]
      fun y => value (m + 2) (restrictL hV'V (m + 2) u) (Φ y) := by
    filter_upwards [value_restrictL_ae hBU (m + 1) w₀,
      ae_restrict_of_ae_restrict_of_subset hBU hw₀,
      (h.restrict hBU hBV').ae_comp (value_restrictL_ae hV'V (m + 2) u)] with y h1 h2 h3
    rw [h1, h2, h3, value_succ (m + 1) u]
  obtain ⟨D_B, hD_weak, hD_ae⟩ := exists_local_deriv_comp_top (h.restrict hBU hBV')
    (restrictL hV'V (m + 2) u) (restrictL hBU (m + 1) w₀) hw_B
  have hM : 0 ≤ max 1 L ^ (m + 2) * (Fintype.card (OrderedFinpartition (m + 2)) : ℝ) := by
    have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
    positivity
  refine ⟨B, D_B, Metric.mem_ball_self hr, hBU,
    hD_weak.congr_ae (iteratedGradient_restrictL_ae hBU m w₀), ?_⟩
  filter_upwards [hD_ae] with y hy
  exact hy.trans (mul_le_mul_of_nonneg_left (norm_restrictL_le hV'V (m + 2) u) hM)

/-- Inductive step at order `m + 2` and exponent `p = ∞`, gluing the local weak derivatives
produced by `exists_ball_deriv_comp_top` across an open cover by balls. -/
private theorem exists_comp_top_succ_succ {m : ℕ} (h : IsChangeOfVariables (m + 2) U V Φ L c)
    (u : Wkp mu V ⊤ (m + 2)) (w₀ : Wkp mu U ⊤ (m + 1))
    (hw₀ : (value (m + 1) w₀ : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value (m + 1) (lowerOrder (m + 1) u) (Φ x))
    (hw₀_norm : ‖w₀‖ ≤ compLBound ⊤ (m + 1) L c * ‖lowerOrder (m + 1) u‖) :
    ∃ w : Wkp mu U ⊤ (m + 2),
      (value (m + 2) w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value (m + 2) u (Φ x)) ∧
      ‖iteratedGradient (m + 1) w‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ ∧
      ‖w‖ ≤ compLBound ⊤ (m + 2) L c * ‖u‖ := by
  set M : ℝ := max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2))
  have hM : 0 ≤ M := by have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _); positivity
  choose B D_B hxB hBU hD_weak hD_ae using exists_ball_deriv_comp_top h u w₀ hw₀
  have hsup : (⨆ x : U, B x) = U := le_antisymm (iSup_le hBU) fun y hy =>
    Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxB ⟨y, hy⟩⟩
  obtain ⟨D_fun, hweak, hD_eq⟩ := exists_hasWeakFDerivOn_iSup B D_B hD_weak
  rw [hsup] at hweak
  have hD_bound : ∀ᵐ y ∂mu.restrict U, ‖D_fun y‖ ≤ M * ‖u‖ :=
    ae_restrict_of_subset_iUnion_isOpen (fun x => (B x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxB ⟨y, hy⟩⟩) fun x => by
        filter_upwards [hD_eq x, hD_ae x] with y hy1 hy2
        exact hy1 ▸ hy2
  have hD_mem : MemLp D_fun ⊤ (mu.restrict U) :=
    memLp_top_of_bound hweak.locallyIntegrableOn_deriv.aestronglyMeasurable _ hD_bound
  set D : Lp (IteratedGradient E (m + 1)) ⊤ (mu.restrict U) := hD_mem.toLp D_fun
  have hDn : ‖D‖ ≤ M * ‖u‖ := Lp.norm_top_le_of_ae_bound (mul_nonneg hM (norm_nonneg u))
    (hD_mem.coeFn_toLp.mp (hD_bound.mono fun _ hy hxy => hxy ▸ hy))
  set w : Wkp mu U ⊤ (m + 2) := mk m w₀ D (hweak.congr_ae_deriv hD_mem.coeFn_toLp.symm)
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [value_mk, value_succ (m + 1) u]
    exact hw₀
  · simpa only [w, iteratedGradient_mk] using hDn
  · have hlow : ‖w₀‖ ≤ compLBound ⊤ (m + 1) L c * ‖u‖ :=
      hw₀_norm.trans (mul_le_mul_of_nonneg_left (norm_lowerOrder_le (m + 1) u)
        (compLBound_nonneg ⊤ (m + 1) L h.pos))
    have hcb : compLBound ⊤ (m + 2) L c = compLBound ⊤ (m + 1) L c + M := by
      simp [compLBound, M, Finset.sum_range_succ]
    have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient (m + 1) w
    simp only [w, lowerOrder_mk, iteratedGradient_mk] at hle
    rw [hcb, add_mul]
    linarith

private theorem exists_comp_top :
    ∀ (k : ℕ) {U V : Opens E} {L c : ℝ}, IsChangeOfVariables k U V Φ L c →
      ∀ u : Wkp mu V ⊤ k,
      ∃ w : Wkp mu U ⊤ k,
        (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
        ‖w‖ ≤ compLBound ⊤ k L c * ‖u‖
  | 0, _, _, _, _, h, u =>
      ⟨compLp h u, by rw [value_zero, value_zero]; exact compLp_ae h u, by
        simpa [compLBound, Fintype.card_unique] using norm_compLp_le h u⟩
  | 1, _, _, _, _, h, u =>
      let ⟨w, hw, _, hn⟩ := exists_comp_top_one h u
      ⟨w, hw, hn⟩
  | m + 2, _, _, _, _, h, u => by
      obtain ⟨w₀, hw₀, hw₀n⟩ := exists_comp_top (m + 1) (h.mono (Nat.le_succ (m + 1)))
        (lowerOrder (m + 1) u)
      obtain ⟨w, hw, _, hn⟩ := exists_comp_top_succ_succ h u w₀ hw₀ hw₀n
      exact ⟨w, hw, hn⟩

private theorem exists_comp (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ∃ w : Wkp mu U p k,
      (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
      ‖w‖ ≤ compLBound p k L c * ‖u‖ := by
  by_cases hp : p = ⊤
  · subst hp
    exact exists_comp_top k h u
  · exact ⟨compLFinite h hp u, value_compLFinite_ae h hp u, norm_compLFinite_le h hp u⟩

private def compFun (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) : Wkp mu U p k :=
  (exists_comp h u).choose

private theorem value_compFun_ae (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    (value k (compFun h u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  (exists_comp h u).choose_spec.1

private theorem value_compFun (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    value k (compFun h u) = compLp h (value k u) :=
  Lp.ext ((value_compFun_ae h u).trans (compLp_ae h (value k u)).symm)

private theorem norm_compFun_le (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ‖compFun h u‖ ≤ compLBound p k L c * ‖u‖ :=
  (exists_comp h u).choose_spec.2

/-- **Change of variables in `W^{k,p}`.** If `Φ` is a change of variables of order `k` from `U`
into `V` (`TauCeti.Wkp.IsChangeOfVariables`) and `1 ≤ p ≤ ∞`, then precomposition with `Φ` is a
bounded linear operator `W^{k,p}(V) →L[ℝ] W^{k,p}(U)`. Its value is `u ∘ Φ`
(`TauCeti.Wkp.value_compL_ae`), which characterizes it (`TauCeti.Wkp.compL_eq_iff`). -/
def compL (h : IsChangeOfVariables k U V Φ L c) :
    Wkp mu V p k →L[ℝ] Wkp mu U p k :=
  LinearMap.mkContinuous
    { toFun := compFun h
      map_add' := fun u v => ext k (by simp only [value_add, value_compFun, map_add])
      map_smul' := fun a u => ext k (by
        simp only [value_smul, value_compFun, map_smul, RingHom.id_apply]) }
    (compLBound p k L c) (norm_compFun_le h)

/-- The value of `compL h u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem value_compL_ae (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    (value k (compL h u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  value_compFun_ae h u

/-- An element of `W^{k,p}(U)` is `compL h u` exactly when its value is `u ∘ Φ` almost everywhere
on `U`. -/
theorem compL_eq_iff (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k)
    (w : Wkp mu U p k) :
    compL h u = w ↔ (value k w : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  ⟨fun hw => hw ▸ value_compL_ae h u,
    fun hw => ext k (Lp.ext ((value_compL_ae h u).trans hw.symm))⟩

/-- `compL h` increases norms by at most the factor `compLBound p k L c`. -/
theorem norm_compL_le (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ‖compL h u‖ ≤ compLBound p k L c * ‖u‖ :=
  norm_compFun_le h u

/-- `compL h` has operator norm at most `compLBound p k L c`. -/
theorem opNorm_compL_le (h : IsChangeOfVariables k U V Φ L c) :
    ‖(compL h : Wkp mu V p k →L[ℝ] Wkp mu U p k)‖ ≤ compLBound p k L c :=
  LinearMap.mkContinuous_norm_le _ (compLBound_nonneg p k L h.pos) (norm_compFun_le h)

/-- The `Lᵖ(U)` norm of the highest weak derivative of `compL h u` is bounded by
`max 1 L ^ (k + 1) · #{ordered partitions of k + 1} · c ^ (-1/p) · ‖u‖`, for every `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compL_le (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    ‖iteratedGradient k (compL h u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
  by_cases hp : p = ⊤
  · subst hp
    cases k with
    | zero =>
        obtain ⟨w, hw, hg, -⟩ := exists_comp_top_one h u
        rw [(compL_eq_iff h u w).2 hw]
        simpa [Fintype.card_unique] using hg
    | succ m =>
        obtain ⟨w₀, hw₀, hw₀n⟩ := exists_comp_top (m + 1) (h.mono (Nat.le_succ (m + 1)))
          (lowerOrder (m + 1) u)
        obtain ⟨w, hw, hg, -⟩ := exists_comp_top_succ_succ h u w₀ hw₀ hw₀n
        rw [(compL_eq_iff h u w).2 hw]
        simpa using hg
  · have heq : compL h u = compLFinite h hp u :=
      (compL_eq_iff h u _).2 (value_compLFinite_ae h hp u)
    rw [heq]
    exact norm_iteratedGradient_compLFinite_le h hp u

end Extension

/-! ### Compatibility -/

section Compatibility

/-- Precomposition with the identity is the identity of `W^{k,p}(U)`. -/
@[simp]
theorem compL_id (h : IsChangeOfVariables k U U _root_.id L c) (u : Wkp mu U p k) :
    compL h u = u :=
  (compL_eq_iff h u u).2 Filter.EventuallyEq.rfl

/-- Precomposition commutes with forgetting the highest weak derivative.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    lowerOrder k (compL h u) = compL (h.mono k.le_succ) (lowerOrder k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_compL_ae h u] with x hx
  rw [← value_succ, hx, value_succ]

/-- Precomposition commutes with restriction to open subdomains. -/
theorem restrictL_compL {U' V' : Opens E} (h : IsChangeOfVariables k U V Φ L c)
    (hU : U' ≤ U) (hV : V' ≤ V) (hUV : MapsTo Φ U' V') (u : Wkp mu V p k) :
    restrictL hU k (compL h u) = compL (h.restrict hU hUV) (restrictL hV k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_restrictL_ae hU k (compL h u),
    ae_restrict_of_ae_restrict_of_subset hU (value_compL_ae h u),
    (h.restrict hU hUV).ae_comp (value_restrictL_ae hV k u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- Precomposition commutes with lowering the integrability exponent on finite-measure domains. -/
theorem ofExponentLEL_compL {q : ℝ≥0∞} [Fact (1 ≤ q)]
    [IsFiniteMeasure (mu.restrict (U : Set E))] [IsFiniteMeasure (mu.restrict (V : Set E))]
    (h : IsChangeOfVariables k U V Φ L c) (hpq : p ≤ q) (u : Wkp mu V q k) :
    ofExponentLEL hpq k (compL h u) = compL h (ofExponentLEL hpq k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_ofExponentLEL_ae hpq k (compL h u), value_compL_ae h u,
    h.ae_comp (value_ofExponentLEL_ae hpq k u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **First-order chain rule in `W^{k+1,p}` for `1 ≤ p ≤ ∞`.** The weak gradient of the
first-order part of `compL h u` is `DΦ(x)* (∇u(Φ x))` almost everywhere on `U`. -/
theorem gradient_firstOrder_compL_ae (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    W1p.gradient (firstOrder k (compL h u)) =ᵐ[mu.restrict U]
      fun x => (fderiv ℝ Φ x).adjoint (W1p.gradient (firstOrder k u) (Φ x)) := by
  have hc1 : ContDiffOn ℝ 1 Φ U := h.contDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  have h1 := (W1p.hasWeakFDerivOn (firstOrder k u)).comp_contDiffOn_diffeo hc1 h.injOn
    (fun x hx => abs_ne_zero.1 (h.pos.trans_le (h.le_abs_det x hx)).ne') h.mapsTo
  have heq : (W1p.value (firstOrder k (compL h u)) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => W1p.value (firstOrder k u) (Φ x) := by
    simp only [value_firstOrder]
    exact value_compL_ae h u
  have h2 := (W1p.hasWeakFDerivOn (firstOrder k (compL h u))).congr_ae heq
  filter_upwards [h2.ae_eq h1] with x hx
  refine ext_inner_right ℝ fun v => ?_
  have hxv := DFunLike.congr_fun hx v
  simpa only [innerSL_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] using hxv

/-- **The chain rule at finite exponent.** For `1 ≤ p < ∞`, the first-order part of `compL h u`
is the first-order change of variables `TauCeti.W1p.compL` of the first-order part of `u`.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem firstOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p (k + 1)) :
    firstOrder k (compL h u) =
      W1p.compL Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det
        (firstOrder k u) := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_compL_ae h u, W1p.value_compL_ae Φ hp h.differentiableOn h.injOn
    h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det (firstOrder k u)] with x h1 h2
  rw [h2, value_firstOrder, value_firstOrder, h1]

/-- **Functoriality.** Precomposing with `Φ` and then with `Ψ` is precomposing with `Φ ∘ Ψ`. -/
theorem compL_comp (hΦ : IsChangeOfVariables k V W Φ L c)
    (hΨ : IsChangeOfVariables k U V Ψ L' c') {L'' c'' : ℝ}
    (hΦΨ : IsChangeOfVariables k U W (Φ ∘ Ψ) L'' c'') (u : Wkp mu W p k) :
    compL hΨ (compL hΦ u) = compL hΦΨ u := by
  refine (compL_eq_iff _ _ _).2 ?_
  filter_upwards [value_compL_ae hΦΨ u, hΨ.ae_comp (value_compL_ae hΦ u)] with x h1 h2
  rw [h1, h2, Function.comp_apply]

end Compatibility

/-! ### Diffeomorphism invariance -/

section Equiv

/-- If `Ψ` maps `V` back to `U` inverse to `Φ`, precomposing with `Φ` and then with `Ψ` is the
identity of `W^{k,p}(V)`. -/
theorem compL_compL_of_rightInvOn (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (u : Wkp mu V p k) :
    compL hΨ (compL hΦ u) = u := by
  refine (compL_eq_iff _ _ _).2 ?_
  filter_upwards [hΨ.ae_comp (value_compL_ae hΦ u), ae_restrict_mem V.isOpen.measurableSet]
    with y hy hyV
  rw [hy, hΦΨ hyV]

/-- **Diffeomorphism invariance of `W^{k,p}`.** If `Φ` is a change of variables of order `k` from
`U` into `V` and `Ψ` one from `V` into `U` with `Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`, then
for `1 ≤ p ≤ ∞` precomposition with `Φ` is an isomorphism of Banach spaces
`W^{k,p}(V) ≃L[ℝ] W^{k,p}(U)`, with inverse precomposition with `Ψ`. -/
def compLEquiv (hΦ : IsChangeOfVariables k U V Φ L c) (hΨ : IsChangeOfVariables k V U Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) :
    Wkp mu V p k ≃L[ℝ] Wkp mu U p k :=
  ContinuousLinearEquiv.equivOfInverse (compL hΦ) (compL hΨ)
    (compL_compL_of_rightInvOn hΦ hΨ hΦΨ) (compL_compL_of_rightInvOn hΨ hΦ hΨΦ)

@[simp]
theorem compLEquiv_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (u : Wkp mu V p k) :
    compLEquiv hΦ hΨ hΦΨ hΨΦ u = compL hΦ u :=
  (rfl)

@[simp]
theorem compLEquiv_symm_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (u : Wkp mu U p k) :
    (compLEquiv hΦ hΨ hΦΨ hΨΦ).symm u = compL hΨ u :=
  (rfl)

end Equiv

/-! ### Left-invertible `Cᵏ` maps and uniform norm bounds -/

section LeftInvOn

private theorem map_measurableExtension_le_of_leftInvOn (hΦ : ContinuousOn Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    (mu.restrict U).map (measurableExtension Φ U) ≤
      ENNReal.ofReal (max 1 L' ^ Module.finrank ℝ E) • mu.restrict V := by
  rw [Measure.map_congr measurableExtension_ae_eq]
  exact map_restrict_le_smul_restrict_of_norm_fderiv_le mu
    (hΦ.aemeasurable U.isOpen.measurableSet) V.isOpen hΨ hmaps hΨΦ fun x hx =>
      (hL' x hx).trans (le_max_right 1 L')

/-- **Precomposition with a left-invertible `Cᵏ` map.** For any order `k : ℕ` and exponent
`1 ≤ p ≤ ∞`, if `Φ` is `Cᵏ` on `U` mapping `U` into `V` with derivatives of orders `1` through
`k` bounded by `L` on `U`, and `Ψ` is differentiable on `V` with `Ψ (Φ x) = x` and
`‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, then precomposition with `Φ` is a bounded linear operator
`W^{k,p}(V) →L[ℝ] W^{k,p}(U)`. At `k = 0` no differentiability of `Φ` is assumed (`C⁰` is
continuity on `U`), while for `k ≥ 1` it agrees with `compL` (`compOfLeftInvOnL_eq_compL`). -/
def compOfLeftInvOnL : ∀ {k : ℕ}, ContDiffOn ℝ k Φ U → DifferentiableOn ℝ Ψ V →
    MapsTo Φ U V → LeftInvOn Ψ Φ U →
    (∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
    (∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') → Wkp mu V p k →L[ℝ] Wkp mu U p k
  | 0, hΦ, hΨ, hmaps, hΨΦ, _, hL' =>
      Lp.compOfMapLeSmul ℝ (measurable_measurableExtension_of_continuousOn hΦ.continuousOn)
        ENNReal.ofReal_ne_top
        (map_measurableExtension_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL')
  | k + 1, hΦ, hΨ, hmaps, hΨΦ, hL, hL' =>
      compL (IsChangeOfVariables.of_leftInvOn k.succ_pos hΦ hΨ hmaps hΨΦ hL hL')

/-- For `k ≥ 1`, `compOfLeftInvOnL` agrees with `compL` applied to
`IsChangeOfVariables.of_leftInvOn`. -/
theorem compOfLeftInvOnL_eq_compL (hk : 1 ≤ k) (hΦ : ContDiffOn ℝ k Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    compOfLeftInvOnL (mu := mu) (p := p) hΦ hΨ hmaps hΨΦ hL hL' =
      compL (IsChangeOfVariables.of_leftInvOn hk hΦ hΨ hmaps hΨΦ hL hL') := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk; rfl

/-- The value of `compOfLeftInvOnL` is `u ∘ Φ` almost everywhere on `U`. -/
theorem value_compOfLeftInvOnL_ae (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) :
    (value k (compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value k u (Φ x) := by
  cases k with
  | zero =>
      filter_upwards [Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ)
          (measurable_measurableExtension_of_continuousOn hΦ.continuousOn) ENNReal.ofReal_ne_top
          (map_measurableExtension_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL') u,
        measurableExtension_ae_eq (mu := mu) (Φ := Φ) (U := U)] with x hx hx'
      simpa only [compOfLeftInvOnL, value_zero, Function.comp_apply, hx'] using hx
  | succ m =>
      exact value_compL_ae (IsChangeOfVariables.of_leftInvOn m.succ_pos hΦ hΨ hmaps hΨΦ hL hL') u

/-- An element of `W^{k,p}(U)` is `compOfLeftInvOnL ... u` if and only if its value agrees with
`u ∘ Φ` almost everywhere on `U`. -/
theorem compOfLeftInvOnL_eq_iff (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) (w : Wkp mu U p k) :
    compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u = w ↔
      (value k w : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  ⟨fun hw => hw ▸ value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u,
    fun hw => ext k (Lp.ext ((value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u).trans hw.symm))⟩

/-- `compOfLeftInvOnL` increases norms by at most
`compLBound p k L (max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem norm_compOfLeftInvOnL_le (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) :
    ‖compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u‖ ≤
      compLBound p k L (max 1 L' ^ Module.finrank ℝ E)⁻¹ * ‖u‖ := by
  cases k with
  | zero =>
      have hM : 0 ≤ max 1 L' ^ Module.finrank ℝ E :=
        pow_nonneg (zero_le_one.trans (le_max_left 1 L')) _
      refine (Lp.norm_compOfMapLeSmul_le
        (measurable_measurableExtension_of_continuousOn hΦ.continuousOn) ENNReal.ofReal_ne_top
        (map_measurableExtension_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL') u).trans
        (le_of_eq ?_)
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM]
      simp [compLBound, Fintype.card_unique]
  | succ m =>
      exact norm_compL_le (IsChangeOfVariables.of_leftInvOn m.succ_pos hΦ hΨ hmaps hΨΦ hL hL') u

/-- The operator norm of `compOfLeftInvOnL` is bounded by
`compLBound p k L (max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem opNorm_compOfLeftInvOnL_le (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    ‖compOfLeftInvOnL (mu := mu) (p := p) hΦ hΨ hmaps hΨΦ hL hL'‖ ≤
      compLBound p k L (max 1 L' ^ Module.finrank ℝ E)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _
    (compLBound_nonneg p k L (inv_pos.2 (pow_pos (zero_lt_one.trans_le (le_max_left 1 L')) _)))
    (norm_compOfLeftInvOnL_le hΦ hΨ hmaps hΨΦ hL hL')

end LeftInvOn

end Calculus

private theorem compLBound_pos (k : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) : 0 < compLBound 1 k L c := by
  unfold compLBound
  refine mul_pos (Real.rpow_pos_of_pos (inv_pos.2 hc) _) (Finset.sum_pos' (fun _ _ => ?_)
    ⟨0, Finset.mem_range.2 k.succ_pos, by simp [Fintype.card_unique]⟩)
  have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _); positivity

private theorem compLBound_le_compLBound_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) (L : ℝ) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) : compLBound p k L c ≤ compLBound 1 k L c := by
  unfold compLBound
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by
    have : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _); positivity)
  have hp1 : (1 / p).toReal ≤ (1 / (1 : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono (by simp)
      (by simpa only [div_one] using ENNReal.div_le_of_le_mul (by simpa using (Fact.out : 1 ≤ p)))
  exact Real.rpow_le_rpow_of_exponent_le (one_le_inv₀ hc0 |>.2 hc1) hp1

/-- **Uniform `W^{k,p}` precomposition bound for left-invertible `Cᵏ` maps.** There is a positive
constant `C`, depending only on the dimension of `E`, the order `k`, and the derivative bounds `L`
and `L'`, such that for every additive Haar measure `mu`, every exponent `1 ≤ p ≤ ∞`, open sets
`U, V ⊆ E`, `Cᵏ` map `Φ : E → E` on `U` mapping `U` into `V` with derivatives of orders `1`
through `k` bounded by `L` on `U`, and differentiable left inverse `Ψ` on `V` satisfying
`‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, precomposition with `Φ` carries each `u ∈ W^{k,p}(V)` to an
element `w ∈ W^{k,p}(U)` of norm at most `C * ‖u‖` whose value agrees with `u ∘ Φ` almost
everywhere on `U`. -/
theorem exists_norm_comp_le (E : Type*) [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] (k : ℕ) (L L' : ℝ) :
    ∃ C > 0, ∀ (mu : Measure E) [mu.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
      {U V : Opens E} {Φ Ψ : E → E},
      ContDiffOn ℝ k Φ U → DifferentiableOn ℝ Ψ V → MapsTo Φ U V → LeftInvOn Ψ Φ U →
      (∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
      (∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') →
      ∀ u : Wkp mu V p k, ∃ w : Wkp mu U p k,
        (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧ ‖w‖ ≤ C * ‖u‖ := by
  set c : ℝ := (max 1 L' ^ Module.finrank ℝ E)⁻¹
  have hc0 : 0 < c := inv_pos.2 (pow_pos (zero_lt_one.trans_le (le_max_left 1 L')) _)
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left 1 L'))
  refine ⟨compLBound 1 k L c, compLBound_pos k L hc0,
    fun mu _ p _ {U V Φ Ψ} hΦ hΨ hmaps hΨΦ hL hL' u =>
      ⟨compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u,
        value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u,
        (norm_compOfLeftInvOnL_le hΦ hΨ hmaps hΨΦ hL hL' u).trans
          (mul_le_mul_of_nonneg_right (compLBound_le_compLBound_one p k L hc0 hc1)
            (norm_nonneg u))⟩⟩

end TauCeti.Wkp
