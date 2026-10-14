/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.OfLipschitz
-- Private: parametric integrals and the chain rule are used only inside proofs.
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The variational equation of a flow

Let `v` be a globally Lipschitz, continuously differentiable vector field on a Banach space and
`φ` its flow (`TauCeti.flowOfLipschitz`). The derivative `Dφₜ(x)` of the time-`t` map at `x`
describes how a perturbation of the initial condition `x` evolves along the orbit of `x`. It is
the solution of the linear equation

`Dφₜ(x) = id + ∫₀ᵗ Dv(φ_τ x) ∘ Dφ_τ(x) dτ`,

equivalently `d/dt Dφₜ(x) = Dv(φₜ x) ∘ Dφₜ(x)`, with `Dφ₀(x) = id`. This is the equation used to
compute the first-order dependence of the flow on parameters of the vector field.

## Main results

* `TauCeti.differentiable_flowOfLipschitz_apply`: the time-`t` map is differentiable.
* `TauCeti.fderiv_flowOfLipschitz_eq_id_add_integral`: the integral form.
* `TauCeti.hasDerivAt_fderiv_flowOfLipschitz`: the differential form.
* `TauCeti.hasDerivAt_fderiv_flowOfLipschitz_apply`: the differential form applied to a vector.
* `TauCeti.fderiv_flow_add`, `TauCeti.fderiv_flow_neg_comp`, `TauCeti.fderiv_flow_comp_neg`,
  `TauCeti.fderivFlowUnit`, `TauCeti.ringInverse_fderiv_flow`: for a flow whose time maps are
  differentiable at the relevant points, `Dϕ_{s+t}(x) = Dϕ_s(ϕ_t x) ∘ Dϕ_t(x)`, and `Dϕ_t(x)` is
  invertible with inverse `Dϕ_{-t}(ϕ_t x)`.
* `TauCeti.fderiv_flow_apply_of_hasDerivAt`: the derivative of a flow carries its velocity field
  along.
* `TauCeti.continuous_fderiv_flowOfLipschitz`, `TauCeti.continuous_fderiv_flowOfLipschitz_neg`:
  for a `C¹` field, `τ ↦ Dφ_τ(x)` and its inverse `σ ↦ Dφ_{-σ}(φ_σ x)` are continuous.
-/

public section

open Set Filter Topology intervalIntegral MeasureTheory
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

section Smooth

variable (hv : LipschitzWith K v) (hvs : ContDiff ℝ 1 v)
include hv hvs

private theorem contDiff_uncurry_flowOfLipschitz :
    ContDiff ℝ 1 (Function.uncurry (flowOfLipschitz v hv)) := by
  simpa using contDiff_flowOfLipschitz 0 v hv (by simpa using hvs)

/-- The time-`t` map of the flow of a Lipschitz `C¹` vector field is differentiable. -/
theorem differentiable_flowOfLipschitz_apply (t : ℝ) :
    Differentiable ℝ (flowOfLipschitz v hv t) :=
  (contDiff_flowOfLipschitz_apply 0 v hv (by simpa using hvs) t).differentiable
    (by norm_num)

/-- The derivative of the time-`τ` map at a fixed point is continuous in `τ`. -/
theorem continuous_fderiv_flowOfLipschitz (x : E) :
    Continuous fun τ : ℝ ↦ fderiv ℝ (flowOfLipschitz v hv τ) x :=
  Continuous.fderiv_one (contDiff_uncurry_flowOfLipschitz hv hvs) continuous_const

/-- The integrand of the variational equation is continuous in time. -/
private theorem continuous_variational_integrand (x : E) :
    Continuous fun τ : ℝ ↦
      (fderiv ℝ v (flowOfLipschitz v hv τ x)).comp (fderiv ℝ (flowOfLipschitz v hv τ) x) := by
  exact ((hvs.continuous_fderiv one_ne_zero).comp
    ((flowOfLipschitz v hv).continuous continuous_id continuous_const)).clm_comp
    (continuous_fderiv_flowOfLipschitz hv hvs x)

/-- **The variational equation, integral form.** For a globally Lipschitz `C¹` vector field, the
derivative of the time-`t` map of its flow at `x` is
`id + ∫₀ᵗ Dv(φ_τ x) ∘ Dφ_τ(x) dτ`. -/
theorem fderiv_flowOfLipschitz_eq_id_add_integral (x : E) (t : ℝ) :
    fderiv ℝ (flowOfLipschitz v hv t) x = ContinuousLinearMap.id ℝ E +
      ∫ τ in (0 : ℝ)..t,
        (fderiv ℝ v (flowOfLipschitz v hv τ x)).comp (fderiv ℝ (flowOfLipschitz v hv τ) x) := by
  have hdiff := differentiable_flowOfLipschitz_apply hv hvs
  have hI : HasFDerivAt (fun y ↦ ∫ τ in (0 : ℝ)..t, v (flowOfLipschitz v hv τ y))
      (∫ τ in (0 : ℝ)..t, (fderiv ℝ v (flowOfLipschitz v hv τ x)).comp
        (fderiv ℝ (flowOfLipschitz v hv τ) x)) x := by
    have hcont : ∀ y : E, Continuous fun τ : ℝ ↦ v (flowOfLipschitz v hv τ y) := fun y ↦
      hv.continuous.comp
        ((flowOfLipschitz v hv).continuous continuous_id continuous_const)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (F := fun y τ ↦ v (flowOfLipschitz v hv τ y))
      (F' := fun y τ ↦ (fderiv ℝ v (flowOfLipschitz v hv τ y)).comp
        (fderiv ℝ (flowOfLipschitz v hv τ) y))
      (bound := fun _ ↦ K * Real.exp (K * |t|)) (s := univ) Filter.univ_mem
      (Eventually.of_forall fun y ↦ (hcont y).aestronglyMeasurable)
      ((hcont x).intervalIntegrable _ _)
      (continuous_variational_integrand hv hvs x).aestronglyMeasurable ?_
      intervalIntegrable_const ?_
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ y _ ↦ ?_
      have hτt : |τ| ≤ |t| := by
        have := Real.dist_le_of_mem_uIcc (Set.uIoc_subset_uIcc hτ) Set.left_mem_uIcc
        simpa [Real.dist_eq] using this
      calc _ ≤ ‖fderiv ℝ v (flowOfLipschitz v hv τ y)‖ * ‖fderiv ℝ (flowOfLipschitz v hv τ) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ K * Real.exp (K * |t|) := by
          refine mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hv) ?_ (norm_nonneg _) K.2
          exact (norm_fderiv_flowOfLipschitz_le hv y τ).trans
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτt K.2))
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun τ _ y _ ↦ ?_
      exact ((hvs.differentiable one_ne_zero _).hasFDerivAt.comp y (hdiff τ y).hasFDerivAt)
  have hφ : flowOfLipschitz v hv t = fun y ↦ y + ∫ τ in (0 : ℝ)..t, v (flowOfLipschitz v hv τ y) :=
    funext fun y ↦ flowOfLipschitz_eq_add_integral hv y t
  rw [hφ]
  exact ((hasFDerivAt_id x).add hI).fderiv

/-- **The variational equation, differential form.** For a globally Lipschitz `C¹` vector field,
`t ↦ Dφₜ(x)` is differentiable with derivative `Dv(φₜ x) ∘ Dφₜ(x)`. -/
theorem hasDerivAt_fderiv_flowOfLipschitz (x : E) (t : ℝ) :
    HasDerivAt (fun τ ↦ fderiv ℝ (flowOfLipschitz v hv τ) x)
      ((fderiv ℝ v (flowOfLipschitz v hv t x)).comp (fderiv ℝ (flowOfLipschitz v hv t) x)) t := by
  have h := ((continuous_variational_integrand hv hvs x).integral_hasStrictDerivAt 0 t).hasDerivAt
    |>.const_add (ContinuousLinearMap.id ℝ E)
  convert h using 1
  exact funext fun τ ↦ fderiv_flowOfLipschitz_eq_id_add_integral hv hvs x τ

/-- **The variational equation applied to a vector**: the derivative of the orbit of the
variation `Dφₜ(x) w` is `Dv(φₜ x) (Dφₜ(x) w)`. -/
theorem hasDerivAt_fderiv_flowOfLipschitz_apply (x w : E) (t : ℝ) :
    HasDerivAt (fun τ ↦ fderiv ℝ (flowOfLipschitz v hv τ) x w)
      (fderiv ℝ v (flowOfLipschitz v hv t x) (fderiv ℝ (flowOfLipschitz v hv t) x w)) t :=
  (hasDerivAt_fderiv_flowOfLipschitz hv hvs x t).clm_apply (hasDerivAt_const t w)
    |>.congr_deriv (by simp)

end Smooth

section Composition

variable {ϕ : Flow ℝ E} {s t : ℝ} {x : E}

omit [CompleteSpace E] in
/-- **The chain rule for the group law of a flow**: `Dϕ_{s+t}(x) = Dϕ_s(ϕ_t x) ∘ Dϕ_t(x)`. -/
theorem fderiv_flow_add (hs : DifferentiableAt ℝ (ϕ s) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    fderiv ℝ (ϕ (s + t)) x = (fderiv ℝ (ϕ s) (ϕ t x)).comp (fderiv ℝ (ϕ t) x) := by
  have e : ϕ (s + t) = ϕ s ∘ ϕ t := funext (ϕ.map_add s t)
  rw [e]
  exact fderiv_comp x hs ht

omit [CompleteSpace E] in
/-- The derivative of the time-`(-t)` map at `ϕ t x` is a left inverse of `Dϕ_t(x)`. -/
@[simp]
theorem fderiv_flow_neg_comp (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderiv ℝ (ϕ (-t)) (ϕ t x)).comp (fderiv ℝ (ϕ t) x) = ContinuousLinearMap.id ℝ E := by
  rw [← fderiv_flow_add hs ht, neg_add_cancel, Flow.map_zero, fderiv_id]

omit [CompleteSpace E] in
/-- The derivative of the time-`(-t)` map at `ϕ t x` is a right inverse of `Dϕ_t(x)`. -/
@[simp]
theorem fderiv_flow_comp_neg (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderiv ℝ (ϕ t) x).comp (fderiv ℝ (ϕ (-t)) (ϕ t x)) = ContinuousLinearMap.id ℝ E := by
  have hx : ϕ (-t) (ϕ t x) = x := by rw [← ϕ.map_add, neg_add_cancel, Flow.map_zero_apply]
  have := fderiv_flow_add (s := t) (t := -t) (x := ϕ t x) (by rw [hx]; exact ht) hs
  rw [add_neg_cancel, Flow.map_zero, fderiv_id, hx] at this
  exact this.symm

omit [CompleteSpace E] in
@[simp]
theorem fderiv_flow_neg_apply_fderiv_flow (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) (w : E) :
    fderiv ℝ (ϕ (-t)) (ϕ t x) (fderiv ℝ (ϕ t) x w) = w :=
  congrArg (· w) (fderiv_flow_neg_comp hs ht)

omit [CompleteSpace E] in
@[simp]
theorem fderiv_flow_apply_fderiv_flow_neg (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) (w : E) :
    fderiv ℝ (ϕ t) x (fderiv ℝ (ϕ (-t)) (ϕ t x) w) = w :=
  congrArg (· w) (fderiv_flow_comp_neg hs ht)

/-- **The derivative of a flow as a unit.** When the time-`t` map is differentiable at `x` and the
time-`(-t)` map at `ϕ t x`, the derivative `Dϕ_t(x)` is invertible, with inverse
`Dϕ_{-t}(ϕ_t x)`. -/
noncomputable def fderivFlowUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) : (E →L[ℝ] E)ˣ :=
  ⟨_, _, fderiv_flow_comp_neg hs ht, fderiv_flow_neg_comp hs ht⟩

omit [CompleteSpace E] in
@[simp]
theorem coe_fderivFlowUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderivFlowUnit hs ht : E →L[ℝ] E) = fderiv ℝ (ϕ t) x :=
  (rfl)

omit [CompleteSpace E] in
@[simp]
theorem coe_inv_fderivFlowUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    ((fderivFlowUnit hs ht)⁻¹ : (E →L[ℝ] E)ˣ) = fderiv ℝ (ϕ (-t)) (ϕ t x) :=
  (rfl)

omit [CompleteSpace E] in
/-- **The inverse of the derivative of a flow** is the derivative of the reverse time map. -/
@[simp]
theorem ringInverse_fderiv_flow (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    Ring.inverse (fderiv ℝ (ϕ t) x) = fderiv ℝ (ϕ (-t)) (ϕ t x) :=
  Ring.inverse_unit (fderivFlowUnit hs ht)

omit [CompleteSpace E] in
/-- **The derivative of a flow carries its velocity field along**: if the orbits of `x` and of
`ϕ t x` have velocities `a` and `b` at time `0`, then `Dϕ_t(x) a = b`. -/
theorem fderiv_flow_apply_of_hasDerivAt {a b : E} (hx : HasDerivAt (fun s ↦ ϕ s x) a 0)
    (hy : HasDerivAt (fun s ↦ ϕ s (ϕ t x)) b 0) (ht : DifferentiableAt ℝ (ϕ t) x) :
    fderiv ℝ (ϕ t) x a = b := by
  have h1 : HasDerivAt (fun s ↦ ϕ t (ϕ s x)) (fderiv ℝ (ϕ t) x a) 0 :=
    ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 hx (Flow.map_zero_apply ϕ x).symm
  have h2 : (fun s ↦ ϕ t (ϕ s x)) = fun s ↦ ϕ s (ϕ t x) :=
    funext fun s ↦ by rw [← ϕ.map_add, ← ϕ.map_add, add_comm]
  rw [h2] at h1
  exact h1.unique hy

end Composition

section Inverse

variable (hv : LipschitzWith K v) (hvs : ContDiff ℝ 1 v)

include hvs

/-- **The inverse derivative along an orbit is continuous**: for a globally Lipschitz `C¹` field,
`σ ↦ Dφ_{-σ}(φ_σ x)`, the inverse of `Dφ_σ(x)`, is continuous. -/
theorem continuous_fderiv_flowOfLipschitz_neg (x : E) :
    Continuous fun σ ↦ fderiv ℝ (flowOfLipschitz v hv (-σ)) (flowOfLipschitz v hv σ x) := by
  have hd := differentiable_flowOfLipschitz_apply hv hvs
  have hinv : ∀ σ, Ring.inverse (fderiv ℝ (flowOfLipschitz v hv σ) x) =
      fderiv ℝ (flowOfLipschitz v hv (-σ)) (flowOfLipschitz v hv σ x) := fun σ ↦
    ringInverse_fderiv_flow (hd _ _) (hd σ x)
  simp_rw [← hinv]
  refine continuous_iff_continuousAt.2 fun σ ↦ ?_
  have hU := NormedRing.inverse_continuousAt (fderivFlowUnit (hd (-σ) _) (hd σ x))
  rw [coe_fderivFlowUnit] at hU
  exact hU.comp_of_eq (continuous_fderiv_flowOfLipschitz hv hvs x).continuousAt rfl

end Inverse

end TauCeti
