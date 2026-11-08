/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
public import TauCeti.Dynamics.Flow.OfLipschitz
public import TauCeti.Dynamics.Flow.TimeDependent
-- Private: parametric integrals, the chain rule and the local-inverse derivative are used only
-- inside proofs.
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
* `Flow.fderiv_add`, `Flow.fderiv_neg_comp`, `Flow.fderiv_comp_neg`,
  `Flow.fderivUnit`, `Flow.ringInverse_fderiv`: for a flow whose time maps are
  differentiable at the relevant points, `Dϕ_{s+t}(x) = Dϕ_s(ϕ_t x) ∘ Dϕ_t(x)`, and `Dϕ_t(x)` is
  invertible with inverse `Dϕ_{-t}(ϕ_t x)`.
* `Flow.fderiv_apply_of_hasDerivAt`: the derivative of a flow carries its velocity field
  along.
* `TauCeti.continuous_fderiv_flowOfLipschitz`, `TauCeti.continuous_fderiv_flowOfLipschitz_neg`:
  for a `C¹` field, `τ ↦ Dφ_τ(x)` and its inverse `σ ↦ Dφ_{-σ}(φ_σ x)` are continuous.
* `TauCeti.contDiff_timeDependentFlow` and `TauCeti.hasDerivAt_fderiv_timeDependentFlow`: the
  time-dependent flow `φ(s, t)` of a jointly `C^(n+1)` field (`TauCeti.timeDependentFlow`) is
  `C^(n+1)` in `(s, t, x)`, and `∂ₜ Dφ(s, t)(x) = Dvₜ(φ(s, t) x) ∘ Dφ(s, t)(x)`.
* `TauCeti.differentiable_timeDependentFlow` and
  `TauCeti.fderiv_timeDependentFlow_eq_dysonSeriesLeft`: consequently `Dφ(s, t)(x)` exists and is
  the propagator `TauCeti.dysonSeriesLeft` of the linearized equation `ξ' = Dv_r(φ(s, r) x) ξ`
  along the orbit of `x`, from time `s` to time `t`.
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


end TauCeti

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ϕ : Flow ℝ E} {s t : ℝ} {x : E}

/-- **The chain rule for the group law of a flow**: `Dϕ_{s+t}(x) = Dϕ_s(ϕ_t x) ∘ Dϕ_t(x)`. -/
theorem fderiv_add (hs : DifferentiableAt ℝ (ϕ s) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    fderiv ℝ (ϕ (s + t)) x = (fderiv ℝ (ϕ s) (ϕ t x)).comp (fderiv ℝ (ϕ t) x) := by
  have e : ϕ (s + t) = ϕ s ∘ ϕ t := funext (ϕ.map_add s t)
  rw [e]
  exact fderiv_comp x hs ht

/-- The derivative of the time-`(-t)` map at `ϕ t x` is a left inverse of `Dϕ_t(x)`. -/
@[simp]
theorem fderiv_neg_comp (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderiv ℝ (ϕ (-t)) (ϕ t x)).comp (fderiv ℝ (ϕ t) x) = ContinuousLinearMap.id ℝ E := by
  rw [← Flow.fderiv_add hs ht, neg_add_cancel, Flow.map_zero, fderiv_id]

/-- The derivative of the time-`(-t)` map at `ϕ t x` is a right inverse of `Dϕ_t(x)`. -/
@[simp]
theorem fderiv_comp_neg (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderiv ℝ (ϕ t) x).comp (fderiv ℝ (ϕ (-t)) (ϕ t x)) = ContinuousLinearMap.id ℝ E := by
  have hx : ϕ (-t) (ϕ t x) = x := by rw [← ϕ.map_add, neg_add_cancel, Flow.map_zero_apply]
  have := Flow.fderiv_add (s := t) (t := -t) (x := ϕ t x) (by rw [hx]; exact ht) hs
  rw [add_neg_cancel, Flow.map_zero, fderiv_id, hx] at this
  exact this.symm

/-- The derivative of a differentiable time map is invertible when the reverse time map is
differentiable at the image point. No completeness of the model space is needed. -/
theorem isInvertible_fderiv (ϕ : Flow ℝ E)
    (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x)) (ht : DifferentiableAt ℝ (ϕ t) x) :
    (fderiv ℝ (ϕ t) x).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse (ϕ.fderiv_comp_neg hs ht) (ϕ.fderiv_neg_comp hs ht)

/-- **The derivative of a flow as a unit.** When the time-`t` map is differentiable at `x` and the
time-`(-t)` map at `ϕ t x`, the derivative `Dϕ_t(x)` is invertible, with inverse
`Dϕ_{-t}(ϕ_t x)`. -/
noncomputable def fderivUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) : (E →L[ℝ] E)ˣ :=
  ⟨_, _, Flow.fderiv_comp_neg hs ht, Flow.fderiv_neg_comp hs ht⟩

/-- The unit `fderivUnit` is the derivative `Dϕ_t(x)`. -/
@[simp]
theorem coe_fderivUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    (Flow.fderivUnit hs ht : E →L[ℝ] E) = fderiv ℝ (ϕ t) x :=
  (rfl)

/-- The inverse of the unit `fderivUnit` is the derivative `Dϕ_{-t}(ϕ_t x)` of the reverse time
map. -/
@[simp]
theorem coe_inv_fderivUnit (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    ((Flow.fderivUnit hs ht)⁻¹ : (E →L[ℝ] E)ˣ) = fderiv ℝ (ϕ (-t)) (ϕ t x) :=
  (rfl)

/-- **The inverse of the derivative of a flow** is the derivative of the reverse time map. No
differentiability of the reverse time map is assumed: when `Dϕ_t(x)` is not invertible, the reverse
time map is not differentiable at `ϕ t x`, and both sides are `0`. -/
@[simp]
theorem ringInverse_fderiv (ht : DifferentiableAt ℝ (ϕ t) x) :
    Ring.inverse (fderiv ℝ (ϕ t) x) = fderiv ℝ (ϕ (-t)) (ϕ t x) := by
  have hx : ϕ (-t) (ϕ t x) = x := by rw [← ϕ.map_add, neg_add_cancel, Flow.map_zero_apply]
  by_cases hu : IsUnit (fderiv ℝ (ϕ t) x)
  · obtain ⟨u, hu⟩ := hu
    have hs : HasFDerivAt (ϕ (-t)) ((ContinuousLinearEquiv.unitsEquiv ℝ E u).symm : E →L[ℝ] E)
        (ϕ t x) := by
      refine HasFDerivAt.of_local_left_inverse (f := ϕ t)
        (f' := ContinuousLinearEquiv.unitsEquiv ℝ E u) ?_ ?_ ?_
      · exact (ϕ.continuous continuous_const continuous_id).continuousAt
      · rw [hx, show ((ContinuousLinearEquiv.unitsEquiv ℝ E u : E ≃L[ℝ] E) : E →L[ℝ] E) =
          fderiv ℝ (ϕ t) x from hu]
        exact ht.hasFDerivAt
      · exact Filter.Eventually.of_forall fun y ↦ by rw [← ϕ.map_add, add_neg_cancel,
          Flow.map_zero_apply]
    rw [hs.fderiv, ← hu]
    exact Ring.inverse_unit u ▸ rfl
  · rw [Ring.inverse_non_unit _ hu]
    by_cases hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x)
    · exact absurd ⟨Flow.fderivUnit hs ht, rfl⟩ hu
    · exact (fderiv_zero_of_not_differentiableAt hs).symm

/-- **The derivative of a flow carries its velocity field along**: if the orbits of `x` and of
`ϕ t x` have velocities `a` and `b` at time `0`, then `Dϕ_t(x) a = b`. -/
theorem fderiv_apply_of_hasDerivAt {a b : E} (hx : HasDerivAt (fun s ↦ ϕ s x) a 0)
    (hy : HasDerivAt (fun s ↦ ϕ s (ϕ t x)) b 0) (ht : DifferentiableAt ℝ (ϕ t) x) :
    fderiv ℝ (ϕ t) x a = b := by
  have h1 : HasDerivAt (fun s ↦ ϕ t (ϕ s x)) (fderiv ℝ (ϕ t) x a) 0 :=
    ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 hx (Flow.map_zero_apply ϕ x).symm
  have h2 : (fun s ↦ ϕ t (ϕ s x)) = fun s ↦ ϕ s (ϕ t x) :=
    funext fun s ↦ by rw [← ϕ.map_add, ← ϕ.map_add, add_comm]
  rw [h2] at h1
  exact h1.unique hy

end Flow

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

section Inverse

variable (hv : LipschitzWith K v) (hvs : ContDiff ℝ 1 v)

include hvs

/-- **The inverse derivative along an orbit is continuous**: for a globally Lipschitz `C¹` field,
`σ ↦ Dφ_{-σ}(φ_σ x)`, the inverse of `Dφ_σ(x)`, is continuous. -/
theorem continuous_fderiv_flowOfLipschitz_neg (x : E) :
    Continuous fun σ ↦ fderiv ℝ (flowOfLipschitz v hv (-σ)) (flowOfLipschitz v hv σ x) :=
  Continuous.fderiv_one (f := fun σ ↦ flowOfLipschitz v hv (-σ))
    ((contDiff_uncurry_flowOfLipschitz hv hvs).comp (contDiff_neg.prodMap contDiff_id))
    ((flowOfLipschitz v hv).continuous continuous_id continuous_const)

end Inverse

end TauCeti

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {K : ℝ≥0}

/-! ### Time-dependent flows

The time-dependent flow is the space component of the flow of the suspended autonomous field
`(t, x) ↦ (1, v t x)`, so its smoothness and its variational equation follow from those of
autonomous flows. -/

section TimeDependent

variable {v : ℝ → E → E} (hv : LipschitzWith K (timeDependentSuspension v))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem timeDependentSuspension_eq (v : ℝ → E → E) :
    timeDependentSuspension v = fun p ↦ (1, v p.1 p.2) :=
  funext fun p ↦ timeDependentSuspension_apply v p.1 p.2

/-- A time-dependent field which is jointly `C^(n+1)` has a `C^(n+1)` time-dependent flow,
jointly in the initial time, the final time and the initial point. -/
theorem contDiff_timeDependentFlow (n : ℕ)
    (hvs : ContDiff ℝ (n + 1) fun p : ℝ × E ↦ v p.1 p.2) :
    ContDiff ℝ (n + 1) fun p : (ℝ × ℝ) × E ↦ timeDependentFlow v hv p.1.1 p.1.2 p.2 := by
  have hS : ContDiff ℝ (n + 1) (timeDependentSuspension v) := by
    rw [timeDependentSuspension_eq]; exact contDiff_const.prodMk hvs
  have h := (contDiff_flowOfLipschitz n _ hv hS).comp
    (by fun_prop : ContDiff ℝ (n + 1) fun p : (ℝ × ℝ) × E ↦ (p.1.2 - p.1.1, (p.1.1, p.2)))
  convert contDiff_snd.comp h using 1
  funext p
  simp [globalSolution_timeDependentSuspension]

variable (hvs : ContDiff ℝ 1 fun p : ℝ × E ↦ v p.1 p.2)
include hvs

omit [CompleteSpace E] in
private theorem contDiff_timeDependentSuspension :
    ContDiff ℝ 1 (timeDependentSuspension v) := by
  rw [timeDependentSuspension_eq]; exact contDiff_const.prodMk hvs

/-- The derivative of the time-dependent flow in the initial point, through the flow of the
suspension. -/
private theorem hasFDerivAt_timeDependentFlow (s t : ℝ) (x : E) :
    HasFDerivAt (timeDependentFlow v hv s t)
      ((ContinuousLinearMap.snd ℝ ℝ E).comp
        ((fderiv ℝ (flowOfLipschitz _ hv (t - s)) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)))
      x := by
  have hΦ := (differentiable_flowOfLipschitz_apply hv (contDiff_timeDependentSuspension hvs)
    (t - s) (s, x)).hasFDerivAt
  have hι : HasFDerivAt (fun y : E ↦ (s, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x (hΦ.comp x hι)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  simp [globalSolution_timeDependentSuspension]

/-- The derivative of the flow of the suspension does not move the clock in the space
directions. -/
private theorem fst_fderiv_flowOfLipschitz_inr (s t : ℝ) (x w : E) :
    (fderiv ℝ (flowOfLipschitz _ hv (t - s)) (s, x) (0, w)).1 = 0 := by
  have hΦ := (differentiable_flowOfLipschitz_apply hv (contDiff_timeDependentSuspension hvs)
    (t - s) (s, x)).hasFDerivAt
  have hι : HasFDerivAt (fun y : E ↦ (s, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp x (hΦ.comp x hι)
  have hc : HasFDerivAt (fun y : E ↦ (flowOfLipschitz _ hv (t - s) (s, y)).1) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const t x).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
      simp [globalSolution_timeDependentSuspension])
  simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L w) (h.unique hc)

omit [CompleteSpace E] in
/-- The space derivative of the suspension in the space directions is the space derivative of
the time-dependent field. -/
private theorem snd_fderiv_timeDependentSuspension_inr (t : ℝ) (y w : E) :
    (fderiv ℝ (timeDependentSuspension v) (t, y) (0, w)).2 = fderiv ℝ (v t) y w := by
  have hV := (hvs.differentiable one_ne_zero (t, y)).hasFDerivAt
  have hS : HasFDerivAt (timeDependentSuspension v)
      ((0 : ℝ × E →L[ℝ] ℝ).prod (fderiv ℝ (fun p : ℝ × E ↦ v p.1 p.2) (t, y))) (t, y) := by
    rw [timeDependentSuspension_eq]
    exact (hasFDerivAt_const (1 : ℝ) _).prodMk hV
  have hι : HasFDerivAt (fun y : E ↦ (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have hv' : HasFDerivAt (v t) ((fderiv ℝ (fun p : ℝ × E ↦ v p.1 p.2) (t, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := hV.comp y hι
  rw [hS.fderiv, hv'.fderiv]
  simp

/-- **The variational equation of a time-dependent flow.** For a jointly `C¹` time-dependent
field whose suspension is globally Lipschitz, `u ↦ Dφ(s, u)(x)` is differentiable with derivative
`D(v t)(φ(s, t) x) ∘ Dφ(s, t)(x)` at `t`. -/
theorem hasDerivAt_fderiv_timeDependentFlow (s t : ℝ) (x : E) :
    HasDerivAt (fun u ↦ fderiv ℝ (timeDependentFlow v hv s u) x)
      ((fderiv ℝ (v t) (timeDependentFlow v hv s t x)).comp
        (fderiv ℝ (timeDependentFlow v hv s t) x)) t := by
  have h := (hasDerivAt_fderiv_flowOfLipschitz hv (contDiff_timeDependentSuspension hvs)
    (s, x) (t - s)).comp_sub_const t s
  have h' := (hasDerivAt_const t (ContinuousLinearMap.snd ℝ ℝ E)).clm_comp
    (h.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E)))
  refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u ↦
    (hasFDerivAt_timeDependentFlow hv hvs s u x).fderiv)).congr_deriv ?_
  rw [(hasFDerivAt_timeDependentFlow hv hvs s t x).fderiv]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_snd', zero_add, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, add_zero]
  rw [flowOfLipschitz_apply, globalSolution_timeDependentSuspension]
  conv_lhs => rw [← Prod.mk.eta (p := fderiv ℝ (flowOfLipschitz _ hv (t - s)) (s, x) (0, w)),
    fst_fderiv_flowOfLipschitz_inr hv hvs]
  exact snd_fderiv_timeDependentSuspension_inr hvs t _ _

/-- Each time map of the time-dependent flow of a jointly `C¹` field is differentiable. -/
theorem differentiable_timeDependentFlow (s t : ℝ) :
    Differentiable ℝ (timeDependentFlow v hv s t) :=
  fun x ↦ (hasFDerivAt_timeDependentFlow hv hvs s t x).differentiableAt

/-- **The derivative of a time-dependent flow is the propagator of the linearized equation.**
For a jointly `C¹` time-dependent field whose suspension is globally Lipschitz, the derivative
`Dφ(s, t)(x)` of the evolution from time `s` to time `t` is the propagator from `0` to `t - s`
of the linear equation `ξ' = M r ξ` with `M r = Dv_{s + r}(φ(s, s + r) x)`, the linearization of
the field along the orbit of `x`. -/
theorem fderiv_timeDependentFlow_eq_dysonSeriesLeft (s t : ℝ) (x : E) :
    fderiv ℝ (timeDependentFlow v hv s t) x =
      dysonSeriesLeft (fun r ↦ fderiv ℝ (v (s + r)) (timeDependentFlow v hv s (s + r) x))
        (t - s) := by
  have hM : Continuous fun r ↦ fderiv ℝ (v r) (timeDependentFlow v hv s r x) :=
    (hvs.fderiv (contDiff_zero.2 ((continuous_timeDependentFlow v hv).comp
      (by fun_prop : Continuous fun r : ℝ ↦ ((s, r), x)))) le_rfl).continuous
  have hf (r : ℝ) := (hasDerivAt_fderiv_timeDependentFlow hv hvs s (s + r) x).comp_const_add s r
  have h := eq_dysonSeriesLeft_mul (hM.comp (continuous_const.add continuous_id)) hf (t - s)
  have hself : timeDependentFlow v hv s s = id := funext (timeDependentFlow_self v hv s)
  simpa [hself, Function.comp_def, ContinuousLinearMap.mul_def] using h

end TimeDependent

end TauCeti
