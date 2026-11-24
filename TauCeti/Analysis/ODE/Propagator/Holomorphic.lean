/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator.Dyson
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Holomorphic dependence of the propagator on a parameter

Let `E` be a complex Banach space, `U ⊆ ℂ` open, and `P : ℂ → ℝ → E →L[ℂ] E` a family of
coefficients such that `P z` is integrable on `[a, b]` for every `z ∈ U`, `z ↦ P z r` is
holomorphic on `U` for almost every `r ∈ [a, b]`, and for every compact `K ⊆ U` there is an
integrable `m_K` on `[a, b]` such that, for almost every `r ∈ [a, b]`, `‖P z r‖ ≤ m_K r` for all
`z ∈ K` (the null set does not depend on `z`). Then for `s, t ∈ [a, b]` the propagator
`z ↦ N_{P z}(t, s)` is holomorphic on `U` (`TauCeti.differentiableOn_propagator`), hence
analytic (`TauCeti.analyticOnNhd_propagator`); an entire family of coefficients has entire
propagators (`TauCeti.differentiable_propagator`), for instance the affine family `z • A + B r`
(`TauCeti.differentiable_propagator_smul_add`).

Each Dyson term `D_{n+1}(t) = ∫ r in s..t, P z r ∘L D_n(r)` is a parametric integral of an
integrand holomorphic in `z` and dominated on compact sets, hence holomorphic in `z`
(`TauCeti.differentiableOn_propagatorDysonTerm`), and on a compact set `K` the terms are bounded
by `|∫ r in s..t, m_K r| ^ n / n!` (`TauCeti.norm_propagatorDysonTerm_le_of_norm_le`), so the
Dyson series converges locally uniformly in `z`.

The bound `‖N_{P z}(t, s)‖ ≤ exp |∫ r in s..t, m_K r|` for `z ∈ K` is
`TauCeti.norm_propagator_le_of_norm_le`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped Nat Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {P : ℂ → ℝ → E →L[ℂ] E} {U : Set ℂ} {a b s t : ℝ}

/-- **The Dyson terms are holomorphic in the parameter.** Under the hypotheses of
`TauCeti.differentiableOn_propagator`, for `s, t ∈ [a, b]` and every `n`, the `n`-th Dyson term
`z ↦ Dₙ(t)` of `P z` based at `s` is complex differentiable on `U`. -/
theorem differentiableOn_propagatorDysonTerm (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (n : ℕ) (ht : t ∈ Icc a b) :
    DifferentiableOn ℂ (fun z ↦ propagatorDysonTerm (P z) s n t) U := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    intro z hz
    obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz)
    obtain ⟨m, hmi, hPm⟩ := hm _ hεU (isCompact_closedBall z ε)
    have hVU : ball z ε ⊆ U := ball_subset_closedBall.trans hεU
    have hst : Ι s t ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
    set c := (∫ r in a..b, ‖m r‖) ^ n / (n ! : ℝ)
    -- `Dₙ₊₁(t) = ±∫ r in Ι s t, P w r ∘L Dₙ(r)`, an integral of an integrand holomorphic in `w`
    -- and dominated by `m r * c`.
    simp_rw [propagatorDysonTerm_succ, intervalIntegral.intervalIntegral_eq_integral_uIoc]
    refine ((hasDerivAt_integral_of_dominated_of_differentiableOn
      (F := fun w r ↦ P w r ∘L propagatorDysonTerm (P w) s n r) (μ := volume.restrict (Ι s t))
      isOpen_ball (mem_ball_self hε) (fun w hw ↦ ?_) ?_ ((hmi.mono_set hst).mul_const c)
      ?_).differentiableAt.const_smul (if s ≤ t then 1 else -1 : ℝ)).differentiableWithinAt
    · exact ((hP w (hVU hw)).intervalIntegrable_clm_comp
        (continuousOn_propagatorDysonTerm (hP w (hVU hw)) hs n) hs ht).def'.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
      filter_upwards [hPm] with r hr hrJ w hw
      have hrab := hst hrJ
      have h1 := hr hrab w (ball_subset_closedBall hw)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul h1 ?_
        (norm_nonneg _) ((norm_nonneg _).trans h1))
      refine (norm_propagatorDysonTerm_le_of_norm_le (m := fun u ↦ ‖m u‖) (hP w (hVU hw))
        (IntegrableOn.intervalIntegrable (hmi.mono_set (uIcc_subset_Icc hs hrab)).norm)
        (hPm.mono fun u hu hu' ↦ (hu (uIcc_subset_Icc hs hrab (uIoc_subset_uIcc hu')) w
          (ball_subset_closedBall hw)).trans (Real.le_norm_self _)) hs n hrab).trans ?_
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _)
        (intervalIntegral.abs_integral_norm_le hmi hs hrab) n) (Nat.cast_nonneg _)
    · refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
      filter_upwards [hPd] with r hr hrJ
      exact ((hr (hst hrJ)).mono hVU).clm_comp ((ih (hst hrJ)).mono hVU)

variable [CompleteSpace E]

/-- **Holomorphic dependence of the propagator on a parameter.** Let `U ⊆ ℂ` be open and
`P : ℂ → ℝ → E →L[ℂ] E` such that `P z` is integrable on `[a, b]` for `z ∈ U`, `z ↦ P z r` is
holomorphic on `U` for almost every `r ∈ [a, b]`, and for every compact `K ⊆ U` there is an
integrable `m` on `[a, b]` such that, for almost every `r ∈ [a, b]`, `‖P z r‖ ≤ m r` for all
`z ∈ K` (the null set does not depend on `z`). Then for `s, t ∈ [a, b]` the propagator
`z ↦ N_{P z}(t, s)` is holomorphic on `U`. -/
theorem differentiableOn_propagator (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    DifferentiableOn ℂ (fun z ↦ propagator (P z) t s) U := by
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz)
  obtain ⟨m, hmi, hPm⟩ := hm _ hεU (isCompact_closedBall z ε)
  have hVU : ball z ε ⊆ U := ball_subset_closedBall.trans hεU
  have hmst := (hmi.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  -- On the disc `ball z ε` the Dyson series converges normally, so its sum is holomorphic.
  have hsum : DifferentiableOn ℂ (fun w ↦ ∑' n, propagatorDysonTerm (P w) s n t) (ball z ε) :=
    Complex.differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial _)
      (fun n ↦ (differentiableOn_propagatorDysonTerm hU hP hPd hm hs n ht).mono hVU)
      isOpen_ball fun n w hw ↦ norm_propagatorDysonTerm_le_of_norm_le (hP w (hVU hw)) hmst
        (hPm.mono fun r hr hr' ↦ hr (uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr')) w
          (ball_subset_closedBall hw)) hs n ht
  have heq : (fun w ↦ propagator (P w) t s) =ᶠ[𝓝 z]
      fun w ↦ ∑' n, propagatorDysonTerm (P w) s n t :=
    eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) fun w hw ↦
      ((hasSum_propagatorDysonTerm (hP w (hVU hw)) hs ht).tsum_eq).symm
  exact ((hsum.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))).congr_of_eventuallyEq
    heq).differentiableWithinAt

/-- Under the hypotheses of `TauCeti.differentiableOn_propagator`, the propagator
`z ↦ N_{P z}(t, s)` is analytic on `U`. -/
theorem analyticOnNhd_propagator (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    AnalyticOnNhd ℂ (fun z ↦ propagator (P z) t s) U :=
  (differentiableOn_propagator hU hP hPd hm hs ht).analyticOnNhd hU

/-- **Entire coefficients give entire propagators.** If `P z` is integrable on `[a, b]` for every
`z`, `z ↦ P z r` is entire for almost every `r ∈ [a, b]`, and the coefficients are dominated by
an integrable function on every compact set of parameters, then `z ↦ N_{P z}(t, s)` is entire
for `s, t ∈ [a, b]`. -/
theorem differentiable_propagator (hP : ∀ z, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → Differentiable ℂ (P · r))
    (hm : ∀ K : Set ℂ, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Differentiable ℂ fun z ↦ propagator (P z) t s :=
  differentiableOn_univ.1 <| differentiableOn_propagator isOpen_univ (fun z _ ↦ hP z)
    (hPd.mono fun _ hr hr' ↦ (hr hr').differentiableOn) (fun K _ hK ↦ hm K hK) hs ht

/-- **Affine dependence on the parameter.** For `A : E →L[ℂ] E` and a coefficient `B` integrable on
`[a, b]`, the propagator of `z • A + B` is entire in `z` for `s, t ∈ [a, b]`. The Dirac
coefficient of the nonlinear Fourier transform has this form. -/
theorem differentiable_propagator_smul_add (A : E →L[ℂ] E) {B : ℝ → E →L[ℂ] E}
    (hB : IntegrableOn B (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Differentiable ℂ fun z : ℂ ↦ propagator (fun r ↦ z • A + B r) t s := by
  have hc := measure_Icc_lt_top (μ := volume) (a := a) (b := b) |>.ne
  refine differentiable_propagator (P := fun z r ↦ z • A + B r)
    (fun z ↦ (integrableOn_const hc).add hB)
    (ae_of_all _ fun r _ ↦ (differentiable_id.smul_const A).add_const _) (fun K hK ↦ ?_) hs ht
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨fun r ↦ R * ‖A‖ + ‖B r‖, (integrableOn_const hc).add hB.norm,
    ae_of_all _ fun r _ z hz ↦ ?_⟩
  exact (norm_add_le _ _).trans (add_le_add_left ((norm_smul_le z A).trans
    (mul_le_mul_of_nonneg_right (hR z hz) (norm_nonneg A))) _)

end TauCeti
