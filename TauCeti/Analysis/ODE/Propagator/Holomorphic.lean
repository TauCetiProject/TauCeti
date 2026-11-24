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
integrable `m_K` on `[a, b]` with `‖P z r‖ ≤ m_K r` for almost every `r ∈ [a, b]` and all
`z ∈ K`. Then for `s, t ∈ [a, b]` the propagator `z ↦ N_{P z}(t, s)` is holomorphic on `U`
(`TauCeti.differentiableOn_propagator`), hence analytic (`TauCeti.analyticOnNhd_propagator`); an
entire family of coefficients has entire propagators (`TauCeti.differentiable_propagator`), for
instance the affine family `z • A + B r` (`TauCeti.differentiable_propagator_smul_add`).

Each Dyson term `D_{n+1}(t) = ∫ r in s..t, P z r ∘L D_n(r)` is a parametric integral of an
integrand holomorphic in `z` and dominated on compact sets, hence holomorphic in `z`
(`TauCeti.differentiableOn_propagatorDysonTerm`), and on a compact set `K` the terms are bounded
by `(∫ r in a..b, m_K r) ^ n / n!` (`TauCeti.norm_propagatorDysonTerm_le_of_norm_le`), so the
Dyson series converges locally uniformly in `z`.

The bound `‖N_{P z}(t, s)‖ ≤ exp |∫ r in s..t, m_K r|` for `z ∈ K` is
`TauCeti.norm_propagator_le_of_norm_le`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped Nat

namespace TauCeti

section Bound

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- **The factorial bound on the Dyson terms under a domination.** If `‖P r‖ ≤ m r` for almost
every `r ∈ [a, b]`, then `‖Dₙ(t)‖ ≤ (∫ r in a..b, m r) ^ n / n!` for `s, t ∈ [a, b]`. -/
theorem norm_propagatorDysonTerm_le_of_norm_le {m : ℝ → ℝ} (hP : IntegrableOn P (Icc a b))
    (hm : IntegrableOn m (Icc a b)) (hPm : ∀ᵐ r, r ∈ Icc a b → ‖P r‖ ≤ m r)
    (hs : s ∈ Icc a b) (n : ℕ) (ht : t ∈ Icc a b) :
    ‖propagatorDysonTerm P s n t‖ ≤ (∫ r in a..b, m r) ^ n / n ! := by
  have hab := hs.1.trans hs.2
  refine (norm_propagatorDysonTerm_le hP hs n ht).trans ?_
  gcongr
  refine (intervalIntegral.abs_integral_norm_le hP hs ht).trans ?_
  exact intervalIntegral.integral_mono_ae_restrict hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hP.norm)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hm)
    ((ae_restrict_iff' measurableSet_Icc).2 hPm)

end Bound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {P : ℂ → ℝ → E →L[ℂ] E} {U : Set ℂ} {a b s t : ℝ}

/-- An integral over a measurable set `J` of an integrand holomorphic in the parameter on an open
set `V` and dominated there by an integrable function is complex differentiable on `V`. -/
private theorem differentiableAt_setIntegral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {G : ℂ → ℝ → X} {V : Set ℂ} {J : Set ℝ} {z : ℂ} {bound : ℝ → ℝ}
    (hV : IsOpen V) (hz : z ∈ V) (hJ : MeasurableSet J)
    (hmeas : ∀ w ∈ V, AEStronglyMeasurable (G w) (volume.restrict J))
    (hb : IntegrableOn bound J) (h_bound : ∀ᵐ r, r ∈ J → ∀ w ∈ V, ‖G w r‖ ≤ bound r)
    (h_diff : ∀ᵐ r, r ∈ J → DifferentiableOn ℂ (G · r) V) :
    DifferentiableAt ℂ (fun w ↦ ∫ r in J, G w r) z :=
  (hasDerivAt_integral_of_dominated_of_differentiableOn hV hz hmeas
    ((ae_restrict_iff' hJ).2 h_bound) hb ((ae_restrict_iff' hJ).2 h_diff)).differentiableAt

/-- Every point of an open set `U ⊆ ℂ` is the centre of a closed disc of positive radius
contained in `U`. -/
private theorem exists_closedBall_subset {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ ε > 0, closedBall z ε ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hrU⟩

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
    obtain ⟨ε, hε, hεU⟩ := exists_closedBall_subset hU hz
    obtain ⟨m, hmi, hPm⟩ := hm _ hεU (isCompact_closedBall z ε)
    have hVU : ball z ε ⊆ U := ball_subset_closedBall.trans hεU
    set c := (∫ r in a..b, m r) ^ n / (n ! : ℝ)
    -- The integrand `P w r ∘L Dₙ(r)` is holomorphic in `w` and dominated by `m r * c`.
    set G : ℂ → ℝ → E →L[ℂ] E := fun w r ↦ P w r ∘L propagatorDysonTerm (P w) s n r
    have hGi (w : ℂ) (hw : w ∈ U) : IntervalIntegrable (G w) volume s t :=
      (hP w hw).intervalIntegrable_clm_comp
        (continuousOn_propagatorDysonTerm (hP w hw) hs n) hs ht
    have hpiece {J : Set ℝ} (hJ : MeasurableSet J) (hJab : J ⊆ Icc a b)
        (hJi : ∀ w ∈ U, IntegrableOn (G w) J) :
        DifferentiableAt ℂ (fun w ↦ ∫ r in J, G w r) z := by
      refine differentiableAt_setIntegral isOpen_ball (mem_ball_self hε) hJ
        (fun w hw ↦ (hJi w (hVU hw)).aestronglyMeasurable) ((hmi.mono_set hJab).mul_const c)
        ?_ ?_
      · filter_upwards [hPm] with r hr hrJ w hw
        have hrab := hJab hrJ
        have h1 := hr hrab w (ball_subset_closedBall hw)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul h1
          (norm_propagatorDysonTerm_le_of_norm_le (hP w (hVU hw)) hmi
            (hPm.mono fun u hu hu' ↦ hu hu' w (ball_subset_closedBall hw)) hs n hrab)
          (norm_nonneg _) ((norm_nonneg _).trans h1))
      · filter_upwards [hPd] with r hr hrJ
        exact ((hr (hJab hrJ)).mono hVU).clm_comp ((ih (hJab hrJ)).mono hVU)
    have h₁ := hpiece measurableSet_Ioc (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2))
      fun w hw ↦ (hGi w hw).1
    have h₂ := hpiece measurableSet_Ioc (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1 hs.2))
      fun w hw ↦ (hGi w hw).2
    refine (h₁.sub h₂).differentiableWithinAt.congr (fun w _ ↦ ?_) ?_ <;>
      simp only [propagatorDysonTerm_succ, intervalIntegral, G, Pi.sub_apply]

variable [CompleteSpace E]

/-- **Holomorphic dependence of the propagator on a parameter.** Let `U ⊆ ℂ` be open and
`P : ℂ → ℝ → E →L[ℂ] E` such that `P z` is integrable on `[a, b]` for `z ∈ U`, `z ↦ P z r` is
holomorphic on `U` for almost every `r ∈ [a, b]`, and for every compact `K ⊆ U` there is an
integrable `m` on `[a, b]` with `‖P z r‖ ≤ m r` for all `z ∈ K` and almost every `r ∈ [a, b]`.
Then for `s, t ∈ [a, b]` the propagator `z ↦ N_{P z}(t, s)` is holomorphic on `U`. -/
theorem differentiableOn_propagator (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    DifferentiableOn ℂ (fun z ↦ propagator (P z) t s) U := by
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := exists_closedBall_subset hU hz
  obtain ⟨m, hmi, hPm⟩ := hm _ hεU (isCompact_closedBall z ε)
  have hVU : ball z ε ⊆ U := ball_subset_closedBall.trans hεU
  -- On the disc `ball z ε` the Dyson series converges normally, so its sum is holomorphic.
  have hsum : DifferentiableOn ℂ (fun w ↦ ∑' n, propagatorDysonTerm (P w) s n t) (ball z ε) :=
    Complex.differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial _)
      (fun n ↦ (differentiableOn_propagatorDysonTerm hU hP hPd hm hs n ht).mono hVU)
      isOpen_ball fun n w hw ↦ norm_propagatorDysonTerm_le_of_norm_le (hP w (hVU hw)) hmi
        (hPm.mono fun r hr hr' ↦ hr hr' w (ball_subset_closedBall hw)) hs n ht
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
`[a, b]`, the propagator of `z • A + B` is entire in `z` for `s, t ∈ [a, b]`; on a compact set
`K` with `‖z‖ ≤ R` the domination is `R ‖A‖ + ‖B r‖`. The Dirac coefficient of the nonlinear
Fourier transform has this form. -/
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
