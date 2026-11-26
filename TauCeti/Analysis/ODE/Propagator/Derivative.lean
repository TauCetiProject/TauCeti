/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.ODE.Propagator.Holomorphic.Basic
import TauCeti.Analysis.ODE.VariationOfConstants
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The derivative of the propagator in a holomorphic parameter

Let `E` be a complex Banach space, `U ⊆ ℂ` open, and `P : ℂ → ℝ → E →L[ℂ] E` a family of
coefficients such that `P z` is integrable on `[a, b]` for `z ∈ U`, `z ↦ P z r` is holomorphic
on `U` for almost every `r ∈ [a, b]`, and on every compact `K ⊆ U` the coefficients are
dominated by one integrable function. For `s, t ∈ [a, b]` and `z ∈ U`, the propagator has the
derivative

`∂_z N_{P z}(t, s) = ∫ r in s..t, N_{P z}(t, r) ∂_z P(z, r) N_{P z}(r, s)`

(`TauCeti.hasDerivAt_propagator`).

By Duhamel's formula (`TauCeti.propagator_sub_propagator_eq_integral`), the difference quotient
of `w ↦ N_{P w}(t, s)` at `z` is
`∫ r in s..t, N_{P z}(t, r) ((P w r - P z r) / (w - z)) N_{P w}(r, s)`. As `w → z` the middle
factor tends to `∂_z P(z, r)` for almost every `r`, and `N_{P w}(r, s) → N_{P z}(r, s)` since
the propagator is holomorphic in the parameter (`TauCeti.differentiableOn_propagator`). If
`‖P w r‖ ≤ m r` on a disc of radius `ε` about `z`, the Schwarz lemma
(`Complex.norm_dslope_le_div_of_mapsTo_ball`) bounds the middle factor by `2 m r / ε`, and the
propagators are bounded by `exp (∫ ‖m‖)`, so dominated convergence gives the limit.

## Main results

* `TauCeti.hasDerivAt_propagator`: the derivative formula.
* `TauCeti.deriv_propagator`: the same formula for `deriv`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {P : ℂ → ℝ → E →L[ℂ] E} {U : Set ℂ} {a b s t : ℝ} {z : ℂ}

/-- Propagators of coefficients dominated by `m` on `[a, b]` are bounded by
`exp (∫ u in a..b, ‖m u‖)` between any two points of `[a, b]`. -/
private theorem norm_propagator_le_exp_of_forall_norm_le {K : Set ℂ} {m : ℝ → ℝ}
    (hP : ∀ z ∈ K, IntegrableOn (P z) (Icc a b)) (hmi : IntegrableOn m (Icc a b))
    (hPm : ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r) {w : ℂ} (hw : w ∈ K) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖propagator (P w) x y‖ ≤ Real.exp (∫ u in a..b, ‖m u‖) :=
  (norm_propagator_le_of_norm_le (P := P w) (m := fun u ↦ ‖m u‖)
    ((hP w hw).mono_set (uIcc_subset_Icc hy hx)).intervalIntegrable
    (IntegrableOn.intervalIntegrable (hmi.mono_set (uIcc_subset_Icc hy hx)).norm)
    (hPm.mono fun _ hu hu' ↦ (hu (uIcc_subset_Icc hy hx (uIoc_subset_uIcc hu')) w hw).trans
      (Real.le_norm_self _))).trans
    (Real.exp_le_exp.2 (intervalIntegral.abs_integral_norm_le hmi hy hx))

/-- **The derivative of the propagator in a holomorphic parameter.** Let `U ⊆ ℂ` be open and
`P : ℂ → ℝ → E →L[ℂ] E` such that `P z` is integrable on `[a, b]` for `z ∈ U`, `z ↦ P z r` is
holomorphic on `U` for almost every `r ∈ [a, b]`, and for every compact `K ⊆ U` there is an
integrable `m` on `[a, b]` such that, for almost every `r ∈ [a, b]`, `‖P z r‖ ≤ m r` for all
`z ∈ K`. Then for `s, t ∈ [a, b]` and `z ∈ U`, `w ↦ N_{P w}(t, s)` has derivative
`∫ r in s..t, N_{P z}(t, r) ∂_z P(z, r) N_{P z}(r, s)` at `z`. -/
theorem hasDerivAt_propagator (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hz : z ∈ U) :
    HasDerivAt (fun w ↦ propagator (P w) t s)
      (∫ r in s..t, propagator (P z) t r ∘L deriv (P · r) z ∘L propagator (P z) r s) z := by
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz)
  obtain ⟨m, hmi, hPm⟩ := hm _ hεU (isCompact_closedBall z ε)
  have hst : Ι s t ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
  have hBU : ball z ε ⊆ U := ball_subset_closedBall.trans hεU
  set C := Real.exp (∫ u in a..b, ‖m u‖)
  have hNle {w : ℂ} :=
    norm_propagator_le_exp_of_forall_norm_le (w := w) (fun w hw ↦ hP w (hεU hw)) hmi hPm
  -- The integrand of the difference quotient.
  set F : ℂ → ℝ → E →L[ℂ] E := fun w r ↦
    propagator (P z) t r ∘L ((w - z)⁻¹ • (P w r - P z r)) ∘L propagator (P w) r s
  have hball : ∀ᶠ w in 𝓝[≠] z, w ∈ ball z ε := nhdsWithin_le_nhds (ball_mem_nhds z hε)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := F) (fun r ↦ C * 2 / ε * C * ‖m r‖) ?_ ?_ ?_ ?_).congr' ?_
  · -- measurability
    filter_upwards [hball] with w hw
    refine (((integrableOn_propagator_comp_sub_comp (hP z hz) (hP w (hBU hw)) hs ht).mono_set
      hst).aestronglyMeasurable.const_smul (w - z)⁻¹).congr (ae_of_all _ fun r ↦ ?_)
    simp [F, ContinuousLinearMap.smul_comp]
  · -- domination, by the Schwarz lemma for `P · r` on `ball z ε`
    filter_upwards [hball, self_mem_nhdsWithin] with w hw hwz
    filter_upwards [hPm, hPd] with r hr hrd hrJ
    have hrab := hst hrJ
    have hmaps : MapsTo (P · r) (ball z ε) (closedBall (P z r) (2 * ‖m r‖)) := fun w' hw' ↦ by
      rw [mem_closedBall_iff_norm]
      linarith [norm_sub_le (P w' r) (P z r), Real.le_norm_self (m r),
        hr hrab w' (ball_subset_closedBall hw'), hr hrab z (mem_closedBall_self hε.le)]
    have hq := Complex.norm_dslope_le_div_of_mapsTo_ball ((hrd hrab).mono hBU) hmaps hw
    rw [dslope_of_ne _ hwz, slope_def_module] at hq
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul (hNle (mem_closedBall_self hε.le) ht hrab)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hq
        (hNle (ball_subset_closedBall hw) hrab hs) (norm_nonneg _) (by positivity)))
      (by positivity) (by positivity) |>.trans_eq (by ring)
  · -- integrability of the bound
    exact (IntegrableOn.intervalIntegrable (hmi.mono_set (uIcc_subset_Icc hs ht)).norm).const_mul _
  · -- pointwise limit
    filter_upwards [hPd] with r hrd hrJ
    have hrab := hst hrJ
    have h1 := (hasDerivAt_iff_tendsto_slope.1
      ((hrd hrab).differentiableAt (hU.mem_nhds hz)).hasDerivAt).congr (slope_def_module (P · r) z)
    have h2 := ((differentiableOn_propagator hU hP hPd hm hs hrab).differentiableAt
      (hU.mem_nhds hz)).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    have := tendsto_const_nhds (x := propagator (P z) t r) |>.mul (h1.mul h2)
    simpa only [F, ContinuousLinearMap.mul_def] using this
  · -- the difference quotient is the integral, by Duhamel's formula
    filter_upwards [hball] with w hw
    rw [slope_def_module, propagator_sub_propagator_eq_integral (hP z hz) (hP w (hBU hw)) hs ht,
      ← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun r _ ↦ by simp [F, ContinuousLinearMap.smul_comp]

/-- **The derivative of the propagator in a holomorphic parameter**, for `deriv`: under the
hypotheses of `TauCeti.hasDerivAt_propagator`,
`∂_z N_{P z}(t, s) = ∫ r in s..t, N_{P z}(t, r) ∂_z P(z, r) N_{P z}(r, s)`. -/
theorem deriv_propagator (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hz : z ∈ U) :
    deriv (fun w ↦ propagator (P w) t s) z =
      ∫ r in s..t, propagator (P z) t r ∘L deriv (P · r) z ∘L propagator (P z) r s :=
  (hasDerivAt_propagator hU hP hPd hm hs ht hz).deriv

end TauCeti
