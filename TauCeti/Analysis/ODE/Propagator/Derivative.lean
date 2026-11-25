/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.ODE.Propagator.ParameterContinuity
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
factor tends to `∂_z P(z, r)` for almost every `r`, and `N_{P w}(r, s) → N_{P z}(r, s)` by the
joint continuity of the propagator in the parameter
(`TauCeti.continuousOn_propagator_parameter`). If `‖P w r‖ ≤ m r` on a disc of radius `ε` about
`z`, the Schwarz lemma (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) bounds the middle factor
by `2 m r / ε`, and the propagators are bounded by `exp (∫ ‖m‖)`, so dominated convergence gives
the limit.

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

/-- **Difference quotients of a bounded holomorphic function.** If `g` is holomorphic on the disc
`ball z ε` with `‖g‖ ≤ M` on the closed disc, then `‖(w - z)⁻¹ • (g w - g z)‖ ≤ 2 M / ε` for
`w ≠ z` in the disc, by the Schwarz lemma. -/
private theorem norm_inv_smul_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {ε M : ℝ} (hε : 0 < ε) (hg : DifferentiableOn ℂ g (ball z ε))
    (hM : ∀ w ∈ closedBall z ε, ‖g w‖ ≤ M) {w : ℂ} (hw : w ∈ ball z ε) (hwz : w ≠ z) :
    ‖(w - z)⁻¹ • (g w - g z)‖ ≤ 2 * M / ε := by
  have hmaps : MapsTo g (ball z ε) (closedBall (g z) (2 * M)) := fun w' hw' ↦ by
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hM w' (ball_subset_closedBall hw')
    have h2 := hM z (mem_closedBall_self hε.le)
    linarith [norm_sub_le (g w') (g z)]
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmaps hw
  rw [dist_eq_norm, dist_eq_norm] at hschwarz
  rw [norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hwz)), mul_comm]
  exact hschwarz

/-- The integrand `r ↦ N_P(t, r) (c • (P' r - P r)) N_{P'}(r, s)` of Duhamel's formula is
integrable on `[a, b]`. -/
private theorem integrableOn_propagator_comp_comp {P P' : ℝ → E →L[ℂ] E}
    (hP : IntegrableOn P (Icc a b)) (hP' : IntegrableOn P' (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (c : ℂ) :
    IntegrableOn (fun r ↦ propagator P t r ∘L (c • (P' r - P r)) ∘L propagator P' r s)
      (Icc a b) := by
  have h := (IntegrableOn.mul_continuousOn ((hP'.sub hP).smul c)
    (continuousOn_propagator_left hP' hs) isCompact_Icc).continuousOn_mul
    (continuousOn_propagator_right hP ht) isCompact_Icc
  simpa only [ContinuousLinearMap.mul_def, Pi.smul_apply, Pi.sub_apply] using h

/-- Under the hypotheses of `TauCeti.hasDerivAt_propagator`, `w ↦ N_{P w}(r, s)` is continuous
at every `z ∈ U`, for `r, s ∈ [a, b]`. -/
private theorem continuousAt_propagator_of_differentiableOn (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    {r : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hz : z ∈ U) :
    ContinuousAt (fun w ↦ propagator (P w) r s) z := by
  have hjoint := continuousOn_propagator_parameter (P := fun r w ↦ P w r) (U := U) (a := a)
    (b := b) (fun w hw ↦ (hP w hw).aestronglyMeasurable)
    (hPd.mono fun r h hr ↦ (h hr).continuousOn) fun K hKU hK ↦ by
      obtain ⟨m', hm'i, hPm'⟩ := hm K hKU hK
      exact ⟨m', hm'i, fun w hw ↦ hPm'.mono fun r h hr ↦ h hr w hw⟩
  exact ((hjoint ((r, s), z) ⟨⟨hr, hs⟩, hz⟩).comp (f := fun w ↦ ((r, s), w))
    (by fun_prop) fun w hw ↦ ⟨⟨hr, hs⟩, hw⟩).continuousAt (hU.mem_nhds hz)

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
  have hNle {w : ℂ} (hw : w ∈ closedBall z ε) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      ‖propagator (P w) x y‖ ≤ C :=
    norm_propagator_le_exp_of_forall_norm_le (fun w hw ↦ hP w (hεU hw)) hmi hPm hw hx hy
  -- The integrand of the difference quotient.
  set F : ℂ → ℝ → E →L[ℂ] E := fun w r ↦
    propagator (P z) t r ∘L ((w - z)⁻¹ • (P w r - P z r)) ∘L propagator (P w) r s
  have hball : ∀ᶠ w in 𝓝[≠] z, w ∈ ball z ε := nhdsWithin_le_nhds (ball_mem_nhds z hε)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := F) (fun r ↦ C * 2 / ε * C * ‖m r‖) ?_ ?_ ?_ ?_).congr' ?_
  · -- measurability
    filter_upwards [hball] with w hw
    exact (integrableOn_propagator_comp_comp (hP z hz) (hP w (hBU hw)) hs ht
      ((w - z)⁻¹) |>.mono_set hst).aestronglyMeasurable
  · -- domination
    filter_upwards [hball, self_mem_nhdsWithin] with w hw hwz
    filter_upwards [hPm, hPd] with r hr hrd hrJ
    have hrab := hst hrJ
    have hq := norm_inv_smul_sub_le hε ((hrd hrab).mono hBU)
      (fun w' hw' ↦ (hr hrab w' hw').trans (Real.le_norm_self _)) hw hwz
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
    have h1 : Tendsto (fun w ↦ (w - z)⁻¹ • (P w r - P z r)) (𝓝[≠] z) (𝓝 (deriv (P · r) z)) := by
      have := ((hrd hrab).differentiableAt (hU.mem_nhds hz)).hasDerivAt
      exact (hasDerivAt_iff_tendsto_slope.1 this).congr fun w ↦ slope_def_module _ _ _
    have h2 : Tendsto (fun w ↦ propagator (P w) r s) (𝓝[≠] z) (𝓝 (propagator (P z) r s)) :=
      (continuousAt_propagator_of_differentiableOn hU hP hPd hm hrab hs hz).tendsto.mono_left
        nhdsWithin_le_nhds
    have := tendsto_const_nhds (x := propagator (P z) t r) |>.mul (h1.mul h2)
    simpa only [F, ContinuousLinearMap.mul_def] using this
  · -- the difference quotient is the integral, by Duhamel's formula
    filter_upwards [hball] with w hw
    rw [slope_def_module, propagator_sub_propagator_eq_integral (hP z hz) (hP w (hBU hw)) hs ht,
      ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    simp [F, ContinuousLinearMap.smul_comp]

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
