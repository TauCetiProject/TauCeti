/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Propagator bounds from the symmetric part of the coefficient

Let `N_P(t, s)` be the propagator of `x' = P(t) x` on a real inner product space
(`TauCeti.propagator`). The norm bound `‖N_P(t, s)‖ ≤ exp |∫ ‖P‖|`
(`TauCeti.norm_propagator_le`) sees the whole coefficient. Only the symmetric part of `P` changes
lengths: along a solution `x`, `(‖x‖²)' = 2 ⟪x, P x⟫`. So if `|⟪v, P(u) v⟫| ≤ m(u) ‖v‖²` for every
`v`, then

`exp (-|∫ₛᵗ m|) ‖v‖ ≤ ‖N_P(t, s) v‖ ≤ exp |∫ₛᵗ m| ‖v‖`

(`TauCeti.norm_propagator_apply_le_of_abs_inner_le`,
`TauCeti.exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le`). A skew-adjoint part of
`P`, for which `⟪v, P v⟫ = 0`, does not enter `m` at all.

The proof applies Grönwall's inequality
(`TauCeti.le_mul_exp_abs_integral_of_le_add_abs_integral_mul`) to `‖N_P(·, s) v‖²`, which is
absolutely continuous with derivative `2 ⟪x, P x⟫` almost everywhere
(`TauCeti.absolutelyContinuousOnInterval_norm_sq_propagator_apply_left`,
`TauCeti.ae_deriv_norm_sq_propagator_apply_left`), by the fundamental theorem of calculus for
absolutely continuous functions (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). The lower
bound follows from the upper bound for `N_P(s, t)`, the inverse of `N_P(t, s)`.
-/

public section

open MeasureTheory Set Real
open scoped RealInnerProductSpace Interval

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  {P : ℝ → E →L[𝕜] E} {m : ℝ → ℝ} {s t : ℝ}

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] in
/-- The `Icc` form of `uIcc s t` taken by the propagator API: `P` is integrable on
`Icc (min s t) (max s t)`, which contains `s` and `t`. -/
private theorem integrableOn_Icc_min_max_of_uIcc (hP : IntegrableOn P (uIcc s t)) :
    IntegrableOn P (Icc (min s t) (max s t)) ∧ s ∈ Icc (min s t) (max s t) ∧
      t ∈ Icc (min s t) (max s t) := by
  rw [Icc_min_max]
  exact ⟨hP, left_mem_uIcc, right_mem_uIcc⟩

/-- Along a solution, `r ↦ ‖N_P(r, s) v‖²` is absolutely continuous between `s` and `t`. -/
theorem absolutelyContinuousOnInterval_norm_sq_propagator_apply_left
    (hP : IntegrableOn P (uIcc s t)) (v : E) :
    AbsolutelyContinuousOnInterval (fun r ↦ ‖propagator P r s v‖ ^ 2) s t := by
  obtain ⟨hP', hs, -⟩ := integrableOn_Icc_min_max_of_uIcc hP
  have h := absolutelyContinuousOnInterval_propagator_left hP' hs
  have h' := (ContinuousLinearMap.apply 𝕜 E v).lipschitzWith.comp_absolutelyContinuousOnInterval h
  have hwac : AbsolutelyContinuousOnInterval (fun r ↦ propagator P r s v) s t := by
    refine h'.mono ?_
    rw [uIcc_of_le min_le_max, Icc_min_max]
  have hnac : AbsolutelyContinuousOnInterval (fun r ↦ ‖propagator P r s v‖) s t :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hwac
  simpa only [sq] using hnac.fun_mul hnac

/-- Along a solution, `(‖N_P(r, s) v‖²)' = 2 ⟪N_P(r, s) v, P(r) N_P(r, s) v⟫` for almost every `r`
between `s` and `t`. -/
theorem ae_deriv_norm_sq_propagator_apply_left (hP : IntegrableOn P (uIcc s t)) (v : E) :
    ∀ᵐ r ∂volume.restrict (uIcc s t), deriv (fun r ↦ ‖propagator P r s v‖ ^ 2) r =
      2 * ⟪propagator P r s v, P r (propagator P r s v)⟫ := by
  obtain ⟨hP', hs, -⟩ := integrableOn_Icc_min_max_of_uIcc hP
  rw [← Icc_min_max, ← Measure.restrict_congr_set Ioo_ae_eq_Icc,
    ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_hasDerivAt_propagator_left hP' hs] with r hr hrIoo
  exact ((((ContinuousLinearMap.apply 𝕜 E v).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    r (hr hrIoo)).norm_sq.deriv

/-- The integral inequality behind `TauCeti.norm_propagator_apply_le_of_abs_inner_le`:
`‖N_P(r, s) v‖² ≤ ‖v‖² + |∫ₛʳ 2 m ‖N_P(·, s) v‖²|` for `r` between `s` and `t`. -/
private theorem norm_sq_propagator_apply_le (hP : IntegrableOn P (uIcc s t))
    (hm : IntegrableOn m (uIcc s t))
    (hPm : ∀ᵐ u ∂volume.restrict (uIcc s t), ∀ v, |⟪v, P u v⟫| ≤ m u * ‖v‖ ^ 2) (v : E)
    {r : ℝ} (hr : r ∈ uIcc s t) :
    ‖propagator P r s v‖ ^ 2 ≤
      ‖v‖ ^ 2 + |∫ u in s..r, 2 * m u * ‖propagator P u s v‖ ^ 2| := by
  set f : ℝ → ℝ := fun r ↦ ‖propagator P r s v‖ ^ 2 with hf
  have hfac := absolutelyContinuousOnInterval_norm_sq_propagator_apply_left hP v
  have hβu : IntegrableOn (fun r ↦ 2 * m r * f r) (uIcc s t) :=
    IntegrableOn.mul_continuousOn (hm.const_mul 2) hfac.continuousOn isCompact_uIcc
  have hsub : uIcc s r ⊆ uIcc s t := uIcc_subset_uIcc left_mem_uIcc hr
  have hFTC := (hfac.mono hsub).integral_deriv_eq_sub
  have hf0 : f s = ‖v‖ ^ 2 := by simp [hf]
  have hle : |∫ u in s..r, deriv f u| ≤ |∫ u in s..r, 2 * m u * f u| := by
    have hnorm : |∫ u in s..r, deriv f u| ≤ |∫ u in s..r, ‖deriv f u‖| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_abs_integral_norm (f := deriv f) (a := s) (b := r)
    refine hnorm.trans (intervalIntegral.abs_integral_norm_le_abs_integral_of_norm_le
      (IntegrableOn.intervalIntegrable (hβu.mono_set hsub)) ?_)
    have hderiv := ae_deriv_norm_sq_propagator_apply_left hP v
    rw [ae_restrict_iff' measurableSet_uIcc] at hderiv hPm
    filter_upwards [hderiv, hPm] with u hu hPu hu'
    have hu'' := hsub (uIoc_subset_uIcc hu')
    rw [hu hu'', Real.norm_eq_abs, abs_mul, abs_two]
    have := hPu hu'' (propagator P u s v)
    simp only [hf]
    nlinarith [abs_nonneg ⟪propagator P u s v, P u (propagator P u s v)⟫]
  have : f r - f s ≤ |∫ u in s..r, deriv f u| := hFTC ▸ le_abs_self _
  linarith

/-- **Upper bound from the symmetric part.** If `P` and `m` are integrable between `s` and `t`
and `|⟪v, P(u) v⟫| ≤ m(u) ‖v‖²` for almost every `u` there and every `v`, then
`‖N_P(t, s) v‖ ≤ exp |∫ₛᵗ m| ‖v‖`. -/
theorem norm_propagator_apply_le_of_abs_inner_le (hP : IntegrableOn P (uIcc s t))
    (hm : IntegrableOn m (uIcc s t))
    (hPm : ∀ᵐ u ∂volume.restrict (uIcc s t), ∀ v, |⟪v, P u v⟫| ≤ m u * ‖v‖ ^ 2) (v : E) :
    ‖propagator P t s v‖ ≤ exp |∫ u in s..t, m u| * ‖v‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim v 0]
  -- `m ≥ 0` follows from the bound at any nonzero vector.
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hm₀ : ∀ᵐ u ∂volume.restrict (uIcc s t), 0 ≤ m u := hPm.mono fun u hu ↦
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hu w)) (pow_pos (norm_pos_iff.2 hw) 2)
  have hβu : IntegrableOn (fun r ↦ 2 * m r * ‖propagator P r s v‖ ^ 2) (uIcc s t) :=
    IntegrableOn.mul_continuousOn (hm.const_mul 2)
      (absolutelyContinuousOnInterval_norm_sq_propagator_apply_left hP v).continuousOn
        isCompact_uIcc
  -- Grönwall for `‖N_P(·, s) v‖²`.
  have hg := le_mul_exp_abs_integral_of_le_add_abs_integral_mul
    (u := fun r ↦ ‖propagator P r s v‖ ^ 2) (β := fun r ↦ 2 * m r) (t₀ := s) (t := t)
    (α := ‖v‖ ^ 2) (hm.const_mul 2) (hm₀.mono fun u hu ↦ by positivity)
    (by simpa only [mul_assoc] using hβu) (fun r _ ↦ by positivity)
    (fun r hr ↦ by simpa only [mul_assoc] using norm_sq_propagator_apply_le hP hm hPm v hr)
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_two] at hg
  have h2 : (exp |∫ u in s..t, m u| * ‖v‖) ^ 2 = ‖v‖ ^ 2 * exp (2 * |∫ u in s..t, m u|) := by
    rw [mul_pow, ← Real.exp_natCast_mul]
    push_cast
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h2 ▸ hg)

/-- **Lower bound from the symmetric part.** Under the hypotheses of
`TauCeti.norm_propagator_apply_le_of_abs_inner_le`, `‖v‖ ≤ exp |∫ₛᵗ m| ‖N_P(t, s) v‖`. This is
the multiplicative form of the lower bound
`TauCeti.exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le`. -/
theorem norm_le_exp_mul_norm_propagator_apply_of_abs_inner_le (hP : IntegrableOn P (uIcc s t))
    (hm : IntegrableOn m (uIcc s t))
    (hPm : ∀ᵐ u ∂volume.restrict (uIcc s t), ∀ v, |⟪v, P u v⟫| ≤ m u * ‖v‖ ^ 2) (v : E) :
    ‖v‖ ≤ exp |∫ u in s..t, m u| * ‖propagator P t s v‖ := by
  obtain ⟨hP', hs, ht⟩ := integrableOn_Icc_min_max_of_uIcc hP
  have hinv := congrArg (fun L : E →L[𝕜] E ↦ L v) (propagator_comp_propagator_swap hP' hs ht)
  simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at hinv
  rw [uIcc_comm] at hP hm hPm
  have h := norm_propagator_apply_le_of_abs_inner_le hP hm hPm (propagator P t s v)
  rwa [hinv, intervalIntegral.integral_symm, abs_neg] at h

/-- **Lower bound from the symmetric part.** Under the hypotheses of
`TauCeti.norm_propagator_apply_le_of_abs_inner_le`,
`exp (-|∫ₛᵗ m|) ‖v‖ ≤ ‖N_P(t, s) v‖`. -/
theorem exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le
    (hP : IntegrableOn P (uIcc s t)) (hm : IntegrableOn m (uIcc s t))
    (hPm : ∀ᵐ u ∂volume.restrict (uIcc s t), ∀ v, |⟪v, P u v⟫| ≤ m u * ‖v‖ ^ 2) (v : E) :
    exp (-|∫ u in s..t, m u|) * ‖v‖ ≤ ‖propagator P t s v‖ := by
  have h := norm_le_exp_mul_norm_propagator_apply_of_abs_inner_le hP hm hPm v
  rw [Real.exp_neg, inv_mul_le_iff₀ (exp_pos _)]
  exact h

end TauCeti
