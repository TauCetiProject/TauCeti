/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Inverting the integral of a positive continuous function

For a function continuous and positive on a compact real interval, its accumulated integral
has a strictly increasing `C¹` inverse on the interval from zero to the total integral.
The inverse extends to a `C¹` function on all of `ℝ` and has derivative the reciprocal of
the original function on the integral's range. This supplies the real-calculus construction
used in arc-length reparametrization.

## Main results

* `TauCeti.exists_contDiff_inverse_intervalIntegral`: an inverse for the accumulated integral,
  with both inverse identities and its derivative.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TauCeti

/-- The accumulated integral `t ↦ ∫ r in a..t, w r` of a locally integrable function bounded below
almost everywhere by a positive constant tends to `+∞` at `+∞` and to `-∞` at `-∞`. -/
theorem tendsto_intervalIntegral_atTop_atBot {w : ℝ → ℝ}
    {a : ℝ} (hw : ∀ t, IntervalIntegrable w volume a t) {m : ℝ} (hm : 0 < m)
    (hwm : ∀ᵐ t ∂volume, m ≤ w t) :
    Tendsto (fun t ↦ ∫ r in a..t, w r) atTop atTop ∧
      Tendsto (fun t ↦ ∫ r in a..t, w r) atBot atBot := by
  -- Compare with the integral `m * (t - a)` of the constant lower bound.
  constructor
  · refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_right _ (-(m * a)) (tendsto_id.const_mul_atTop hm))
    filter_upwards [eventually_ge_atTop a] with t ht
    have h := intervalIntegral.integral_mono_ae ht intervalIntegrable_const (hw t) hwm
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    simp only [id]
    linarith
  · refine tendsto_atBot_mono' atBot ?_
      (tendsto_atBot_add_const_right _ (-(m * a)) (tendsto_id.const_mul_atBot hm))
    filter_upwards [eventually_le_atBot a] with t ht
    have h := intervalIntegral.integral_mono_ae ht intervalIntegrable_const (hw t).symm hwm
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    rw [intervalIntegral.integral_symm]
    simp only [id]
    linarith

/-- The accumulated integral of a continuous function bounded below by a positive constant is
inverted by a `C¹` order isomorphism of `ℝ` whose derivative is the reciprocal of the function
at the inverse point. -/
theorem exists_orderIso_contDiff_inverse_intervalIntegral {w : ℝ → ℝ} (hw : Continuous w)
    {m : ℝ} (hm : 0 < m) (hwm : ∀ t, m ≤ w t) (a : ℝ) :
    ∃ ψ : ℝ ≃o ℝ, ContDiff ℝ 1 ψ ∧ (∀ t, ψ (∫ r in a..t, w r) = t) ∧
      (∀ s, (∫ r in a..ψ s, w r) = s) ∧ ∀ s, HasDerivAt ψ (w (ψ s))⁻¹ s := by
  let φ : ℝ → ℝ := fun t ↦ ∫ r in a..t, w r
  have hwpos : ∀ t, 0 < w t := fun t ↦ hm.trans_le (hwm t)
  have hφ : ∀ t, HasDerivAt φ (w t) t := fun t ↦ (hw.integral_hasStrictDerivAt a t).hasDerivAt
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun t ↦ (hφ t).continuousAt
  have hφmono : StrictMono φ := strictMono_of_hasDerivAt_pos hφ hwpos
  obtain ⟨htop, hbot⟩ :=
    tendsto_intervalIntegral_atTop_atBot (fun t ↦ hw.intervalIntegrable a t) hm (ae_of_all _ hwm)
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective φ hφmono (hφcont.surjective htop hbot)
  have hφψ : ∀ s, φ (e.symm s) = s := e.apply_symm_apply
  have hψd : ∀ s, HasDerivAt e.symm (w (e.symm s))⁻¹ s := fun s ↦
    HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hφ (e.symm s))
      (hwpos _).ne' (Eventually.of_forall hφψ)
  refine ⟨e.symm, ?_, fun t ↦ e.symm_apply_apply t, hφψ, hψd⟩
  refine contDiff_one_iff_deriv.2 ⟨fun s ↦ (hψd s).differentiableAt, ?_⟩
  have hderiv : deriv e.symm = fun s ↦ (w (e.symm s))⁻¹ := funext fun s ↦ (hψd s).deriv
  rw [hderiv]
  exact (hw.comp e.symm.continuous).inv₀ fun s ↦ (hwpos _).ne'

/-- Accumulated speed `t ↦ ∫ r in a..t, v r`, for a speed `v` continuous and positive on `[a, b]`,
has an inverse `ψ` on `[0, ∫ r in a..b, v r]` which is the restriction of a strictly increasing
`C¹` function on `ℝ`, maps into `[a, b]`, and has derivative the reciprocal speed. -/
theorem exists_contDiff_inverse_intervalIntegral {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ ContDiff ℝ 1 ψ ∧
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, v r) = t) ∧
      ∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, v r),
        ψ s ∈ Icc a b ∧ (∫ r in a..ψ s, v r) = s ∧ HasDerivAt ψ (v (ψ s))⁻¹ s := by
  -- Extend the speed by constants outside `[a, b]`. Its primitive is then inverted by a
  -- `C¹` order isomorphism of `ℝ`.
  let c : ℝ → ℝ := fun t ↦ max a (min b t)
  have hcmem : ∀ t, c t ∈ Icc a b := fun t ↦ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcid : ∀ t ∈ Icc a b, c t = t := fun t ht ↦ by simp [c, ht.1, ht.2]
  let w : ℝ → ℝ := fun t ↦ v (c t)
  have hw : Continuous w :=
    hv.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hcmem
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hv
  obtain ⟨e, hψC1, hψφ, hφψ, hψd⟩ := exists_orderIso_contDiff_inverse_intervalIntegral hw
    (hpos x₀ hx₀) (fun t ↦ hmin (hcmem t)) a
  -- On `[a, b]` the extended primitive is the accumulated speed itself.
  have hφeq : ∀ t ∈ Icc a b, (∫ r in a..t, w r) = ∫ r in a..t, v r := fun t ht ↦
    intervalIntegral.integral_congr fun r hr ↦
      congrArg v (hcid r (uIcc_subset_Icc (left_mem_Icc.2 hab) ht hr))
  have hψa : e 0 = a := by
    simpa using hψφ a
  refine ⟨e, e.strictMono, hψC1, fun t ht ↦ by rw [← hφeq t ht, hψφ], fun s hs ↦ ?_⟩
  have hψs : e s ∈ Icc a b := by
    constructor
    · exact hψa ▸ e.monotone hs.1
    · rw [← hψφ b, hφeq b (right_mem_Icc.2 hab)]
      exact e.monotone hs.2
  refine ⟨hψs, by rw [← hφeq _ hψs, hφψ], ?_⟩
  simpa only [w, hcid _ hψs] using hψd s

end TauCeti
