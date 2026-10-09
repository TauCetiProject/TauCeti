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

/-- Accumulated speed `t ↦ ∫ r in a..t, v r`, for a speed `v` continuous and positive on `[a, b]`,
has an inverse `ψ` on `[0, ∫ r in a..b, v r]` which is the restriction of a strictly increasing
`C¹` function on `ℝ`, maps into `[a, b]`, and has derivative the reciprocal speed. -/
theorem exists_contDiff_inverse_intervalIntegral {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ ContDiff ℝ 1 ψ ∧
      (∀ t ∈ Icc a b, ψ (∫ r in a..t, v r) = t) ∧
      ∀ s ∈ Icc (0 : ℝ) (∫ r in a..b, v r),
        ψ s ∈ Icc a b ∧ (∫ r in a..ψ s, v r) = s ∧ HasDerivAt ψ (v (ψ s))⁻¹ s := by
  -- Extend the speed by constants outside `[a, b]`. Its primitive `φ` is then `C¹`, with
  -- derivative bounded below by a positive constant, hence an increasing bijection of `ℝ`.
  let c : ℝ → ℝ := fun t ↦ max a (min b t)
  have hcmem : ∀ t, c t ∈ Icc a b := fun t ↦ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcid : ∀ t ∈ Icc a b, c t = t := fun t ht ↦ by simp [c, ht.1, ht.2]
  let w : ℝ → ℝ := fun t ↦ v (c t)
  have hw : Continuous w :=
    hv.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hcmem
  have hwpos : ∀ t, 0 < w t := fun t ↦ hpos _ (hcmem t)
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hv
  have hm : 0 < v x₀ := hpos x₀ hx₀
  have hwm : ∀ t, v x₀ ≤ w t := fun t ↦ hmin (hcmem t)
  let φ : ℝ → ℝ := fun t ↦ ∫ r in a..t, w r
  have hφ : ∀ t, HasDerivAt φ (w t) t := fun t ↦ (hw.integral_hasStrictDerivAt a t).hasDerivAt
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun t ↦ (hφ t).continuousAt
  have hφmono : StrictMono φ := strictMono_of_hasDerivAt_pos hφ hwpos
  have hg : Monotone fun t ↦ φ t - v x₀ * t := by
    have hgd : ∀ t, HasDerivAt (fun t ↦ φ t - v x₀ * t) (w t - v x₀) t := fun t ↦
      (hφ t).sub (by simpa using (hasDerivAt_id t).const_mul (v x₀))
    refine monotone_of_deriv_nonneg (fun t ↦ (hgd t).differentiableAt) fun t ↦ ?_
    rw [(hgd t).deriv]
    exact sub_nonneg.2 (hwm t)
  have htop : Tendsto φ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_left _ (φ 0) (tendsto_id.const_mul_atTop hm))
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h := hg ht
    simp only [mul_zero, sub_zero] at h
    simp only [id]
    linarith
  have hbot : Tendsto φ atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_
      (tendsto_atBot_add_const_left _ (φ 0) (tendsto_id.const_mul_atBot hm))
    filter_upwards [eventually_le_atBot 0] with t ht
    have h := hg ht
    simp only [mul_zero, sub_zero] at h
    simp only [id]
    linarith
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective φ hφmono (hφcont.surjective htop hbot)
  let ψ : ℝ → ℝ := e.symm
  have hψφ : ∀ t, ψ (φ t) = t := e.symm_apply_apply
  have hφψ : ∀ s, φ (ψ s) = s := e.apply_symm_apply
  have hψcont : Continuous ψ := e.symm.continuous
  have hψd : ∀ s, HasDerivAt ψ (w (ψ s))⁻¹ s := fun s ↦
    HasDerivAt.of_local_left_inverse hψcont.continuousAt (hφ (ψ s)) (hwpos _).ne'
      (Eventually.of_forall hφψ)
  have hψC1 : ContDiff ℝ 1 ψ := by
    refine contDiff_one_iff_deriv.2 ⟨fun s ↦ (hψd s).differentiableAt, ?_⟩
    have hderiv : deriv ψ = fun s ↦ (w (ψ s))⁻¹ := funext fun s ↦ (hψd s).deriv
    rw [hderiv]
    exact (hw.comp hψcont).inv₀ fun s ↦ (hwpos _).ne'
  -- On `[a, b]` the extended primitive is the accumulated speed itself.
  have hφeq : ∀ t ∈ Icc a b, φ t = ∫ r in a..t, v r := fun t ht ↦
    intervalIntegral.integral_congr fun r hr ↦
      congrArg v (hcid r (uIcc_subset_Icc (left_mem_Icc.2 hab) ht hr))
  have hψa : ψ 0 = a := by
    simpa [φ] using hψφ a
  refine ⟨ψ, e.symm.strictMono, hψC1, fun t ht ↦ by rw [← hφeq t ht, hψφ], fun s hs ↦ ?_⟩
  have hψs : ψ s ∈ Icc a b := by
    constructor
    · exact hψa ▸ e.symm.monotone hs.1
    · rw [← hψφ b, hφeq b (right_mem_Icc.2 hab)]
      exact e.symm.monotone hs.2
  refine ⟨hψs, by rw [← hφeq _ hψs, hφψ], ?_⟩
  simpa only [w, hcid _ hψs] using hψd s

end TauCeti
