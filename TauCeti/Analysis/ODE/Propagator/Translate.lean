/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Translating, dilating and conjugating a propagator

For a coefficient `P` integrable on `[a, b]`:

* `TauCeti.propagator_comp_add_right`: for a real `c`, the propagator of the translated
  coefficient `u ↦ P (u + c)` is the translate of the propagator of `P`,
  `N_{P(· + c)}(t, s) = N_P(t + c, s + c)` for `s, t ∈ [a - c, b - c]`;
* `TauCeti.propagator_smul_comp_mul_left`: for a real `c`, the propagator of the dilated
  coefficient `u ↦ c • P (c * u)` is `N_{c P(c ·)}(t, s) = N_P(c t, c s)` for `c s, c t ∈ [a, b]`;
* `TauCeti.propagator_mul_mul`: for mutually inverse operators `C` and `C'`, the propagator of
  the conjugated coefficient `u ↦ C * P u * C'` is `C * N_P(t, s) * C'`.

In each case both sides solve the same operator equation, after a change of variables in its
integral for the first two.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- **Translating time.** If `P` is integrable on `[a, b]` and `s, t ∈ [a - c, b - c]`, then the
propagator of `u ↦ P (u + c)` is `N_{P(· + c)}(t, s) = N_P(t + c, s + c)`. -/
theorem propagator_comp_add_right (hP : IntegrableOn P (Icc a b)) {c : ℝ}
    (hs : s ∈ Icc (a - c) (b - c)) (ht : t ∈ Icc (a - c) (b - c)) :
    propagator (fun u ↦ P (u + c)) t s = propagator P (t + c) (s + c) := by
  have hmem {r : ℝ} (hr : r ∈ Icc (a - c) (b - c)) : r + c ∈ Icc a b :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine propagator_eq_of_forall_mem_Icc (hP.comp_add_right_Icc c) hs ht
    (N := fun r ↦ propagator P (r + c) (s + c)) ?_ fun r hr ↦ ?_
  · exact (continuousOn_propagator_left hP (hmem hs)).comp
      (continuous_id.add continuous_const).continuousOn fun r hr ↦ hmem hr
  · rw [propagator_eq_one_add_integral hP (hmem hs) (hmem hr),
      ← intervalIntegral.integral_comp_add_right (fun u ↦ P u ∘L propagator P u (s + c)) c]

/-- **Dilating time.** If `P` is integrable on `[a, b]` and `c s, c t ∈ [a, b]` for a real `c`,
then the propagator of `u ↦ c • P (c * u)` is `N_{c P(c ·)}(t, s) = N_P(c t, c s)`. -/
theorem propagator_smul_comp_mul_left (hP : IntegrableOn P (Icc a b)) (c : ℝ)
    (hs : c * s ∈ Icc a b) (ht : c * t ∈ Icc a b) :
    propagator (fun u ↦ (c : 𝕜) • P (c * u)) t s = propagator P (c * t) (c * s) := by
  have hmem {r : ℝ} (hr : r ∈ uIcc s t) : c * r ∈ Icc a b :=
    uIcc_subset_Icc hs ht (image_const_mul_uIcc c s t ▸ mem_image_of_mem _ hr)
  have hPc : IntegrableOn (fun u ↦ (c : 𝕜) • P (c * u)) (uIcc s t) := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    refine Integrable.smul (c : 𝕜) ?_
    have h := ((intervalIntegrable_iff' (f := P) (a := c * s) (b := c * t) (μ := volume)).2
      (hP.mono_set (uIcc_subset_Icc hs ht))).comp_mul_left (c := c)
    rwa [mul_div_cancel_left₀ _ hc, mul_div_cancel_left₀ _ hc,
      intervalIntegrable_iff' (f := fun u ↦ P (c * u))] at h
  refine propagator_eq_of_forall_mem_Icc hPc left_mem_uIcc right_mem_uIcc
    (N := fun r ↦ propagator P (c * r) (c * s)) ?_ fun r hr ↦ ?_
  · exact (continuousOn_propagator_left hP hs).comp
      (continuous_const.mul continuous_id).continuousOn fun r hr ↦ hmem hr
  · rw [propagator_eq_one_add_integral hP hs (hmem hr),
      ← intervalIntegral.smul_integral_comp_mul_left (fun u ↦ P u ∘L propagator P u (c * s)) c]
    congr 1
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [ContinuousLinearMap.smul_comp, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- **Conjugating the coefficient.** If `P` is integrable on `[a, b]`, `s, t ∈ [a, b]` and
`C * C' = 1 = C' * C`, then the propagator of `u ↦ C * P u * C'` is `C * N_P(t, s) * C'`. -/
theorem propagator_mul_mul (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {C C' : E →L[𝕜] E} (hCC' : C * C' = 1) (hC'C : C' * C = 1) :
    propagator (fun u ↦ C * P u * C') t s = C * propagator P t s * C' := by
  -- The conjugation `X ↦ C X C'` as a continuous linear map on operators.
  let L : (E →L[𝕜] E) →L[𝕜] (E →L[𝕜] E) :=
    ContinuousLinearMap.compL 𝕜 E E E C ∘L (ContinuousLinearMap.compL 𝕜 E E E).flip C'
  have hL (X : E →L[𝕜] E) : L X = C * X * C' := rfl
  have hPL : IntegrableOn (fun u ↦ C * P u * C') (Icc a b) := by
    have h : IntegrableOn (fun u ↦ L (P u)) (Icc a b) := L.integrable_comp hP
    simpa only [hL] using h
  refine propagator_eq_of_forall_mem_Icc hPL hs ht (N := fun r ↦ C * propagator P r s * C')
    ((continuousOn_const.mul (continuousOn_propagator_left hP hs)).mul continuousOn_const)
    fun r hr ↦ ?_
  have hI : IntervalIntegrable (fun u ↦ P u ∘L propagator P u s) volume s r :=
    hP.intervalIntegrable_clm_comp (continuousOn_propagator_left hP hs) hs hr
  have hmul (u : ℝ) : (C * P u * C') ∘L (C * propagator P u s * C') =
      L (P u ∘L propagator P u s) := by
    rw [hL, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
    calc C * P u * C' * (C * propagator P u s * C')
        = C * P u * (C' * C) * propagator P u s * C' := by noncomm_ring
      _ = C * (P u * propagator P u s) * C' := by rw [hC'C]; noncomm_ring
  simp_rw [hmul]
  rw [L.intervalIntegral_comp_comm hI, hL, propagator_eq_one_add_integral hP hs hr, mul_add,
    add_mul, mul_one, hCC']

end TauCeti
