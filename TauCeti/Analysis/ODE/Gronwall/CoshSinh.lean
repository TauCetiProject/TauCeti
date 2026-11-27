/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# A Grönwall inequality for a pair of functions, with `cosh` and `sinh`

Let `k` be integrable on `[a, b]` and nonnegative almost everywhere there, and write
`L(s) = ∫ₛᵇ k`. If two continuous functions satisfy `A(s) ≤ 1 + ∫ₛᵇ k B` and `B(s) ≤ ∫ₛᵇ k A`
on `[a, b]`, then `A(s) ≤ cosh L(s)` and `B(s) ≤ sinh L(s)`
(`TauCeti.le_cosh_and_le_sinh_of_le_integral`). The comparison functions solve the equalities:
`cosh L(s) = 1 + ∫ₛᵇ k sinh L` and `sinh L(s) = ∫ₛᵇ k cosh L`
(`TauCeti.cosh_integral_eq_one_add_integral`, `TauCeti.sinh_integral_eq_integral`).

This is the comparison behind the bounds `|a| ≤ cosh ∫|q|` and `|b| ≤ sinh ∫|q|` of the scattering
functions of a Dirac system; Grönwall's inequality for the sum `A + B` only gives `exp ∫ k`.

## Implementation notes

The identities are the fundamental theorem of calculus for the absolutely continuous functions
`cosh ∘ L` and `sinh ∘ L` (`IntervalIntegrable.comp_intervalIntegral_left_eq_add_integral`). For
the inequality, the positive parts `u⁺` and `v⁺` of `u = A - cosh L` and `v = B - sinh L` satisfy
`u⁺ + v⁺ ≤ ∫ₛᵇ k (u⁺ + v⁺)`, so they vanish by the backward form of Grönwall's inequality,
`TauCeti.le_mul_exp_integral_of_le_add_integral_mul_rev`.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {k : ℝ → ℝ} {a b : ℝ}

/-- **The `cosh` identity.** For `k` integrable on `[a, b]` and `s ∈ [a, b]`,
`cosh (∫ₛᵇ k) = 1 + ∫ₛᵇ k(r) sinh (∫ᵣᵇ k) dr`. -/
theorem cosh_integral_eq_one_add_integral (hk : IntegrableOn k (Icc a b)) {s : ℝ}
    (hs : s ∈ Icc a b) :
    Real.cosh (∫ r in s..b, k r) = 1 + ∫ r in s..b, k r * Real.sinh (∫ u in r..b, k u) := by
  have hki := (intervalIntegrable_iff_integrableOn_Icc_of_le (hs.1.trans hs.2)).2 hk
  simpa using hki.comp_intervalIntegral_left_eq_add_integral right_mem_uIcc Real.contDiff_cosh
    Real.hasDerivAt_cosh (mem_uIcc_of_le hs.1 hs.2)

/-- **The `sinh` identity.** For `k` integrable on `[a, b]` and `s ∈ [a, b]`,
`sinh (∫ₛᵇ k) = ∫ₛᵇ k(r) cosh (∫ᵣᵇ k) dr`. -/
theorem sinh_integral_eq_integral (hk : IntegrableOn k (Icc a b)) {s : ℝ} (hs : s ∈ Icc a b) :
    Real.sinh (∫ r in s..b, k r) = ∫ r in s..b, k r * Real.cosh (∫ u in r..b, k u) := by
  have hki := (intervalIntegrable_iff_integrableOn_Icc_of_le (hs.1.trans hs.2)).2 hk
  simpa using hki.comp_intervalIntegral_left_eq_add_integral right_mem_uIcc Real.contDiff_sinh
    Real.hasDerivAt_sinh (mem_uIcc_of_le hs.1 hs.2)

/-- Products of `k` with functions continuous on `[a, b]` are interval integrable on `[s, b]`. -/
private theorem intervalIntegrable_mul (hk : IntegrableOn k (Icc a b)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {s : ℝ} (hs : s ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ k r * f r) volume s b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).2
    ((hk.mul_continuousOn hf isCompact_Icc).mono_set (Icc_subset_Icc_left hs.1))

/-- One step of the comparison: if `A(s) ≤ c + ∫ₛᵇ k B` and `F(s) = c + ∫ₛᵇ k G`, then
`A(s) - F(s) ≤ ∫ₛᵇ k (B - G)⁺`. -/
private theorem sub_le_integral_max (hk : IntegrableOn k (Icc a b))
    (hk0 : ∀ᵐ r ∂volume.restrict (Icc a b), 0 ≤ k r)
    {A B F G : ℝ → ℝ} {c s : ℝ} (hB : ContinuousOn B (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hs : s ∈ Icc a b) (hA : A s ≤ c + ∫ r in s..b, k r * B r)
    (hF : F s = c + ∫ r in s..b, k r * G r) :
    A s - F s ≤ ∫ r in s..b, k r * max (B r - G r) 0 := by
  calc A s - F s ≤ (c + ∫ r in s..b, k r * B r) - (c + ∫ r in s..b, k r * G r) := by
        rw [← hF]; exact sub_le_sub_right hA _
    _ = ∫ r in s..b, k r * (B r - G r) := by
        rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
          (intervalIntegrable_mul hk hB hs) (intervalIntegrable_mul hk hG hs)]
        simp_rw [mul_sub]
    _ ≤ ∫ r in s..b, k r * max (B r - G r) 0 := by
        refine intervalIntegral.integral_mono_ae_restrict hs.2
          (intervalIntegrable_mul hk (hB.sub hG) hs)
          (intervalIntegrable_mul hk (ContinuousOn.sup (hB.sub hG) continuousOn_const) hs) ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_left hs.1) hk0]
          with r hr
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hr

/-- **Grönwall's inequality for a pair, with `cosh` and `sinh`.** Let `k` be integrable on
`[a, b]` and nonnegative almost everywhere there, and let `A`, `B` be continuous on `[a, b]` with
`A(s) ≤ 1 + ∫ₛᵇ k B` and `B(s) ≤ ∫ₛᵇ k A` for `s ∈ [a, b]`. Then `A(s) ≤ cosh (∫ₛᵇ k)` and
`B(s) ≤ sinh (∫ₛᵇ k)`. -/
theorem le_cosh_and_le_sinh_of_le_integral (hk : IntegrableOn k (Icc a b))
    (hk0 : ∀ᵐ r ∂volume.restrict (Icc a b), 0 ≤ k r) {A B : ℝ → ℝ}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hAB : ∀ s ∈ Icc a b, A s ≤ 1 + ∫ r in s..b, k r * B r)
    (hBA : ∀ s ∈ Icc a b, B s ≤ ∫ r in s..b, k r * A r) {s : ℝ} (hs : s ∈ Icc a b) :
    A s ≤ Real.cosh (∫ r in s..b, k r) ∧ B s ≤ Real.sinh (∫ r in s..b, k r) := by
  set L : ℝ → ℝ := fun s ↦ ∫ r in s..b, k r
  have hLc : ContinuousOn L (Icc a b) := hk.continuousOn_intervalIntegral_left
  have hcosh : ContinuousOn (fun r ↦ Real.cosh (L r)) (Icc a b) :=
    Real.continuous_cosh.comp_continuousOn hLc
  have hsinh : ContinuousOn (fun r ↦ Real.sinh (L r)) (Icc a b) :=
    Real.continuous_sinh.comp_continuousOn hLc
  -- The positive parts `u = (A - cosh L)⁺` and `v = (B - sinh L)⁺`.
  set u : ℝ → ℝ := fun s ↦ max (A s - Real.cosh (L s)) 0
  set v : ℝ → ℝ := fun s ↦ max (B s - Real.sinh (L s)) 0
  have huc : ContinuousOn u (Icc a b) := ContinuousOn.sup (hA.sub hcosh) continuousOn_const
  have hvc : ContinuousOn v (Icc a b) := ContinuousOn.sup (hB.sub hsinh) continuousOn_const
  have hu0 (r : ℝ) : 0 ≤ u r := le_max_right _ _
  have hv0 (r : ℝ) : 0 ≤ v r := le_max_right _ _
  have hnn {f : ℝ → ℝ} (hf : ∀ r, 0 ≤ f r) (s : ℝ) (hs : s ∈ Icc a b) :
      0 ≤ ∫ r in s..b, k r * f r := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hs.2 ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_left hs.1) hk0] with r hr
    exact mul_nonneg hr (hf r)
  -- `w = u + v` satisfies `w ≤ ∫ₛᵇ k w`, hence vanishes.
  have key (s : ℝ) (hs : s ∈ Icc a b) : u s + v s ≤ 0 + ∫ r in s..b, k r * (u r + v r) := by
    have hu := sub_le_integral_max hk hk0 hB hsinh hs (F := fun r ↦ Real.cosh (L r)) (hAB s hs)
      (cosh_integral_eq_one_add_integral hk hs)
    have hv := sub_le_integral_max hk hk0 hA hcosh hs (F := fun r ↦ Real.sinh (L r)) (c := 0)
      (by simpa using hBA s hs) (by simpa using sinh_integral_eq_integral hk hs)
    simp_rw [mul_add]
    rw [zero_add, intervalIntegral.integral_add (intervalIntegrable_mul hk huc hs)
      (intervalIntegrable_mul hk hvc hs), add_comm (u s)]
    exact add_le_add (max_le hv (hnn hu0 s hs)) (max_le hu (hnn hv0 s hs))
  have hw := le_mul_exp_integral_of_le_add_integral_mul_rev hk hk0
    (hk.mul_continuousOn (huc.add hvc) isCompact_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ key)) hs (key s hs)
  rw [zero_mul] at hw
  constructor
  · have := (le_max_left _ _).trans ((le_add_of_nonneg_right (hv0 s)).trans hw)
    linarith
  · have := (le_max_left _ _).trans ((le_add_of_nonneg_left (hu0 s)).trans hw)
    linarith

end TauCeti
