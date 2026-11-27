/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# A Grönwall inequality for a pair of functions, with `cosh` and `sinh`

Let `k ≥ 0` be integrable on `[a, b]` and write `L(s) = ∫ₛᵇ k`. If two continuous functions
satisfy `A(s) ≤ 1 + ∫ₛᵇ k B` and `B(s) ≤ ∫ₛᵇ k A` on `[a, b]`, then `A(s) ≤ cosh L(s)` and
`B(s) ≤ sinh L(s)` (`TauCeti.le_cosh_and_le_sinh_of_le_integral`). The comparison functions solve
the equalities: `cosh L(s) = 1 + ∫ₛᵇ k sinh L` and `sinh L(s) = ∫ₛᵇ k cosh L`
(`TauCeti.cosh_integral_eq_one_add_integral`, `TauCeti.sinh_integral_eq_integral`).

This is the comparison behind the bounds `|a| ≤ cosh ∫|q|` and `|b| ≤ sinh ∫|q|` of the scattering
functions of a Dirac system; Grönwall's inequality for the sum `A + B` only gives `exp ∫ k`.

## Implementation notes

The identities are the fundamental theorem of calculus for the absolutely continuous functions
`cosh ∘ L` and `sinh ∘ L`. For the inequality, the positive parts `u⁺` and `v⁺` of
`u = A - cosh L` and `v = B - sinh L` satisfy `u⁺ + v⁺ ≤ ∫ₛᵇ k (u⁺ + v⁺)`, so they vanish by the
backward form of Grönwall's inequality, `TauCeti.le_mul_exp_integral_of_le_add_integral_mul_rev`.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {k : ℝ → ℝ} {a b : ℝ}

/-- The function `s ↦ ∫ₛᵇ k` has derivative `-k s` at almost every `s ∈ [a, b]`, and is
absolutely continuous on `[a, b]`. -/
private theorem integral_right_props (hk : IntegrableOn k (Icc a b)) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun s ↦ ∫ r in s..b, k r) a b ∧
      ∀ᵐ s, s ∈ uIcc a b → HasDerivAt (fun s ↦ ∫ r in s..b, k r) (-k s) s := by
  have hki : IntervalIntegrable k volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hk
  have hb : b ∈ uIcc a b := right_mem_uIcc
  have heq : (fun s ↦ ∫ r in s..b, k r) = fun s ↦ -∫ r in b..s, k r := by
    ext s; rw [integral_symm]
  rw [heq]
  refine ⟨(hki.absolutelyContinuousOnInterval_intervalIntegral' hb).neg, ?_⟩
  filter_upwards [hki.ae_hasDerivAt_integral] with s hs hmem
  exact (hs hmem b hb).neg

/-- If `k` is integrable on `[a, b]` and `φ` is `C¹` with derivative `φ'`, then
`φ(L(s)) = φ(0) + ∫ₛᵇ k φ'(L)` for `L(s) = ∫ₛᵇ k` and `s ∈ [a, b]`. -/
private theorem comp_integral_eq_add_integral (hk : IntegrableOn k (Icc a b)) {φ φ' : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφ' : ∀ x, HasDerivAt φ (φ' x) x) {s : ℝ} (hs : s ∈ Icc a b) :
    φ (∫ r in s..b, k r) = φ 0 + ∫ r in s..b, k r * φ' (∫ u in r..b, k u) := by
  have hab : a ≤ b := hs.1.trans hs.2
  obtain ⟨hac, hder⟩ := integral_right_props hk hab
  have hac' : AbsolutelyContinuousOnInterval (φ ∘ fun s ↦ ∫ r in s..b, k r) s b :=
    (hac.mono (uIcc_subset_uIcc (mem_uIcc_of_le hs.1 hs.2) right_mem_uIcc)).comp_of_contDiffAt
      fun x _ ↦ hφ.contDiffAt
  have hint := hac'.integral_eq_sub_of_ae_hasDerivAt
    (V := fun r ↦ φ' (∫ u in r..b, k u) * -k r) ?_
  · simp only [Function.comp_apply, integral_same] at hint
    rw [← sub_eq_iff_eq_add', ← neg_sub, ← hint, ← intervalIntegral.integral_neg]
    congr 1
    ext r
    ring
  · filter_upwards [hder] with r hr hmem
    exact (hφ' _).comp r (hr (uIcc_subset_uIcc (mem_uIcc_of_le hs.1 hs.2) right_mem_uIcc
      (uIoc_subset_uIcc hmem)))

/-- **The `cosh` identity.** For `k` integrable on `[a, b]` and `s ∈ [a, b]`,
`cosh (∫ₛᵇ k) = 1 + ∫ₛᵇ k(r) sinh (∫ᵣᵇ k) dr`. -/
theorem cosh_integral_eq_one_add_integral (hk : IntegrableOn k (Icc a b)) {s : ℝ}
    (hs : s ∈ Icc a b) :
    Real.cosh (∫ r in s..b, k r) = 1 + ∫ r in s..b, k r * Real.sinh (∫ u in r..b, k u) := by
  simpa using comp_integral_eq_add_integral hk Real.contDiff_cosh Real.hasDerivAt_cosh hs

/-- **The `sinh` identity.** For `k` integrable on `[a, b]` and `s ∈ [a, b]`,
`sinh (∫ₛᵇ k) = ∫ₛᵇ k(r) cosh (∫ᵣᵇ k) dr`. -/
theorem sinh_integral_eq_integral (hk : IntegrableOn k (Icc a b)) {s : ℝ} (hs : s ∈ Icc a b) :
    Real.sinh (∫ r in s..b, k r) = ∫ r in s..b, k r * Real.cosh (∫ u in r..b, k u) := by
  simpa using comp_integral_eq_add_integral hk Real.contDiff_sinh Real.hasDerivAt_sinh hs

/-- Products of `k` with functions continuous on `[a, b]` are interval integrable on `[s, b]`. -/
private theorem intervalIntegrable_mul (hk : IntegrableOn k (Icc a b)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {s : ℝ} (hs : s ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ k r * f r) volume s b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).2
    ((hk.mul_continuousOn hf isCompact_Icc).mono_set (Icc_subset_Icc_left hs.1))

/-- One step of the comparison: if `A(s) ≤ c + ∫ₛᵇ k B` and `F(s) = c + ∫ₛᵇ k G`, then
`A(s) - F(s) ≤ ∫ₛᵇ k (B - G)⁺`. -/
private theorem sub_le_integral_max (hk : IntegrableOn k (Icc a b)) (hk0 : ∀ r, 0 ≤ k r)
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
    _ ≤ ∫ r in s..b, k r * max (B r - G r) 0 :=
        intervalIntegral.integral_mono_on hs.2 (intervalIntegrable_mul hk (hB.sub hG) hs)
          (intervalIntegrable_mul hk (ContinuousOn.sup (hB.sub hG) continuousOn_const) hs)
          fun r _ ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (hk0 r)

/-- **Grönwall's inequality for a pair, with `cosh` and `sinh`.** Let `k ≥ 0` be integrable on
`[a, b]`, and let `A`, `B` be continuous on `[a, b]` with `A(s) ≤ 1 + ∫ₛᵇ k B` and
`B(s) ≤ ∫ₛᵇ k A` for `s ∈ [a, b]`. Then `A(s) ≤ cosh (∫ₛᵇ k)` and `B(s) ≤ sinh (∫ₛᵇ k)`. -/
theorem le_cosh_and_le_sinh_of_le_integral (hk : IntegrableOn k (Icc a b)) (hk0 : ∀ r, 0 ≤ k r)
    {A B : ℝ → ℝ} (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hAB : ∀ s ∈ Icc a b, A s ≤ 1 + ∫ r in s..b, k r * B r)
    (hBA : ∀ s ∈ Icc a b, B s ≤ ∫ r in s..b, k r * A r) {s : ℝ} (hs : s ∈ Icc a b) :
    A s ≤ Real.cosh (∫ r in s..b, k r) ∧ B s ≤ Real.sinh (∫ r in s..b, k r) := by
  have hab : a ≤ b := hs.1.trans hs.2
  set L : ℝ → ℝ := fun s ↦ ∫ r in s..b, k r
  have hLc : ContinuousOn L (Icc a b) := by
    simpa [uIcc_of_le hab] using (integral_right_props hk hab).1.continuousOn
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
      0 ≤ ∫ r in s..b, k r * f r :=
    intervalIntegral.integral_nonneg hs.2 fun r _ ↦ mul_nonneg (hk0 r) (hf r)
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
  have hw := le_mul_exp_integral_of_le_add_integral_mul_rev hk (ae_of_all _ fun r ↦ hk0 r)
    (hk.mul_continuousOn (huc.add hvc) isCompact_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ key)) hs (key s hs)
  rw [zero_mul] at hw
  constructor
  · have := (le_max_left _ _).trans ((le_add_of_nonneg_right (hv0 s)).trans hw)
    linarith
  · have := (le_max_left _ _).trans ((le_add_of_nonneg_left (hu0 s)).trans hw)
    linarith

end TauCeti
