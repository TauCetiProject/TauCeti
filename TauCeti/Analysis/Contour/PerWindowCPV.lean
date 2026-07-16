/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import TauCeti.Analysis.Contour.ChordQuotientAsymptotics
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.WindingNumber
import TauCeti.Analysis.Contour.WindowSplitting
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The per-window principal value at a simple pole

At a transverse crossing `γ t₀ = s` with unique crossing on the window `[t₀ - r, t₀ + r]`, the
`ε`-truncated integral of the simple-pole integrand `(γ t - s)⁻¹ * deriv γ t` over the window
converges as `ε → 0⁺` (`perWindow_truncated_integral_tendsto`). The window integral
splits at the exit times (`exists_exit_times_truncated_integral_split`); each side integral is
the logarithm of a chord quotient by the logarithmic fundamental theorem of calculus; the
`log ε` real parts of the two sides cancel — both exit radii are exactly `ε` — and the argument
parts converge by the annular argument limits, so the whole expression tends to

  `(log ‖γ (t₀ + r) - s‖ - log ‖γ (t₀ - r) - s‖) + (arg_R + arg_L) · I`.

The slit-plane hypotheses are taken as inputs rather than derived internally — the caller fixes
the window radius once (for multi-crossing aggregation each crossing supplies a threshold
radius and the minimum is used). The chord-quotient inputs are produced by
`Contour.exists_chord_quotient_mem_slitPlane_right/left`; the tangent-side inputs are supplied
externally by the window-boundary radii.

## Main results

* `Contour.perWindow_truncated_integral_tendsto` — the truncated window integral of the
  simple-pole integrand converges as `ε → 0⁺`, to the log-norm difference of the window
  boundary plus the boundary arguments.
* `Contour.intervalIntegrable_inv_sub_truncated` — the truncated simple-pole integrand is
  interval-integrable at every truncation level `ε > 0`.

## Provenance

Migrated from `perCrossing_window_integral_tendsto_exact` and its supporting lemmas
(`annular_log_diff_of_window`, `right/left_annular_log_diff_local`, `log_div_re_im_decomp`,
`cpvIntegrand_inv_intervalIntegrable`) of `LocalCutoffs.lean` in the AINTLIB `LeanModularForms`
development, restated for a raw curve on its crossing window. See N. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- The `ε`-truncated simple-pole integrand is interval-integrable: off the `ε`-ball the
integrand is dominated by `(1/ε) · ‖deriv γ‖`. -/
theorem intervalIntegrable_inv_sub_truncated {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have hK_closed : IsClosed {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε} :=
    ((hγ_cont.sub continuousOn_const).norm).preimage_isClosed_of_isClosed
      (by rw [← Icc_min_max]; exact isClosed_Icc) isClosed_Iic
  have h_inv_aesm : AEStronglyMeasurable (fun t => (γ t - s)⁻¹ * deriv γ t)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    have hγ_aem : AEMeasurable γ (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      ((hγ_cont.aestronglyMeasurable (by rw [← Icc_min_max]; exact measurableSet_Icc)
        ).mono_measure (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)).aemeasurable
    exact (((hγ_aem.sub_const s).inv).mul
      (intervalIntegrable_iff.mp hderiv_int).aestronglyMeasurable.aemeasurable
      ).aestronglyMeasurable
  have h_aesm : AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    refine (h_inv_aesm.indicator hK_closed.measurableSet.compl).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    by_cases h_far : ‖γ t - s‖ > ε
    · have h_mem : t ∈ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ :=
        fun hK => absurd hK.2 (not_le.mpr h_far)
      rw [Set.indicator_of_mem h_mem, if_pos h_far]
    · have h_notMem : t ∉ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ := fun hKc =>
        hKc ⟨Set.uIoc_subset_uIcc ht, not_lt.mp h_far⟩
      rw [Set.indicator_of_notMem h_notMem, if_neg h_far]
  refine ((hderiv_int.norm.const_mul (1 / ε)).mono_fun h_aesm ?_)
  refine Eventually.of_forall fun t => ?_
  -- β-reduce the two sides of the a.e. bound
  change ‖if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0‖ ≤ ‖1 / ε * ‖deriv γ t‖‖
  by_cases h_far : ‖γ t - s‖ > ε
  · rw [if_pos h_far, norm_mul, norm_inv]
    calc ‖γ t - s‖⁻¹ * ‖deriv γ t‖
        ≤ (1 / ε) * ‖deriv γ t‖ := by
          rw [inv_eq_one_div]
          exact mul_le_mul_of_nonneg_right
            (one_div_le_one_div_of_le hε h_far.le) (norm_nonneg _)
      _ ≤ ‖1 / ε * ‖deriv γ t‖‖ := le_abs_self _
  · rw [if_neg h_far, norm_zero]
    positivity

/-- The winding integral is the log of the chord quotient on an ordered pole-free interval
with the chord quotients anchored at the left endpoint in the slit plane: the `Icc`-hypothesis
form of `integral_inv_sub_mul_deriv_eq_log`, with the integrability discharged. -/
private theorem integral_inv_sub_mul_deriv_eq_log_window {γ : ℝ → ℂ} {s : ℂ} {P : Set ℝ}
    {l u : ℝ} (hlu : l ≤ u) (hP : P.Countable)
    (hγ_cont : ContinuousOn γ (Icc l u))
    (hγ_diffP : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume l u)
    (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_slit : ∀ t ∈ Icc l u, (γ t - s) / (γ l - s) ∈ Complex.slitPlane) :
    ∫ t in l..u, (γ t - s)⁻¹ * deriv γ t =
      Complex.log ((γ u - s) / (γ l - s)) := by
  have hγ_cont' : ContinuousOn γ (uIcc l u) := by rwa [uIcc_of_le hlu]
  refine integral_inv_sub_mul_deriv_eq_log hP hγ_cont' ?_ ?_ ?_
  · intro t ht
    rw [min_eq_left hlu, max_eq_right hlu] at ht
    exact hγ_diffP t ht
  · intro t ht
    rw [uIcc_of_le hlu] at ht
    exact h_slit t ht
  · refine intervalIntegrable_inv_sub_mul_deriv hγ_cont' (fun t ht => ?_) hderiv_int
    rw [uIcc_of_le hlu] at ht
    exact h_ne t ht

/-- **Real/imaginary decomposition of a sum of two chord logarithms with matching inner
radii**: for nonzero chords with `‖B‖ = ‖C‖`, the inner `log`-radius terms cancel, leaving the
outer log-norm difference plus the argument parts. -/
private theorem log_sum_decomp {A B C D : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hnorm : ‖B‖ = ‖C‖) :
    Complex.log (B / A) + Complex.log (D / C) =
      ((Real.log ‖D‖ - Real.log ‖A‖ : ℝ) : ℂ) +
        (((B / A).arg + (D / C).arg : ℝ) : ℂ) * Complex.I := by
  have h_decomp : ∀ {a b : ℂ}, a ≠ 0 → b ≠ 0 → Complex.log (a / b) =
      ((Real.log ‖a‖ - Real.log ‖b‖ : ℝ) : ℂ) + ((a / b).arg : ℂ) * Complex.I := by
    intro a b ha hb
    refine Complex.ext ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, sub_zero, add_zero]
      rw [Complex.log_re, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_one, Complex.ofReal_re, zero_add]
      rw [Complex.log_im]
      ring
  rw [h_decomp hB hA, h_decomp hD hC, hnorm]
  push_cast
  ring

/-- **The per-window principal value at a simple pole**: at a transverse crossing `γ t₀ = s`
with unique crossing on the window, non-zero one-sided derivative limits, and the slit-plane
inputs at the window radius, the `ε`-truncated window integral of `(γ t - s)⁻¹ * deriv γ t`
converges as `ε → 0⁺` to the log-norm difference of the window boundary plus the two boundary
arguments. -/
theorem perWindow_truncated_integral_tendsto {γ : ℝ → ℂ} {s : ℂ} {t₀ r : ℝ}
    {L_R L_L : ℂ} {P : Set ℝ} (hr_pos : 0 < r) (h_at : γ t₀ = s)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - r) (t₀ + r)))
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_diff_R : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (h_diff_L : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hP : P.Countable)
    (hγ_diffP : ∀ t ∈ Ioo (t₀ - r) (t₀ + r) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume
      (t₀ - r) (t₀ + r))
    (h_unique : ∀ t ∈ Icc (t₀ - r) (t₀ + r), γ t = s → t = t₀)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane)
    (h_slit_L : ∀ b, t₀ - r ≤ b → b < t₀ →
      (γ b - s) / (γ (t₀ - r) - s) ∈ Complex.slitPlane)
    (h_slit_plus : (γ (t₀ + r) - s) / L_R ∈ Complex.slitPlane)
    (h_slit_minus : (-L_L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane) :
    Tendsto (fun ε : ℝ => ∫ t in (t₀ - r)..(t₀ + r),
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.log ‖γ (t₀ + r) - s‖ - Real.log ‖γ (t₀ - r) - s‖ : ℝ) : ℂ) +
        ((((-L_L) / (γ (t₀ - r) - s)).arg + ((γ (t₀ + r) - s) / L_R).arg : ℝ) : ℂ) *
          Complex.I)) := by
  classical
  have hL_R : L_R ≠ 0 := fun h0 => by
    rw [h0, div_zero] at h_slit_plus
    exact Complex.zero_notMem_slitPlane h_slit_plus
  have hL_L : L_L ≠ 0 := fun h0 => by
    rw [h0, neg_zero, zero_div] at h_slit_minus
    exact Complex.zero_notMem_slitPlane h_slit_minus
  have hγ_at : ContinuousAt γ t₀ :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨τL, τR, h_toL, h_toR, h_radL, h_radR, h_memL, h_memR, h_split⟩ :=
    exists_exit_times_truncated_integral_split hr_pos h_at hγ_cont hL_R hL_L
      h_tendsto_R h_tendsto_L h_diff_R h_diff_L h_unique (fun z => (z - s)⁻¹)
      (fun ε hε a b ha hab hb => intervalIntegrable_inv_sub_truncated
        (hγ_cont.mono (by
          rw [uIcc_of_le hab]
          exact Icc_subset_Icc (by linarith) (by linarith)))
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
          exact Icc_subset_Icc (by linarith) (by linarith))) hε)
  have hδR_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < τR ε - t₀ :=
    h_memR.mono fun ε hε => by linarith [hε.1]
  have hδL_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t₀ - τL ε :=
    h_memL.mono fun ε hε => by linarith [hε.2]
  have hδR_to : Tendsto (fun ε => τR ε - t₀) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (h_toR.mono_right nhdsWithin_le_nhds).sub_const t₀,
      hδR_pos.mono fun ε hε => mem_Ioi.mpr hε⟩
  have hδL_to : Tendsto (fun ε => t₀ - τL ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (h_toL.mono_right nhdsWithin_le_nhds).const_sub t₀,
      hδL_pos.mono fun ε hε => mem_Ioi.mpr hε⟩
  have h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀ :=
    TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv hγ_at h_diff_R h_tendsto_R
  have h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀ :=
    TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv hγ_at h_diff_L h_tendsto_L
  have h_argR : Tendsto (fun ε : ℝ => Complex.arg ((γ (t₀ + r) - s) / (γ (τR ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L_R).arg) :=
    (arg_annular_quotient_tendsto_right h_deriv_R h_at h_slit_plus hδR_pos hδR_to).congr
      fun ε => by rw [show t₀ + (τR ε - t₀) = τR ε from by ring]
  have h_argL : Tendsto (fun ε : ℝ => Complex.arg ((γ (τL ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L) / (γ (t₀ - r) - s)).arg) :=
    (arg_annular_quotient_tendsto_left h_deriv_L h_at h_slit_minus hδL_pos hδL_to).congr
      fun ε => by rw [show t₀ - (t₀ - τL ε) = τL ε from by ring]
  have h_ne_plus : γ (t₀ + r) - s ≠ 0 := sub_ne_zero.mpr fun h_eq =>
    absurd (h_unique _ (right_mem_Icc.mpr (by linarith)) h_eq) (by linarith)
  have h_ne_minus : γ (t₀ - r) - s ≠ 0 := sub_ne_zero.mpr fun h_eq =>
    absurd (h_unique _ (left_mem_Icc.mpr (by linarith)) h_eq) (by linarith)
  have h_ev : (fun ε : ℝ => ∫ t in (t₀ - r)..(t₀ + r),
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ((Real.log ‖γ (t₀ + r) - s‖ - Real.log ‖γ (t₀ - r) - s‖ : ℝ) : ℂ) +
        ((((γ (τL ε) - s) / (γ (t₀ - r) - s)).arg +
          ((γ (t₀ + r) - s) / (γ (τR ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
    filter_upwards [h_split, h_memL, h_memR, h_radL, h_radR, self_mem_nhdsWithin]
      with ε hsplit hτL hτR hradL hradR hε_pos
    have h_ne_L : γ (τL ε) - s ≠ 0 := by
      rw [← norm_pos_iff, hradL]
      exact hε_pos
    have h_ne_R : γ (τR ε) - s ≠ 0 := by
      rw [← norm_pos_iff, hradR]
      exact hε_pos
    rw [hsplit,
      integral_inv_sub_mul_deriv_eq_log_window hτL.1.le hP
        (hγ_cont.mono (Icc_subset_Icc le_rfl (by linarith [hτL.2])))
        (fun t ht => hγ_diffP t ⟨⟨ht.1.1, by linarith [ht.1.2, hτL.2]⟩, ht.2⟩)
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hτL.1.le, uIcc_of_le (show t₀ - r ≤ t₀ + r by linarith)]
          exact Icc_subset_Icc le_rfl (by linarith [hτL.2])))
        (fun t ht h_eq => absurd (h_unique t
          ⟨by linarith [ht.1], by linarith [ht.2, hτL.2]⟩ h_eq)
          (by linarith [ht.2, hτL.2]))
        (fun t ht => h_slit_L t ht.1 (by linarith [ht.2, hτL.2])),
      integral_inv_sub_mul_deriv_eq_log_window hτR.2.le hP
        (hγ_cont.mono (Icc_subset_Icc (by linarith [hτR.1]) le_rfl))
        (fun t ht => hγ_diffP t ⟨⟨by linarith [ht.1.1, hτR.1], ht.1.2⟩, ht.2⟩)
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hτR.2.le, uIcc_of_le (show t₀ - r ≤ t₀ + r by linarith)]
          exact Icc_subset_Icc (by linarith [hτR.1]) le_rfl))
        (fun t ht h_eq => absurd (h_unique t
          ⟨by linarith [ht.1, hτR.1], by linarith [ht.2]⟩ h_eq)
          (by linarith [ht.1, hτR.1]))
        (fun t ht => h_slit_R (τR ε) t hτR.1 ht.1 ht.2),
      log_sum_decomp h_ne_minus h_ne_L h_ne_R h_ne_plus (by rw [hradL, hradR])]
  refine Tendsto.congr' h_ev.symm (tendsto_const_nhds.add ?_)
  have h_sum : Tendsto (fun ε : ℝ =>
      ((γ (τL ε) - s) / (γ (t₀ - r) - s)).arg +
        ((γ (t₀ + r) - s) / (γ (τR ε) - s)).arg) (𝓝[>] (0 : ℝ))
      (𝓝 (((-L_L) / (γ (t₀ - r) - s)).arg + ((γ (t₀ + r) - s) / L_R).arg)) :=
    h_argL.add h_argR
  exact ((Complex.continuous_ofReal.tendsto _).comp h_sum).mul tendsto_const_nhds

end TauCeti.Contour

end
