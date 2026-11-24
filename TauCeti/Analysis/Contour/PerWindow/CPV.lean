/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import TauCeti.Analysis.Contour.Chord.QuotientAsymptotics
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.WindowSplitting
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The per-window principal value at a simple pole

At a transverse crossing `γ t₀ = s` with unique crossing on a window `[l, u]`, the
`ε`-truncated integral of the simple-pole integrand `(γ t - s)⁻¹ * deriv γ t` over the window
converges as `ε → 0⁺` (`perWindow_truncated_integral_tendsto`). The window integral
splits at the exit times (`exists_exit_times_truncated_integral_split`); each side integral is
the logarithm of a chord quotient by the logarithmic fundamental theorem of calculus; the
`log ε` real parts of the two sides cancel — both exit radii are exactly `ε` — and the argument
parts converge by the annular argument limits, so the whole expression tends to

  `(log ‖γ u - s‖ - log ‖γ l - s‖) + (arg_R + arg_L) · I`.

The slit-plane hypotheses are taken as inputs rather than derived internally — the caller fixes
the window radius once (for multi-crossing aggregation each crossing supplies a threshold
radius and the minimum is used). The chord-quotient inputs are produced by
`Contour.exists_chord_quotient_mem_slitPlane_right/left`; the tangent-side inputs are supplied
externally by the window-boundary radii.

## Main results

* `Contour.perWindow_truncated_integral_tendsto` — the truncated window integral of the
  simple-pole integrand converges as `ε → 0⁺`, to the log-norm difference of the window
  boundary plus the boundary arguments.

## Provenance

Migrated from `perCrossing_window_integral_tendsto_exact` and its supporting lemmas
(`annular_log_diff_of_window`, `right/left_annular_log_diff_local`, `log_div_re_im_decomp`) of
`LocalCutoffs.lean` in the AINTLIB `LeanModularForms` development, restated for a raw curve on
its crossing window. The truncated-integrability lemma migrated alongside them,
`cpvIntegrand_inv_intervalIntegrable`, lives with the rest of the truncation API in
`Contour.Cauchy.PrincipalValue.Basic` as `intervalIntegrable_inv_sub_truncated`.
See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

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

/-- **Closed form of the truncated window integral at a fixed truncation level.** For points
`τl ∈ Ioo l t₀` and `τr ∈ Ioo t₀ u` at the same distance from `s`, a curve absolutely continuous on
the window `[l, u]`, the anchored slit-plane chord quotients on each side, and the window-split
identity for the `ε`-truncated simple-pole integrand, the truncated window integral equals the
log-norm difference of the window endpoints plus the two boundary chord arguments times `I`. -/
private theorem perWindow_truncated_integral_eq_log_form {γ : ℝ → ℂ} {s : ℂ} {l t₀ u ε : ℝ}
    {τl τr : ℝ} (hγ : AbsolutelyContinuousOnInterval γ l u)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ u → (γ b - s) / (γ a - s) ∈ Complex.slitPlane)
    (h_slit_L : ∀ b, l ≤ b → b < t₀ → (γ b - s) / (γ l - s) ∈ Complex.slitPlane)
    (hτL : τl ∈ Ioo l t₀) (hτR : τr ∈ Ioo t₀ u) (hrad : ‖γ τl - s‖ = ‖γ τr - s‖)
    (hsplit : ∫ v in l..u, (if ‖γ v - s‖ > ε then (γ v - s)⁻¹ * deriv γ v else 0) =
      (∫ v in l..τl, (γ v - s)⁻¹ * deriv γ v) +
      (∫ v in τr..u, (γ v - s)⁻¹ * deriv γ v)) :
    ∫ t in l..u,
        (if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
      ((Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ : ℝ) : ℂ) +
        ((((γ τl - s) / (γ l - s)).arg +
          ((γ u - s) / (γ τr - s)).arg : ℝ) : ℂ) * Complex.I := by
  have hlt : l < t₀ := hτL.1.trans hτL.2
  have htu : t₀ < u := hτR.1.trans hτR.2
  obtain ⟨h_ne_plus, h_ne_R⟩ :=
    div_ne_zero_iff.mp (Complex.slitPlane_ne_zero (h_slit_R τr u hτR.1 hτR.2.le le_rfl))
  obtain ⟨h_ne_L, h_ne_minus⟩ :=
    div_ne_zero_iff.mp (Complex.slitPlane_ne_zero (h_slit_L τl hτL.1.le hτL.2))
  have h_win : l ≤ u := hlt.le.trans htu.le
  rw [hsplit,
    (hγ.mono (uIcc_subset_uIcc (mem_uIcc_of_le le_rfl h_win)
      (mem_uIcc_of_le hτL.1.le (by linarith [hτL.2])))).integral_inv_sub_mul_deriv_eq_log
      fun t ht ↦ h_slit_L t (uIcc_of_le hτL.1.le ▸ ht).1
        (by linarith [(uIcc_of_le hτL.1.le ▸ ht).2, hτL.2]),
    (hγ.mono (uIcc_subset_uIcc (mem_uIcc_of_le (by linarith [hτR.1]) hτR.2.le)
      (mem_uIcc_of_le h_win le_rfl))).integral_inv_sub_mul_deriv_eq_log
      fun t ht ↦ h_slit_R τr t hτR.1 (uIcc_of_le hτR.2.le ▸ ht).1 (uIcc_of_le hτR.2.le ▸ ht).2,
    log_sum_decomp h_ne_minus h_ne_L h_ne_R h_ne_plus hrad]

/-- The sum of the two boundary arguments along the exit times converges to the sum of the
boundary arguments of the one-sided derivative limits. -/
private theorem arg_sum_exitTimes_tendsto {γ : ℝ → ℂ} {s : ℂ} {l t₀ u : ℝ} {L_R L_L : ℂ}
    {τL τR : ℝ → ℝ} (h_at : γ t₀ = s) (h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀)
    (h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀)
    (h_slit_plus : (γ u - s) / L_R ∈ Complex.slitPlane)
    (h_slit_minus : (-L_L) / (γ l - s) ∈ Complex.slitPlane)
    (h_toL : Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_toR : Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀)) :
    Tendsto (fun ε : ℝ =>
      ((γ (τL ε) - s) / (γ l - s)).arg + ((γ u - s) / (γ (τR ε) - s)).arg) (𝓝[>] (0 : ℝ))
      (𝓝 (((-L_L) / (γ l - s)).arg + ((γ u - s) / L_R).arg)) :=
  (tendsto_arg_chord_div_left h_deriv_L h_at h_slit_minus h_toL).add
    (tendsto_arg_div_chord_right h_deriv_R h_at h_slit_plus h_toR)

/-- **The per-window principal value at a simple pole**: at a transverse crossing `γ t₀ = s`
with non-zero one-sided derivative limits, and the slit-plane inputs at the window radius (which
force the crossing to be unique on the window), the `ε`-truncated window integral of
`(γ t - s)⁻¹ * deriv γ t` converges as `ε → 0⁺` to the log-norm difference of the window boundary
plus the two boundary arguments. -/
theorem perWindow_truncated_integral_tendsto {γ : ℝ → ℂ} {s : ℂ} {l t₀ u : ℝ}
    {L_R L_L : ℂ} (hlt : l < t₀) (htu : t₀ < u) (h_at : γ t₀ = s)
    (hγ : AbsolutelyContinuousOnInterval γ l u)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ u → (γ b - s) / (γ a - s) ∈ Complex.slitPlane)
    (h_slit_L : ∀ b, l ≤ b → b < t₀ → (γ b - s) / (γ l - s) ∈ Complex.slitPlane)
    (h_slit_plus : (γ u - s) / L_R ∈ Complex.slitPlane)
    (h_slit_minus : (-L_L) / (γ l - s) ∈ Complex.slitPlane) :
    Tendsto (fun ε : ℝ => ∫ t in l..u,
        if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ : ℝ) : ℂ) +
        ((((-L_L) / (γ l - s)).arg + ((γ u - s) / L_R).arg : ℝ) : ℂ) *
          Complex.I)) := by
  classical
  have hγ_cont : ContinuousOn γ (Icc l u) := uIcc_of_le (hlt.le.trans htu.le) ▸ hγ.continuousOn
  have hderiv_int := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have h_unique : ∀ t ∈ Icc l u, γ t = s → t = t₀ := by
    intro t ht hts
    rcases lt_trichotomy t t₀ with h | h | h
    · exfalso
      have h0 := h_slit_L t ht.1 h
      rw [hts, sub_self, zero_div] at h0
      exact Complex.zero_notMem_slitPlane h0
    · exact h
    · exfalso
      have h0 := h_slit_R t t h le_rfl ht.2
      rw [hts, sub_self, div_zero] at h0
      exact Complex.zero_notMem_slitPlane h0
  have hL_R : L_R ≠ 0 := fun h0 => by
    rw [h0, div_zero] at h_slit_plus
    exact Complex.zero_notMem_slitPlane h_slit_plus
  have hL_L : L_L ≠ 0 := fun h0 => by
    rw [h0, neg_zero, zero_div] at h_slit_minus
    exact Complex.zero_notMem_slitPlane h_slit_minus
  have hγ_at : ContinuousAt γ t₀ :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀ :=
    TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_R
      h_tendsto_R
  have h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀ :=
    TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_L
      h_tendsto_L
  obtain ⟨τL, τR, h_toL, h_toR, h_radL, h_radR, h_memL, h_memR, h_split⟩ :=
    exists_exit_times_truncated_integral_split hlt htu h_at hγ_cont hL_R hL_L
      h_tendsto_R h_tendsto_L h_unique (fun z => (z - s)⁻¹)
      (fun ε hε a b ha hab hb => intervalIntegrable_inv_sub_truncated
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
          exact Icc_subset_Icc (by linarith) (by linarith))) hε)
  have h_ev : (fun ε : ℝ => ∫ t in l..u,
      if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => ((Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ : ℝ) : ℂ) +
        ((((γ (τL ε) - s) / (γ l - s)).arg +
          ((γ u - s) / (γ (τR ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
    filter_upwards [h_split, h_memL, h_memR, h_radL, h_radR] with ε hsplit hτL hτR hradL hradR
    exact perWindow_truncated_integral_eq_log_form hγ h_slit_R h_slit_L hτL hτR
      (hradL.trans hradR.symm) hsplit
  refine Tendsto.congr' h_ev.symm (tendsto_const_nhds.add ?_)
  have h_sum := arg_sum_exitTimes_tendsto h_at h_deriv_R h_deriv_L h_slit_plus h_slit_minus
    h_toL h_toR
  exact ((Complex.continuous_ofReal.tendsto _).comp h_sum).mul tendsto_const_nhds

end TauCeti.Contour

end
