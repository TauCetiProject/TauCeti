/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import TauCeti.Analysis.Contour.HigherOrder.Asymptotics
import TauCeti.Analysis.Contour.SectorCancellation
import TauCeti.Analysis.Contour.WindowSplitting
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The per-window principal value at a higher-order pole

At a transverse crossing `γ t_i = s` that is flat of order `n ≥ k ≥ 2` and satisfies the
condition-(B) power identity, the `ε`-truncated window integral of the order-`k` polar term
`(c / (z - s)^k)` along the curve converges as `ε → 0⁺` to the boundary difference of its
antiderivative `F z = -(k-1)⁻¹ (z - s)^{-(k-1)}`:

  `∫ window, truncated → c · (F (γ (t_i + r)) - F (γ (t_i - r)))`.

The window integral splits at the exit times (`exists_exit_times_truncated_integral_split`);
each side integral evaluates by the fundamental theorem of calculus to a boundary difference of
`c · F ∘ γ`, and the two inner exit-time terms cancel in the limit by the sector-even
cancellation (`antiderivative_diff_across_crossing_tendsto_zero`) — the mechanism of
Hungerbühler–Wasem condition (B) at a higher-order pole.

Of the curve's regularity, the window lemma asks absolute continuity on the window, which is what
`Contour.integral_pow_inv_mul_deriv_eq_sub` needs on each side of the crossing. Its other
hypotheses are conditions at the crossing: nonzero one-sided tangent limits, flatness of order `n`,
condition (B), and a unique crossing in the window.

## Main results

* `Contour.perWindow_higherOrder_truncated_integral_tendsto` — the truncated window integral
  of the order-`k` polar term converges, with the explicit boundary-difference value.

## Provenance

Migrated from `perCrossing_higherOrder_window_integral_tendsto_corner` of `MultiCrossingCPV.lean`
in the AINTLIB `LeanModularForms` development, restated for a raw curve on its crossing window.
The truncated-integrability lemma migrated alongside it,
`cpvIntegrand_higherOrder_intervalIntegrable`, lives with the rest of the truncation API in
`Contour.Cauchy.PrincipalValue.Basic` as `intervalIntegrable_pow_inv_mul_deriv_truncated`, and the
fundamental theorem of calculus it uses, `antiderivPow_FTC_on_avoiding` there, is
`Contour.integral_pow_inv_mul_deriv_eq_sub` in `HigherOrder/Asymptotics.lean`. The source asks for
a curve that is continuous and differentiable off a countable set with integrable derivative on
the window; here the curve is absolutely continuous there, which covers that case
(`ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable`).
See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **Antiderivative evaluation on a subinterval missing the crossing.** On a subinterval
`[l, u]` of the window `[t_i - r, t_i + r]`, where the curve meets `s` only at `t_i` and
`t_i ∉ [l, u]`, the higher-order integrand integrates to the difference of antiderivative values
at the endpoints. The two pieces a truncated window integral splits into — left of the entry time
and right of the exit time — are both instances. -/
private lemma integral_pow_inv_mul_deriv_eq_sub_of_subinterval {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    {k : ℕ} (hk : 2 ≤ k) (c : ℂ) (hγ : AbsolutelyContinuousOnInterval γ (t_i - r) (t_i + r))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    {l u : ℝ} (hlu : l ≤ u) (hl : t_i - r ≤ l) (hu : u ≤ t_i + r) (h_excl : t_i ∉ Icc l u) :
    ∫ t in l..u, c / (γ t - s) ^ k * deriv γ t =
      c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ l - s) ^ (k - 1))⁻¹) := by
  have hsub : uIcc l u ⊆ uIcc (t_i - r) (t_i + r) :=
    uIcc_subset_uIcc (mem_uIcc_of_le hl (hlu.trans hu)) (mem_uIcc_of_le (hl.trans hlu) hu)
  refine integral_pow_inv_mul_deriv_eq_sub hk c (hγ.mono hsub) fun t ht h_eq => ?_
  rw [uIcc_of_le hlu] at ht
  exact h_excl (h_unique t ⟨hl.trans ht.1, ht.2.trans hu⟩ h_eq ▸ ht)

/-- **The per-window principal value at a higher-order pole**: for a curve absolutely continuous
on the window, at a transverse crossing `γ t_i = s`, flat of order `n ≥ k ≥ 2` and satisfying the
condition-(B) power identity, with unique crossing on the window, the `ε`-truncated window
integral of the order-`k` polar term `c / (z - s)^k` converges as `ε → 0⁺` to the boundary
difference of its antiderivative. -/
theorem perWindow_higherOrder_truncated_integral_tendsto {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    {L_R L_L : ℂ} {n k : ℕ} (hr_pos : 0 < r) (h_at : γ t_i = s)
    (hγ : AbsolutelyContinuousOnInterval γ (t_i - r) (t_i + r)) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t_i) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t_i) (𝓝 L_L))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    (h_flat : FlatOfOrder γ t_i n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_B : (L_R / (‖L_R‖ : ℂ)) ^ (k - 1) = ((-L_L) / (‖L_L‖ : ℂ)) ^ (k - 1)) (c : ℂ) :
    Tendsto (fun ε : ℝ => ∫ t in (t_i - r)..(t_i + r),
        if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹))) := by
  classical
  have hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r)) :=
    uIcc_of_le (by linarith : t_i - r ≤ t_i + r) ▸ hγ.continuousOn
  have hderiv_int := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hγ_at : ContinuousAt γ t_i :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have h_deriv_R : HasDerivWithinAt γ L_R (Ioi t_i) t_i :=
    TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_R
      h_tendsto_R
  have h_deriv_L : HasDerivWithinAt γ L_L (Iio t_i) t_i :=
    TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_L
      h_tendsto_L
  obtain ⟨τL, τR, h_toL, h_toR, h_radL, h_radR, h_memL, h_memR, h_split⟩ :=
    exists_exit_times_truncated_integral_split (by linarith) (by linarith) h_at hγ_cont hL_R hL_L
      h_tendsto_R h_tendsto_L h_unique (fun z => c / (z - s) ^ k)
      (fun ε hε a b ha hab hb => intervalIntegrable_pow_inv_mul_deriv_truncated c k
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
          exact Icc_subset_Icc ha hb)) hε)
  have h_cancel := antiderivative_diff_across_crossing_tendsto_zero h_flat hL_L hL_R
    h_deriv_R h_deriv_L h_at hkn h_B h_toR h_radR h_toL h_radL
  have h_cancel_cx : Tendsto (fun ε =>
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr h_cancel
  have h_ev : (fun ε : ℝ => ∫ t in (t_i - r)..(t_i + r),
      if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
          c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) +
        c * ((-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
          (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹)) := by
    filter_upwards [h_split, h_memL, h_memR] with ε hsplit hτL hτR
    rw [hsplit,
      integral_pow_inv_mul_deriv_eq_sub_of_subinterval hk c hγ h_unique
        hτL.1.le le_rfl (by linarith [hτL.2]) (fun h => absurd h.2 (by linarith [hτL.2])),
      integral_pow_inv_mul_deriv_eq_sub_of_subinterval hk c hγ h_unique
        hτR.2.le (by linarith [hτR.1]) le_rfl (fun h => absurd h.1 (by linarith [hτR.1]))]
    ring
  refine Tendsto.congr' h_ev.symm ?_
  simpa using tendsto_const_nhds.add (h_cancel_cx.const_mul c)

end TauCeti.Contour

end
