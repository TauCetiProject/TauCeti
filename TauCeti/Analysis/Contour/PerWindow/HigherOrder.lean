/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import TauCeti.Analysis.Contour.HigherOrder.Asymptotics
import TauCeti.Analysis.Contour.SectorCancellation
import TauCeti.Analysis.Contour.WindowSplitting
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

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

## Main results

* `Contour.perWindow_higherOrder_truncated_integral_tendsto` — the truncated window integral
  of the order-`k` polar term converges, with the explicit boundary-difference value.
* `Contour.integral_pow_inv_mul_deriv_eq_sub` — the fundamental theorem of calculus for the
  order-`k` polar term along the curve, on an interval avoiding the pole.
* `Contour.intervalIntegrable_pow_inv_mul_deriv_truncated` — the truncated order-`k` polar
  integrand is interval-integrable at every truncation level `ε > 0`.

## Provenance

Migrated from `perCrossing_higherOrder_window_integral_tendsto_corner` and its supporting
lemmas (`pow_inv_mul_deriv_intervalIntegrable`, `cpvIntegrand_higherOrder_intervalIntegrable`,
`antiderivPow_FTC_on_avoiding`) of `MultiCrossingCPV.lean` in the AINTLIB `LeanModularForms`
development, restated for a raw curve on its crossing window. See N. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- The order-`k` polar integrand is interval-integrable off the pole: the polar factor is
continuous there. -/
private theorem intervalIntegrable_pow_inv_mul_deriv {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    (c : ℂ) (k : ℕ) (hlu : l ≤ u) (hγ_cont : ContinuousOn γ (Icc l u))
    (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume l u) :
    IntervalIntegrable (fun t => c / (γ t - s) ^ k * deriv γ t)
      MeasureTheory.volume l u := by
  refine hderiv_int.continuousOn_mul ?_
  rw [uIcc_of_le hlu]
  exact continuousOn_const.div ((hγ_cont.sub continuousOn_const).pow k)
    fun t ht => pow_ne_zero k (sub_ne_zero.mpr (h_ne t ht))

/-- The `ε`-truncated order-`k` polar integrand is interval-integrable: off the `ε`-ball it is
dominated by `(‖c‖ / ε^k) · ‖deriv γ‖`. -/
theorem intervalIntegrable_pow_inv_mul_deriv_truncated {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    (c : ℂ) (k : ℕ) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have hK_closed : IsClosed {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε} :=
    ((hγ_cont.sub continuousOn_const).norm).preimage_isClosed_of_isClosed
      (by rw [← Icc_min_max]; exact isClosed_Icc) isClosed_Iic
  have h_fn_aesm : AEStronglyMeasurable (fun t => c / (γ t - s) ^ k * deriv γ t)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    have hγ_aem : AEMeasurable γ (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      ((hγ_cont.aestronglyMeasurable (by rw [← Icc_min_max]; exact measurableSet_Icc)
        ).mono_measure (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)).aemeasurable
    have h1 : AEMeasurable (fun t => c / (γ t - s) ^ k)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      (((hγ_aem.sub_const s).pow_const k).inv.const_mul c).congr
        (Eventually.of_forall fun t => (div_eq_mul_inv c _).symm)
    exact (h1.mul
      (intervalIntegrable_iff.mp hderiv_int).aestronglyMeasurable.aemeasurable
      ).aestronglyMeasurable
  have h_aesm : AEStronglyMeasurable
      (fun t => if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    refine (h_fn_aesm.indicator hK_closed.measurableSet.compl).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    by_cases h_far : ‖γ t - s‖ > ε
    · have h_mem : t ∈ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ :=
        fun hK => absurd hK.2 (not_le.mpr h_far)
      rw [Set.indicator_of_mem h_mem, if_pos h_far]
    · have h_notMem : t ∉ {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε}ᶜ := fun hKc =>
        hKc ⟨Set.uIoc_subset_uIcc ht, not_lt.mp h_far⟩
      rw [Set.indicator_of_notMem h_notMem, if_neg h_far]
  refine intervalIntegrable_truncated_mul_deriv (f := fun z => c / (z - s) ^ k)
    (M := ‖c‖ / ε ^ k) hderiv_int h_aesm fun t h_far => ?_
  rw [norm_div, norm_pow]
  gcongr

/-- The fundamental theorem of calculus for the order-`k` polar term along the curve, on an
interval avoiding the pole: the integral is the boundary difference of the antiderivative
`c · (-(k-1)⁻¹ (· - s)^{-(k-1)}) ∘ γ`. -/
theorem integral_pow_inv_mul_deriv_eq_sub {γ : ℝ → ℂ} {s : ℂ} {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    {l u : ℝ} (hlu : l ≤ u) {P : Set ℝ} (hP : P.Countable)
    (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_diff : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousOn γ (Icc l u))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume l u) :
    ∫ t in l..u, c / (γ t - s) ^ k * deriv γ t =
      c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ l - s) ^ (k - 1))⁻¹) := by
  have h_G_deriv : ∀ t ∈ Ioo l u \ P,
      HasDerivAt (fun v => c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ v - s) ^ (k - 1))⁻¹))
        (c / (γ t - s) ^ k * deriv γ t) t := by
    intro t ht
    have h_F := (hasDerivAt_antiderivative_pow_inv hk
      (h_ne t (Ioo_subset_Icc_self ht.1))).const_mul c
    have h_chain := h_F.comp t (h_diff t ht).hasDerivAt
    rwa [show c * (1 / (γ t - s) ^ k) * deriv γ t =
        c / (γ t - s) ^ k * deriv γ t from by ring] at h_chain
  have h_G_cont : ContinuousOn
      (fun v => c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ v - s) ^ (k - 1))⁻¹)) (Icc l u) := fun t ht =>
    (((hasDerivAt_antiderivative_pow_inv hk (h_ne t ht)).continuousAt).const_mul
      c).comp_continuousWithinAt (hγ_cont t ht)
  exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hlu hP h_G_cont
    h_G_deriv (intervalIntegrable_pow_inv_mul_deriv c k hlu hγ_cont h_ne hderiv_int)

/-- **The per-window principal value at a higher-order pole**: at a transverse crossing
`γ t_i = s`, flat of order `n ≥ k ≥ 2` and satisfying the condition-(B) power identity, with
unique crossing on the window, the `ε`-truncated window integral of the order-`k` polar term
`c / (z - s)^k` converges as `ε → 0⁺` to the boundary difference of its antiderivative. -/
theorem perWindow_higherOrder_truncated_integral_tendsto {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    {L_R L_L : ℂ} {n k : ℕ} {P : Set ℝ} (hr_pos : 0 < r) (h_at : γ t_i = s)
    (hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r)))
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t_i) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t_i) (𝓝 L_L))
    (h_diff_R : ∀ᶠ t in 𝓝[>] t_i, DifferentiableAt ℝ γ t)
    (h_diff_L : ∀ᶠ t in 𝓝[<] t_i, DifferentiableAt ℝ γ t)
    (hP : P.Countable)
    (hγ_diffP : ∀ t ∈ Ioo (t_i - r) (t_i + r) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume
      (t_i - r) (t_i + r))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    (h_flat : FlatOfOrder γ t_i n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_B : (L_R / (‖L_R‖ : ℂ)) ^ (k - 1) = ((-L_L) / (‖L_L‖ : ℂ)) ^ (k - 1))
    (c : ℂ) :
    Tendsto (fun ε : ℝ => ∫ t in (t_i - r)..(t_i + r),
        if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹))) := by
  classical
  have hγ_at : ContinuousAt γ t_i :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have h_deriv_R : HasDerivWithinAt γ L_R (Ioi t_i) t_i :=
    TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv hγ_at h_diff_R h_tendsto_R
  have h_deriv_L : HasDerivWithinAt γ L_L (Iio t_i) t_i :=
    TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv hγ_at h_diff_L h_tendsto_L
  obtain ⟨τL, τR, h_toL, h_toR, h_radL, h_radR, h_memL, h_memR, h_split⟩ :=
    exists_exit_times_truncated_integral_split hr_pos h_at hγ_cont hL_R hL_L
      h_tendsto_R h_tendsto_L h_diff_R h_diff_L h_unique (fun z => c / (z - s) ^ k)
      (fun ε hε a b ha hab hb => intervalIntegrable_pow_inv_mul_deriv_truncated c k
        (hγ_cont.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
          exact Icc_subset_Icc ha hb)) hε)
  have h_cancel := antiderivative_diff_across_crossing_tendsto_zero h_flat hL_L hL_R
    h_deriv_R h_deriv_L h_at hk hkn h_B h_toR h_radR h_toL h_radL
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
    have h_ne_left : ∀ t ∈ Icc (t_i - r) (τL ε), γ t ≠ s := fun t ht h_eq => by
      have := h_unique t ⟨ht.1, by linarith [ht.2, hτL.2]⟩ h_eq
      linarith [ht.2, hτL.2, this]
    have h_ne_right : ∀ t ∈ Icc (τR ε) (t_i + r), γ t ≠ s := fun t ht h_eq => by
      have := h_unique t ⟨by linarith [ht.1, hτR.1], ht.2⟩ h_eq
      linarith [ht.1, hτR.1, this]
    rw [hsplit,
      integral_pow_inv_mul_deriv_eq_sub hk c hτL.1.le hP
        (fun t ht => h_ne_left t ht)
        (fun t ht => hγ_diffP t ⟨⟨ht.1.1, by linarith [ht.1.2, hτL.2]⟩, ht.2⟩)
        (hγ_cont.mono (Icc_subset_Icc le_rfl (by linarith [hτL.2])))
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hτL.1.le, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
          exact Icc_subset_Icc le_rfl (by linarith [hτL.2]))),
      integral_pow_inv_mul_deriv_eq_sub hk c hτR.2.le hP
        (fun t ht => h_ne_right t ht)
        (fun t ht => hγ_diffP t ⟨⟨by linarith [ht.1.1, hτR.1], ht.1.2⟩, ht.2⟩)
        (hγ_cont.mono (Icc_subset_Icc (by linarith [hτR.1]) le_rfl))
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hτR.2.le, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
          exact Icc_subset_Icc (by linarith [hτR.1]) le_rfl))]
    ring
  refine Tendsto.congr' h_ev.symm ?_
  have h_lim : Tendsto (fun ε =>
      (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) +
      c * ((-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) + c * 0)) :=
    tendsto_const_nhds.add (h_cancel_cx.const_mul c)
  simpa using h_lim

end TauCeti.Contour

end
