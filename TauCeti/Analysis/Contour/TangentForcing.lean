/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.ChordTangentBound
public import TauCeti.Analysis.Contour.RegularityConditions
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Tangent forcing: flatness bounds the deviation against the tangent

`Contour.FlatOfOrder γ t₀ n` bounds the perpendicular deviation of the curve against **some**
non-zero one-sided witness directions. This file shows the witnesses are forced onto the actual
one-sided tangents: if `γ` has one-sided derivative `L ≠ 0` and is flat of order `n ≥ 1`, the
flatness direction is a real multiple of `L`, so the deviation bound transfers to `L` itself —
the exact hypothesis the higher-order antiderivative asymptotics
(`Contour.antiderivative_diff_at_tangent_target_tendsto_zero_right` / `_left`) consume.

## Main results

* `Contour.FlatOfOrder.tangentDeviation_isLittleO_right` — from flatness of order `n ≥ 1` and a
  right derivative `L ≠ 0`, the deviation against `L` is `o(‖γ t - γ t₀‖ ^ n)` from the right.
* `Contour.FlatOfOrder.tangentDeviation_isLittleO_left` — the left counterpart.

## Provenance

New to the raw-curve development: the AINTLIB `LeanModularForms` flatness structure
(`IsFlatOfOrder`) is indexed by the tangent, so no forcing step was needed there; the roadmap's
`Contour.FlatOfOrder` quantifies its witness directions existentially, and this file supplies
the bridge. The forcing argument is the standard one: the curve leaves `t₀` tangent to `L`, so a
line it hugs to first order can only be `ℝ • L`. See N. Hungerbühler, M. Wasem, *Non-integer
valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Filter Set Topology

/-- The forcing core (right side): a flatness deviation bound of order `n ≥ 1` against `v ≠ 0`,
together with a right derivative `L`, forces `Im(L · conj v) = 0` — the flatness direction and
the tangent are colinear. -/
private theorem im_mul_conj_eq_zero_of_flat_right {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n)
    (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  -- it suffices that c ≤ ε for every ε > 0
  have hc_le : ∀ ε : ℝ, 0 < ε → c ≤ ε := by
    intro ε hε
    have herr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[𝓝[>] t₀] (fun t => t - t₀) :=
      hasDerivWithinAt_iff_isLittleO.mp h_deriv
    -- ‖γ t - γ t₀‖ ≤ (‖L‖ + 1) * (t - t₀) eventually
    have h_growth : ∀ᶠ t in 𝓝[>] t₀, ‖γ t - γ t₀‖ ≤ (‖L‖ + 1) * (t - t₀) := by
      filter_upwards [herr.bound one_pos, self_mem_nhdsWithin] with t hb ht
      have ht' : 0 < t - t₀ := sub_pos.mpr ht
      have h1 : ‖γ t - γ t₀‖ ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
        simpa using norm_add_le ((t - t₀) • L) (γ t - γ t₀ - (t - t₀) • L)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht'] at h1
      rw [Real.norm_eq_abs, abs_of_pos ht'] at hb
      calc ‖γ t - γ t₀‖ ≤ (t - t₀) * ‖L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := h1
        _ ≤ (t - t₀) * ‖L‖ + 1 * (t - t₀) := by linarith
        _ = (‖L‖ + 1) * (t - t₀) := by ring
    -- ‖γ t - γ t₀‖ ^ n ≤ C * (t - t₀) eventually, C := (‖L‖ + 1) ^ n
    have h_pow : ∀ᶠ t in 𝓝[>] t₀, ‖γ t - γ t₀‖ ^ n ≤ (‖L‖ + 1) ^ n * (t - t₀) := by
      have h_small : ∀ᶠ t in 𝓝[>] t₀, t - t₀ ≤ 1 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (eventually_le_nhds (by linarith : t₀ < t₀ + 1))] with t ht
        linarith
      filter_upwards [h_growth, h_small, self_mem_nhdsWithin] with t hg hs ht
      have ht' : 0 < t - t₀ := sub_pos.mpr ht
      calc ‖γ t - γ t₀‖ ^ n ≤ ((‖L‖ + 1) * (t - t₀)) ^ n := by gcongr
        _ = (‖L‖ + 1) ^ n * (t - t₀) ^ n := by rw [mul_pow]
        _ ≤ (‖L‖ + 1) ^ n * (t - t₀) := by
            gcongr
            exact pow_le_of_le_one ht'.le hs (by omega : n ≠ 0)
    -- combine: c * (t - t₀) ≤ dev + ‖err‖ ≤ small * (t - t₀) eventually
    set ε' : ℝ := ε / (2 * (‖L‖ + 1) ^ n) with hε'_def
    have hε' : 0 < ε' := by positivity
    have h_dev_bound := (isLittleO_iff.mp h_dev) hε'
    have h_err_bound := (isLittleO_iff.mp herr) (c := ε / 2) (by positivity)
    have h_all : ∀ᶠ t in 𝓝[>] t₀, c * (t - t₀) ≤ ε * (t - t₀) := by
      filter_upwards [h_dev_bound, h_err_bound, h_pow, self_mem_nhdsWithin]
        with t hd he hp ht
      have ht' : 0 < t - t₀ := sub_pos.mpr ht
      -- seminorm triangle: |Im((t-t₀)L · conj v)| ≤ |Im((γΔ)conj v)| + ‖err‖·‖v‖
      have h_tri : c * (t - t₀) ≤
          |((γ t - γ t₀) * star v).im| / ‖v‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
        have h_split : ((t - t₀ : ℝ) • L) * starRingEnd ℂ v =
            (γ t - γ t₀) * star v - (γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v := by
          rw [Complex.star_def]
          ring
        have h_im : |(((t - t₀ : ℝ) • L) * starRingEnd ℂ v).im| ≤
            |((γ t - γ t₀) * star v).im| + ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖ := by
          rw [h_split, Complex.sub_im]
          refine (abs_sub _ _).trans ?_
          gcongr
          calc |((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v).im|
              ≤ ‖(γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v‖ :=
                Complex.abs_im_le_norm _
            _ = ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖ := by
                rw [norm_mul, RCLike.norm_conj]
        have hc_mul : c * ‖v‖ = |(L * starRingEnd ℂ v).im| := by
          rw [hc_def]
          field_simp
        have h_lhs : |(((t - t₀ : ℝ) • L) * starRingEnd ℂ v).im| = (t - t₀) * (c * ‖v‖) := by
          rw [Complex.real_smul, mul_assoc]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          rw [abs_mul, abs_of_pos ht', hc_mul, Complex.mul_im]
        rw [h_lhs] at h_im
        calc c * (t - t₀) = (t - t₀) * (c * ‖v‖) / ‖v‖ := by field_simp
          _ ≤ (|((γ t - γ t₀) * star v).im| +
              ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖) / ‖v‖ := by gcongr
          _ = |((γ t - γ t₀) * star v).im| / ‖v‖ +
              ‖γ t - γ t₀ - (t - t₀) • L‖ := by
              rw [add_div, mul_div_assoc, div_self hv_pos.ne', mul_one]
      rw [Real.norm_eq_abs, abs_of_pos ht'] at he
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hd
      have hd' : |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ((‖L‖ + 1) ^ n * (t - t₀)) := by
        calc |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ‖γ t - γ t₀‖ ^ n := by
              simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)] using hd
          _ ≤ ε' * ((‖L‖ + 1) ^ n * (t - t₀)) := by gcongr
      have hε'_eq : ε' * (‖L‖ + 1) ^ n = ε / 2 := by
        rw [hε'_def]
        field_simp
      calc c * (t - t₀) ≤ |((γ t - γ t₀) * star v).im| / ‖v‖ +
            ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
        _ ≤ ε' * ((‖L‖ + 1) ^ n * (t - t₀)) + ε / 2 * (t - t₀) := by
            gcongr
        _ = ε * (t - t₀) := by rw [← mul_assoc, hε'_eq]; ring
    obtain ⟨t, hct, ht⟩ := (h_all.and self_mem_nhdsWithin).exists
    exact le_of_mul_le_mul_right hct (sub_pos.mpr ht)
  rcases eq_or_lt_of_le hc_nonneg with h0 | hpos
  · have h' : |(L * starRingEnd ℂ v).im| / ‖v‖ = 0 := by rw [← hc_def, ← h0]
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp h').resolve_right hv_pos.ne')
  · exact absurd (hc_le (c / 2) (by linarith)) (by linarith)

/-- The forcing core (left side): the counterpart of `im_mul_conj_eq_zero_of_flat_right` from
the left. -/
private theorem im_mul_conj_eq_zero_of_flat_left {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n)
    (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le : ∀ ε : ℝ, 0 < ε → c ≤ ε := by
    intro ε hε
    have herr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[𝓝[<] t₀] (fun t => t - t₀) :=
      hasDerivWithinAt_iff_isLittleO.mp h_deriv
    have h_growth : ∀ᶠ t in 𝓝[<] t₀, ‖γ t - γ t₀‖ ≤ (‖L‖ + 1) * (t₀ - t) := by
      filter_upwards [herr.bound one_pos, self_mem_nhdsWithin] with t hb ht
      have ht' : 0 < t₀ - t := sub_pos.mpr ht
      have h1 : ‖γ t - γ t₀‖ ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
        simpa using norm_add_le ((t - t₀) • L) (γ t - γ t₀ - (t - t₀) • L)
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : t - t₀ < 0)] at h1
      rw [Real.norm_eq_abs, abs_of_neg (by linarith : t - t₀ < 0)] at hb
      calc ‖γ t - γ t₀‖ ≤ -(t - t₀) * ‖L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := h1
        _ ≤ -(t - t₀) * ‖L‖ + 1 * -(t - t₀) := by linarith
        _ = (‖L‖ + 1) * (t₀ - t) := by ring
    have h_pow : ∀ᶠ t in 𝓝[<] t₀, ‖γ t - γ t₀‖ ^ n ≤ (‖L‖ + 1) ^ n * (t₀ - t) := by
      have h_small : ∀ᶠ t in 𝓝[<] t₀, t₀ - t ≤ 1 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (eventually_ge_nhds (by linarith : t₀ - 1 < t₀))] with t ht
        linarith
      filter_upwards [h_growth, h_small, self_mem_nhdsWithin] with t hg hs ht
      have ht' : 0 < t₀ - t := sub_pos.mpr ht
      calc ‖γ t - γ t₀‖ ^ n ≤ ((‖L‖ + 1) * (t₀ - t)) ^ n := by gcongr
        _ = (‖L‖ + 1) ^ n * (t₀ - t) ^ n := by rw [mul_pow]
        _ ≤ (‖L‖ + 1) ^ n * (t₀ - t) := by
            gcongr
            exact pow_le_of_le_one ht'.le hs (by omega : n ≠ 0)
    set ε' : ℝ := ε / (2 * (‖L‖ + 1) ^ n) with hε'_def
    have hε' : 0 < ε' := by positivity
    have h_dev_bound := (isLittleO_iff.mp h_dev) hε'
    have h_err_bound := (isLittleO_iff.mp herr) (c := ε / 2) (by positivity)
    have h_all : ∀ᶠ t in 𝓝[<] t₀, c * (t₀ - t) ≤ ε * (t₀ - t) := by
      filter_upwards [h_dev_bound, h_err_bound, h_pow, self_mem_nhdsWithin]
        with t hd he hp ht
      have ht' : 0 < t₀ - t := sub_pos.mpr ht
      have h_tri : c * (t₀ - t) ≤
          |((γ t - γ t₀) * star v).im| / ‖v‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
        have h_split : ((t - t₀ : ℝ) • L) * starRingEnd ℂ v =
            (γ t - γ t₀) * star v - (γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v := by
          rw [Complex.star_def]
          ring
        have h_im : |(((t - t₀ : ℝ) • L) * starRingEnd ℂ v).im| ≤
            |((γ t - γ t₀) * star v).im| + ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖ := by
          rw [h_split, Complex.sub_im]
          refine (abs_sub _ _).trans ?_
          gcongr
          calc |((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v).im|
              ≤ ‖(γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ v‖ :=
                Complex.abs_im_le_norm _
            _ = ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖ := by
                rw [norm_mul, RCLike.norm_conj]
        have hc_mul : c * ‖v‖ = |(L * starRingEnd ℂ v).im| := by
          rw [hc_def]
          field_simp
        have h_lhs : |(((t - t₀ : ℝ) • L) * starRingEnd ℂ v).im| = (t₀ - t) * (c * ‖v‖) := by
          rw [Complex.real_smul, mul_assoc]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          rw [abs_mul, abs_of_neg (by linarith : t - t₀ < 0), hc_mul, neg_sub,
            Complex.mul_im]
        rw [h_lhs] at h_im
        calc c * (t₀ - t) = (t₀ - t) * (c * ‖v‖) / ‖v‖ := by field_simp
          _ ≤ (|((γ t - γ t₀) * star v).im| +
              ‖γ t - γ t₀ - (t - t₀) • L‖ * ‖v‖) / ‖v‖ := by gcongr
          _ = |((γ t - γ t₀) * star v).im| / ‖v‖ +
              ‖γ t - γ t₀ - (t - t₀) • L‖ := by
              rw [add_div, mul_div_assoc, div_self hv_pos.ne', mul_one]
      rw [Real.norm_eq_abs, abs_of_neg (by linarith : t - t₀ < 0)] at he
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hd
      have hd' : |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ((‖L‖ + 1) ^ n * (t₀ - t)) := by
        calc |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ‖γ t - γ t₀‖ ^ n := by
              simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)] using hd
          _ ≤ ε' * ((‖L‖ + 1) ^ n * (t₀ - t)) := by gcongr
      have hε'_eq : ε' * (‖L‖ + 1) ^ n = ε / 2 := by
        rw [hε'_def]
        field_simp
      calc c * (t₀ - t) ≤ |((γ t - γ t₀) * star v).im| / ‖v‖ +
            ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
        _ ≤ ε' * ((‖L‖ + 1) ^ n * (t₀ - t)) + ε / 2 * -(t - t₀) := by
            gcongr
        _ = ε * (t₀ - t) := by rw [← mul_assoc, hε'_eq]; ring
    obtain ⟨t, hct, ht⟩ := (h_all.and self_mem_nhdsWithin).exists
    exact le_of_mul_le_mul_right hct (sub_pos.mpr ht)
  rcases eq_or_lt_of_le hc_nonneg with h0 | hpos
  · have h' : |(L * starRingEnd ℂ v).im| / ‖v‖ = 0 := by rw [← hc_def, ← h0]
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp h').resolve_right hv_pos.ne')
  · exact absurd (hc_le (c / 2) (by linarith)) (by linarith)

/-- **Flatness bounds the deviation against the right tangent**: from `FlatOfOrder γ t₀ n`
(`n ≥ 1`) and a right derivative `L ≠ 0`, the perpendicular deviation against `L` itself is
`o(‖γ t - γ t₀‖ ^ n)` from the right — the hypothesis the higher-order antiderivative
asymptotics consume. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_right {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, hvp, hvm, hr, -⟩ := flatOfOrder_iff.mp hflat
  obtain ⟨cc, -, hcc⟩ := exists_real_smul_of_im_mul_conj_eq_zero hvp
    (im_mul_conj_eq_zero_of_flat_right hvp hn hr h_deriv)
  have hcc_ne : cc ≠ 0 := fun h0 => hL (by rw [hcc, h0, zero_smul])
  have hkey : ∀ t, ‖tangentDeviation (γ t - γ t₀) L‖ =
      |((γ t - γ t₀) * star vp).im| / ‖vp‖ := fun t => by
    rw [hcc, norm_tangentDeviation_smul_real hcc_ne hvp, norm_tangentDeviation hvp,
      Complex.star_def]
  exact hr.congr' (Filter.Eventually.of_forall fun t => (hkey t).symm) Filter.EventuallyEq.rfl

/-- **Flatness bounds the deviation against the left tangent**: the counterpart of
`FlatOfOrder.tangentDeviation_isLittleO_right` from the left. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_left {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, hvp, hvm, -, hl⟩ := flatOfOrder_iff.mp hflat
  obtain ⟨cc, -, hcc⟩ := exists_real_smul_of_im_mul_conj_eq_zero hvm
    (im_mul_conj_eq_zero_of_flat_left hvm hn hl h_deriv)
  have hcc_ne : cc ≠ 0 := fun h0 => hL (by rw [hcc, h0, zero_smul])
  have hkey : ∀ t, ‖tangentDeviation (γ t - γ t₀) L‖ =
      |((γ t - γ t₀) * star vm).im| / ‖vm‖ := fun t => by
    rw [hcc, norm_tangentDeviation_smul_real hcc_ne hvm, norm_tangentDeviation hvm,
      Complex.star_def]
  exact hl.congr' (Filter.Eventually.of_forall fun t => (hkey t).symm) Filter.EventuallyEq.rfl

end TauCeti.Contour

end
