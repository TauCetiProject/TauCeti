/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Basic.Real.Sign

/-!
# Measure-theoretic properties of the real sign function

The real sign function is measurable, so it can be composed with measurable real-valued
parameters even at their zeros (`TauCeti.measurable_real_sign` and `TauCeti.measurable_coe_sign`).
Moreover, any real function continuous at `0` stays at `L^∞(B(0, r))` distance at least `1` from
`sign` for every `r > 0` (`TauCeti.one_le_eLpNorm_top_sub_sign_of_continuousAt`).
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

/-- The real sign function is measurable. -/
@[fun_prop]
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (by measurability) measurable_const
    (Measurable.ite (by measurability) measurable_const measurable_const)

/-- Coercing `SignType.sign` to `ℝ` is measurable. -/
@[fun_prop]
theorem measurable_coe_sign : Measurable fun r : ℝ => (SignType.sign r : ℝ) := by
  simpa only [Real.coe_sign_eq_sign] using measurable_real_sign

/-- Any real function continuous at `0` stays at `L^∞(B(0, r))` distance at least `1` from `sign`
for every `r > 0`. -/
theorem one_le_eLpNorm_top_sub_sign_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    {r : ℝ} (hr : 0 < r) :
    1 ≤ eLpNorm (fun x : ℝ => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε0 : 0 < (ε : ℝ) := NNReal.coe_pos.2 hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg (ε : ℝ) hε0
  set η := min δ r
  have hη : 0 < η := lt_min hδ hr
  set c : ℝ≥0∞ := eLpNorm (fun x => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r))
  have hae : ∀ᵐ x ∂volume.restrict (ball (0 : ℝ) r), ‖g x - (SignType.sign x : ℝ)‖ₑ ≤ c :=
    ae_le_eLpNormEssSup.mono fun x hx => hx.trans eLpNormEssSup_le_eLpNorm_top
  have hstep {a b s : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ ball (0 : ℝ) r)
      (hsign : ∀ x ∈ Ioo a b, (SignType.sign x : ℝ) = s)
      (hclose : ∀ x ∈ Ioo a b, |g x - g 0| < ε) (hgap : (1 : ℝ) ≤ |g 0 - s|) :
      (1 : ℝ≥0∞) ≤ c + ε := by
    have hpos : volume (Ioo a b) ≠ 0 := by simp [Real.volume_Ioo, hab]
    obtain ⟨x, hxIoo, hxc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae_restrict_of_subset hsub hae)
    have h1 : (1 : ℝ) ≤ |g x - (SignType.sign x : ℝ)| + ε := by
      have htri : |g 0 - s| ≤ |g 0 - g x| + |g x - s| := abs_sub_le _ _ _
      rw [abs_sub_comm (g 0) (g x)] at htri
      rw [hsign x hxIoo]
      linarith [hclose x hxIoo]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|g x - (SignType.sign x : ℝ)| + ε) := ENNReal.ofReal_le_ofReal h1
      _ = ‖g x - (SignType.sign x : ℝ)‖ₑ + ε := by
          rw [ENNReal.ofReal_add (abs_nonneg _) hε0.le, ← Real.norm_eq_abs, ofReal_norm,
            ENNReal.ofReal_coe_nnreal]
      _ ≤ c + ε := by gcongr
  rcases le_or_gt (g 0) 0 with hg0 | hg0
  · refine hstep hη (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_right _ _))
      (fun x hx => by rw [sign_pos hx.1, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_left _ _))
      (by linarith [neg_le_abs (g 0 - 1)])
  · refine hstep (neg_lt_zero.2 hη) (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_neg hx.2]
        linarith [hx.1, min_le_right δ r])
      (fun x hx => by rw [sign_neg hx.2, SignType.coe_neg, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_neg hx.2]
        linarith [hx.1, min_le_left δ r])
      (by linarith [le_abs_self (g 0 - (-1))])

end TauCeti
