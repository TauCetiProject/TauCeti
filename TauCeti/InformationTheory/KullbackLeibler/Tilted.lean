/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Relative entropy against an exponentially tilted reference

Let `ν` be a probability measure and `f ≥ 0` a measurable potential. The tilted measure
`ν.tilted (-f)` is the Gibbs probability measure `Z⁻¹ e^{-f} ν`, where `Z = ∫ e^{-f} dν` lies in
`(0, 1]`. Changing the reference measure of a relative entropy from `ν` to this Gibbs measure
trades the potential energy `∫ f dμ` against the free energy `-log Z`:
`klDiv μ (ν.tilted (-f)) - log Z = ∫ f dμ + klDiv μ ν` for every probability measure `μ`.

Mathlib's `MeasureTheory.integral_llr_tilted_right` gives the real-valued form of this identity,
under the hypotheses that `f` is `μ`-integrable and both log-likelihood ratios are integrable.
The statement here is the one in `ℝ≥0∞`, with no integrability hypothesis: each side is infinite
exactly when the other is. Its two genuinely new cases are a measure `μ` that is not absolutely
continuous with respect to `ν`, and a potential that is not `μ`-integrable, where the relative
entropy against the Gibbs measure has to be shown infinite. The latter rests on
`TauCeti.integrable_llr_of_ae_le`: the negative part of a log-likelihood ratio between finite
measures is always integrable, so an integrable upper bound makes the ratio integrable.

This is the change-of-reference step behind entropic optimal transport, where `f` is the cost
divided by the temperature and `ν` is the product of the two marginals.

## Main statements

* `TauCeti.integrable_llr_of_ae_le`: for finite measures `μ ≪ ν`, the log-likelihood ratio
  `llr μ ν` is `μ`-integrable as soon as it is bounded above by a `μ`-integrable function.
* `TauCeti.klDiv_tilted_neg_add_ofReal_neg_log`: the change-of-reference identity
  `klDiv μ (ν.tilted (-f)) + ENNReal.ofReal (-log Z) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ + klDiv μ ν`.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the Gibbs reformulation of entropically regularised transport.
-/

public section

open MeasureTheory Real InformationTheory
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f g : α → ℝ}

/-- For finite measures `μ ≪ ν`, an integrable upper bound on the log-likelihood ratio
`llr μ ν` makes it integrable. Its negative part needs no hypothesis: `log t ≥ 1 - t⁻¹` bounds it
below by `1 - dν/dμ`, which is `μ`-integrable since `ν` is finite. -/
theorem integrable_llr_of_ae_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, llr μ ν x ≤ g x) : Integrable (llr μ ν) μ := by
  refine integrable_of_le_of_le (measurable_llr μ ν).aestronglyMeasurable ?_ h
    ((integrable_const 1).sub (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))) hg
  filter_upwards [Measure.inv_rnDeriv hμν, Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hpos hlt
  simp only [Pi.sub_apply]
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv]
  exact one_sub_inv_le_log_of_pos (ENNReal.toReal_pos hpos.ne' hlt.ne)

/-- **Change of reference to a Gibbs measure.** For probability measures `μ` and `ν` and a
nonnegative potential `f`, the relative entropy of `μ` against the Gibbs measure
`ν.tilted (-f) = Z⁻¹ e^{-f} ν`, with `Z = ∫ e^{-f} dν`, satisfies
`klDiv μ (ν.tilted (-f)) - log Z = ∫ f dμ + klDiv μ ν`. Since `0 < Z ≤ 1`, every term is
nonnegative, and the identity holds in `ℝ≥0∞` with no integrability hypothesis. -/
theorem klDiv_tilted_neg_add_ofReal_neg_log [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf : AEMeasurable f ν) (hf0 : 0 ≤ᵐ[ν] f) :
    klDiv μ (ν.tilted fun x ↦ -f x) + ENNReal.ofReal (-log (∫ x, exp (-f x) ∂ν)) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ + klDiv μ ν := by
  set Z := ∫ x, exp (-f x) ∂ν
  have hexp : Integrable (fun x ↦ exp (-f x)) ν :=
    (integrable_const 1).mono' (hf.neg.exp).aestronglyMeasurable <| by
      filter_upwards [hf0] with x hx
      simpa [abs_exp] using hx
  have hZ : 0 < Z := integral_exp_pos hexp
  have : IsProbabilityMeasure (ν.tilted fun x ↦ -f x) := isProbabilityMeasure_tilted hexp
  -- Three cases: if `μ` is not absolutely continuous with respect to `ν`, or if `f` is not
  -- `μ`-integrable, both sides are infinite; otherwise this is Mathlib's real-valued identity.
  by_cases hμν : μ ≪ ν
  swap
  · have hμG : ¬ μ ≪ ν.tilted fun x ↦ -f x :=
      fun h ↦ hμν (h.trans (tilted_absolutelyContinuous ν _))
    simp [klDiv_of_not_ac hμG, klDiv_of_not_ac hμν]
  have hμG : μ ≪ ν.tilted fun x ↦ -f x := hμν.trans (absolutelyContinuous_tilted hexp)
  have hllr : llr μ (ν.tilted fun x ↦ -f x) =ᵐ[μ] fun x ↦ (f x + log Z) + llr μ ν x := by
    filter_upwards [llr_tilted_right hμν hexp] with x hx
    simpa using hx
  have hfμ : AEStronglyMeasurable f μ := (hf.mono_ac hμν).aestronglyMeasurable
  have hf0μ : 0 ≤ᵐ[μ] f := hμν.ae_le hf0
  by_cases hfi : Integrable f μ
  · have hfZ : Integrable (fun x ↦ f x + log Z) μ := hfi.add (integrable_const _)
    have hiff : Integrable (llr μ (ν.tilted fun x ↦ -f x)) μ ↔ Integrable (llr μ ν) μ := by
      rw [integrable_congr hllr]
      exact integrable_add_iff_integrable_right hfZ
    by_cases hint : Integrable (llr μ ν) μ
    swap
    · simp [klDiv_of_not_integrable hint, klDiv_of_not_integrable (mt hiff.1 hint)]
    have hintG := hiff.2 hint
    have hP := integral_llr_add_sub_measure_univ_nonneg hμν hint
    have hG := integral_llr_add_sub_measure_univ_nonneg hμG hintG
    simp only [probReal_univ, add_sub_cancel_right] at hP hG
    have hGP : ∫ x, llr μ (ν.tilted fun x ↦ -f x) x ∂μ =
        ∫ x, f x ∂μ + log Z + ∫ x, llr μ ν x ∂μ := by
      rw [integral_congr_ae hllr, integral_add hfZ hint, integral_add hfi (integrable_const _)]
      simp
    rw [klDiv_of_ac_of_integrable hμG hintG, klDiv_of_ac_of_integrable hμν hint,
      ← ofReal_integral_eq_lintegral_ofReal hfi hf0μ]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [← ENNReal.ofReal_add hG (neg_nonneg.2 (log_nonpos hZ.le ?_)),
      ← ENNReal.ofReal_add (integral_nonneg_of_ae hf0μ) hP, hGP]
    · ring_nf
    · calc Z ≤ ∫ _, (1 : ℝ) ∂ν :=
            integral_mono_ae hexp (integrable_const 1) <| by
              filter_upwards [hf0] with x hx
              simpa using hx
        _ = 1 := by simp
  · -- A potential that is not `μ`-integrable has infinite energy, and then the relative
    -- entropy against the Gibbs measure is infinite too: were it finite, `llr μ ν` would be
    -- bounded above by the integrable `llr μ (ν.tilted _) - log Z`, hence integrable, and so
    -- would be `f`, as the difference of the two log-likelihood ratios.
    have hlin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ⊤ := by
      by_contra h
      exact hfi ((lintegral_ofReal_ne_top_iff_integrable hfμ hf0μ).1 h)
    have hG : klDiv μ (ν.tilted fun x ↦ -f x) = ⊤ := by
      rw [klDiv_eq_top_iff]
      intro _ hintG
      have hint : Integrable (llr μ ν) μ := by
        refine integrable_llr_of_ae_le hμν (hintG.sub (integrable_const (log Z))) ?_
        filter_upwards [hllr, hf0μ] with x hx hx0
        simp only [Pi.sub_apply, hx]
        linarith [show 0 ≤ f x from hx0]
      refine hfi ((integrable_congr ?_).1 ((hintG.sub hint).sub (integrable_const (log Z))))
      filter_upwards [hllr] with x hx
      rw [Pi.sub_apply, Pi.sub_apply, hx]
      ring
    simp [hlin, hG]

end TauCeti
