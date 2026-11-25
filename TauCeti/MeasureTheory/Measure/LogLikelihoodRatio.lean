/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Log-likelihood ratios of measures with real densities

Two measures `P = R.withDensity (ofReal ∘ p)` and `Q = R.withDensity (ofReal ∘ q)` with real
densities against a common reference measure `R` have log-likelihood ratio `log p - log q`,
`P`-almost everywhere, as soon as `P ≪ Q` and `Q` is σ-finite. Writing `P` as a density against
`Q` itself, the proof needs no σ-finiteness instance on `R`.

## Main statements

* `TauCeti.ae_pos_withDensity_ofReal`: a real density is positive almost everywhere for the
  measure it defines.
* `TauCeti.llr_withDensity_ofReal_ae_eq`: `llr P Q =ᵐ[P] log p - log q`.

## References

The statement is adapted from `llr_ae_eq_log_sub_log` in the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>, `CKSD/Bayes/Evidence/Bounds.lean`), which assumes a
σ-finite reference measure and positive densities.
-/

public section

open MeasureTheory Measure
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- A real density `p` is positive almost everywhere for the measure
`R.withDensity (ofReal ∘ p)` it defines. -/
theorem ae_pos_withDensity_ofReal {R : Measure α} {p : α → ℝ} (hp : AEMeasurable p R) :
    ∀ᵐ x ∂R.withDensity fun x ↦ ENNReal.ofReal (p x), 0 < p x :=
  (ae_withDensity_iff' hp.ennreal_ofReal).2 <|
    .of_forall fun _ hx ↦ ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hx)

/-- The log-likelihood ratio of the measures `P = R.withDensity (ofReal ∘ p)` and
`Q = R.withDensity (ofReal ∘ q)` with almost everywhere measurable real densities `p`, `q`
against a common reference measure `R` is `log p - log q`, `P`-almost everywhere, when `P ≪ Q`
and `Q` is σ-finite. No separate σ-finiteness instance on `R` is assumed (`Q` is σ-finite for
instance when `q` is integrable), and `p`, `q` may vanish together on a set of positive
`R`-measure. -/
theorem llr_withDensity_ofReal_ae_eq {R : Measure α} {p q : α → ℝ}
    [SigmaFinite (R.withDensity fun x ↦ ENNReal.ofReal (q x))] (hp : AEMeasurable p R)
    (hq : AEMeasurable q R)
    (hPQ : (R.withDensity fun x ↦ ENNReal.ofReal (p x)) ≪
      R.withDensity fun x ↦ ENNReal.ofReal (q x)) :
    llr (R.withDensity fun x ↦ ENNReal.ofReal (p x))
        (R.withDensity fun x ↦ ENNReal.ofReal (q x)) =ᵐ[R.withDensity fun x ↦ ENNReal.ofReal (p x)]
      fun x ↦ Real.log (p x) - Real.log (q x) := by
  set P := R.withDensity fun x ↦ ENNReal.ofReal (p x)
  set Q := R.withDensity fun x ↦ ENNReal.ofReal (q x)
  -- Both densities are positive `P`-almost everywhere.
  have hpP : ∀ᵐ x ∂P, 0 < p x := ae_pos_withDensity_ofReal hp
  have hqP : ∀ᵐ x ∂P, 0 < q x := hPQ.ae_le (ae_pos_withDensity_ofReal hq)
  -- Hence `P` has density `ofReal (p / q)` against `Q`.
  have hr : AEMeasurable (fun x ↦ ENNReal.ofReal (p x / q x)) R := (hp.div hq).ennreal_ofReal
  have hP : P = Q.withDensity fun x ↦ ENNReal.ofReal (p x / q x) := by
    rw [← withDensity_mul₀ hq.ennreal_ofReal hr]
    refine withDensity_congr_ae ?_
    filter_upwards [(ae_withDensity_iff' hp.ennreal_ofReal).1 hqP] with x hx
    rw [Pi.mul_apply]
    rcases le_or_gt (q x) 0 with hqx | hqx
    · have hpx : p x ≤ 0 := not_lt.1 fun hpx ↦ (hx (by simpa using hpx)).not_ge hqx
      rw [ENNReal.ofReal_of_nonpos hpx, ENNReal.ofReal_of_nonpos hqx, zero_mul]
    · rw [← ENNReal.ofReal_mul hqx.le, mul_div_cancel₀ _ hqx.ne']
  have hd := rnDeriv_withDensity₀ Q (hr.mono_ac (withDensity_absolutelyContinuous _ _))
  rw [← hP] at hd
  filter_upwards [hPQ.ae_le hd, hpP, hqP] with x hx hpx hqx
  rw [llr, hx, ENNReal.toReal_ofReal (div_pos hpx hqx).le, Real.log_div hpx.ne' hqx.ne']

end TauCeti
