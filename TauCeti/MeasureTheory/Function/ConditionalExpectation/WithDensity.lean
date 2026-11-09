/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bayes' formula for integrable random variables

For a finite measure `Q = μ.withDensity w`, conditional expectation under `Q` is
conditional expectation of the density-weighted variable under `μ`, divided by the
conditional density. The multiplication identity holds `μ`-almost everywhere, even
where the density vanishes. The division identity holds `Q`-almost everywhere; no
strict positivity or equivalence assumption is needed.

The observable may take values in any real Banach space and need only be integrable
under `Q`, not under `μ`. These identities allow conditional prices and martingale
identities to be transported across a change of measure. We use native conditional
expectation, its integral characterization and its unbounded-multiplier pull-out rule.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {w : Ω → ℝ≥0∞} {f : Ω → E}

/-- **Bayes' formula, multiplication form.** The conditional density times the
new-measure conditional expectation is the old-measure conditional expectation of
the weighted variable. The observable need not be integrable under the old measure. -/
theorem condExp_toReal_smul_condExp_withDensity (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (hw : AEMeasurable w μ)
    [IsFiniteMeasure (μ.withDensity w)] (hf : Integrable f (μ.withDensity w)) :
    (fun x ↦ μ[fun y ↦ (w y).toReal | m] x • (μ.withDensity w)[f | m] x) =ᵐ[μ]
      μ[fun x ↦ (w x).toReal • f x | m] := by
  have hmass := isFiniteMeasure_withDensity_iff.mp
    (inferInstance : IsFiniteMeasure (μ.withDensity w))
  have htop := ae_lt_top' hw hmass
  have hwint := integrable_toReal_of_lintegral_ne_top hw hmass
  have hweighted := (integrable_withDensity_iff_integrable_smul₀' hw htop).mp hf
  have hweightedCE := (integrable_withDensity_iff_integrable_smul₀' hw htop).mp
    (integrable_condExp (μ := μ.withDensity w) (f := f) (m := m))
  have hpull := condExp_smul_of_aestronglyMeasurable_right hwint hweightedCE
    (stronglyMeasurable_condExp.aestronglyMeasurable (μ := μ))
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hweighted
    (fun _ _ _ ↦ integrable_condExp.congr hpull |>.integrableOn) ?_
    ((stronglyMeasurable_condExp.smul stronglyMeasurable_condExp).aestronglyMeasurable)
  intro s hs _
  calc
    ∫ x in s, μ[fun y ↦ (w y).toReal | m] x • (μ.withDensity w)[f | m] x ∂μ =
        ∫ x in s, μ[fun y ↦ (w y).toReal • (μ.withDensity w)[f | m] y | m] x ∂μ :=
      setIntegral_congr_ae (hm s hs) (hpull.symm.mono fun _ hx _ ↦ hx)
    _ = ∫ x in s, (w x).toReal • (μ.withDensity w)[f | m] x ∂μ :=
      setIntegral_condExp hm hweightedCE hs
    _ = ∫ x in s, (μ.withDensity w)[f | m] x ∂μ.withDensity w :=
      (setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hw.restrict
        (ae_restrict_of_ae htop) _ (hm s hs)).symm
    _ = ∫ x in s, f x ∂μ.withDensity w := setIntegral_condExp hm hf hs
    _ = ∫ x in s, (w x).toReal • f x ∂μ :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hw.restrict
        (ae_restrict_of_ae htop) _ (hm s hs)

/-- The conditional density is strictly positive almost everywhere under the new
measure, even when the original density vanishes on a set of positive old measure. -/
theorem condExp_toReal_pos_withDensity (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)] :
    ∀ᵐ x ∂μ.withDensity w, 0 < μ[fun y ↦ (w y).toReal | m] x := by
  have hmass := isFiniteMeasure_withDensity_iff.mp
    (inferInstance : IsFiniteMeasure (μ.withDensity w))
  have htop := ae_lt_top' hw hmass
  have hwint := integrable_toReal_of_lintegral_ne_top hw hmass
  let s := {x | μ[fun y ↦ (w y).toReal | m] x = 0}
  have hs : MeasurableSet[m] s := stronglyMeasurable_condExp.measurable (measurableSet_singleton 0)
  have hint : ∫ x in s, (w x).toReal ∂μ = 0 := by
    rw [← setIntegral_condExp hm hwint hs]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ hx
  have hzero : (fun x ↦ (w x).toReal) =ᵐ[μ.restrict s] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ ENNReal.toReal_nonneg) hwint.integrableOn).mp hint
  have hqs : μ.withDensity w s = 0 := by
    rw [withDensity_apply _ (hm s hs)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero, ae_restrict_of_ae htop] with x hx hxt
    exact ((ENNReal.toReal_eq_zero_iff _).mp hx).resolve_right hxt.ne
  have hne : ∀ᵐ x ∂μ.withDensity w, μ[fun y ↦ (w y).toReal | m] x ≠ 0 := by
    simpa only [ae_iff, not_not] using hqs
  have hnonneg := (withDensity_absolutelyContinuous μ w).ae_le
    (condExp_nonneg (m := m) (μ := μ) (f := fun x ↦ (w x).toReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg))
  filter_upwards [hne, hnonneg] with x hx hnx
  exact lt_of_le_of_ne hnx hx.symm

/-- **Bayes' formula** for a Banach-valued integrable observable. Division is expressed
as scalar multiplication by the inverse conditional density. Equality is under the
new measure, so the formula also permits densities which vanish. -/
theorem condExp_withDensity (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)]
    (hf : Integrable f (μ.withDensity w)) :
    (μ.withDensity w)[f | m] =ᵐ[μ.withDensity w]
      fun x ↦ (μ[fun y ↦ (w y).toReal | m] x)⁻¹ •
        μ[fun y ↦ (w y).toReal • f y | m] x := by
  have hmul := (withDensity_absolutelyContinuous μ w).ae_le
    (condExp_toReal_smul_condExp_withDensity hm hw hf)
  filter_upwards [hmul, condExp_toReal_pos_withDensity hm hw] with x hx hpos
  rw [← hx, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- **Bayes' formula** for a real integrable observable, in quotient notation.
The new-measure conditional mean is the density-weighted conditional mean divided
by the conditional density. -/
theorem condExp_withDensity_eq_div {f : Ω → ℝ} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (hw : AEMeasurable w μ)
    [IsFiniteMeasure (μ.withDensity w)] (hf : Integrable f (μ.withDensity w)) :
    (μ.withDensity w)[f | m] =ᵐ[μ.withDensity w]
      fun x ↦ μ[fun y ↦ (w y).toReal * f y | m] x /
        μ[fun y ↦ (w y).toReal | m] x := by
  simpa only [smul_eq_mul, div_eq_inv_mul] using condExp_withDensity hm hw hf

/-- A variable known in `m`, integrable under the changed measure, remains integrable
under the original measure after multiplication by the conditional density. -/
theorem StronglyMeasurable.integrable_condExp_toReal_smul (hf : StronglyMeasurable[m] f)
    (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)]
    (hint : Integrable f (μ.withDensity w)) :
    Integrable (fun x ↦ μ[fun y ↦ (w y).toReal | m] x • f x) μ := by
  have hmass := isFiniteMeasure_withDensity_iff.mp
    (inferInstance : IsFiniteMeasure (μ.withDensity w))
  have htop := ae_lt_top' hw hmass
  have hweighted := (integrable_withDensity_iff_integrable_smul₀' hw htop).mp hint
  exact integrable_condExp.congr
    (condExp_smul_of_aestronglyMeasurable_right
      (integrable_toReal_of_lintegral_ne_top hw hmass) hweighted hf.aestronglyMeasurable)

/-- On events in `m`, integration against the conditional density is integration
under the changed measure, for an `m`-measurable integrable observable. -/
theorem StronglyMeasurable.setIntegral_condExp_toReal_smul (hf : StronglyMeasurable[m] f)
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] (hw : AEMeasurable w μ)
    [IsFiniteMeasure (μ.withDensity w)] (hint : Integrable f (μ.withDensity w))
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫ x in s, μ[fun y ↦ (w y).toReal | m] x • f x ∂μ = ∫ x in s, f x ∂μ.withDensity w := by
  have hmass := isFiniteMeasure_withDensity_iff.mp
    (inferInstance : IsFiniteMeasure (μ.withDensity w))
  have htop := ae_lt_top' hw hmass
  have hweighted := (integrable_withDensity_iff_integrable_smul₀' hw htop).mp hint
  have hpull := condExp_smul_of_aestronglyMeasurable_right
    (integrable_toReal_of_lintegral_ne_top hw hmass) hweighted hf.aestronglyMeasurable
  calc
    ∫ x in s, μ[fun y ↦ (w y).toReal | m] x • f x ∂μ =
        ∫ x in s, μ[fun y ↦ (w y).toReal • f y | m] x ∂μ :=
      setIntegral_congr_ae (hm s hs) (hpull.symm.mono fun _ hx _ ↦ hx)
    _ = ∫ x in s, (w x).toReal • f x ∂μ := setIntegral_condExp hm hweighted hs
    _ = ∫ x in s, f x ∂μ.withDensity w :=
      (setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hw.restrict
        (ae_restrict_of_ae htop) _ (hm s hs)).symm

end MeasureTheory
