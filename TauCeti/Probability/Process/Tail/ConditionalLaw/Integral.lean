/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.ConditionalLaw.Basic
public import TauCeti.MeasureTheory.Integral.ENNRealProd

/-!
# Integrating finite products of tail-conditioned-law evaluations

Two facts about `∏ i, tailConditionalMeasure μ X ω (B i)`, read as a function of `ω`: it is
integrable in its real form, and its real integral agrees with its `ℝ≥0∞` integral. These let
rectangle arguments pass between real conditional expectations and measure-valued identities.

## Main results

* `integrable_prod_tailConditionalMeasure_real` — the product of the real evaluations is
  `[0,1]`-valued and measurable, hence integrable against a finite measure.
* `ofReal_integral_eq_lintegral_prod_tailConditionalMeasure` — the real integral of that product is
  the `ℝ≥0∞` integral of the product of the evaluations themselves.

Neither argument uses anything about tail-conditioned laws beyond measurability of each evaluation
`ω ↦ tailConditionalMeasure μ X ω (B i)` and the bounds `≤ 1` and `≠ ∞`. The two statements are
therefore instances of `TauCeti.MeasureTheory.integrable_prod_toReal` and
`TauCeti.MeasureTheory.ofReal_integral_prod_toReal_eq_lintegral_prod`, which are about finite
products of `ℝ≥0∞`-valued functions over a `Finset`, with almost-everywhere hypotheses, and mention
no measure on `α`. What is left here is the
specialisation: it discharges measurability from `measurable_tailConditionalMeasure_coe`, which all
three consumers would otherwise repeat.

In both, the measure in the integration slot is independent of the measure `μ` that defines the
tail-conditioned law: `μ` is only the parameter of the conditional law, and the integral is taken
against a separate `ν`. The set-integral forms are the instances at `ν := μ.restrict A`. Neither
mentions conditional independence, symmetry, or any cylinder: they are facts about the conditional
law alone.

This module is separate from `TauCeti.Probability.Process.Tail.ConditionalLaw.Basic` so that its
measurability and evaluation API stays free of the integration dependencies these results need.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- The product of tail-conditioned-law evaluations is a `[0,1]`-valued measurable function, hence
integrable against a finite measure. Only tail-measurability of the process and measurability of
the blocks are used; the integration measure `ν` is unrelated to the `μ` defining the
tail-conditioned law. -/
lemma integrable_prod_tailConditionalMeasure_real [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ω} [IsFiniteMeasure ν] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ mΩ) {r : ℕ} {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    Integrable (fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i)) ν :=
  by
  simpa only [measureReal_def] using
    TauCeti.MeasureTheory.integrable_prod_toReal
      (f := fun i ω => tailConditionalMeasure μ X ω (B i))
      (fun i _ => (measurable_tailConditionalMeasure_coe hTail (hB i)).aemeasurable)
      fun _ _ => ae_of_all _ fun _ => prob_le_one

/-- The real integral of the product of tail-conditioned-law evaluations is its `ℝ≥0∞` integral,
factor by factor: each factor is a finite measure of a set, so `ENNReal.ofReal_toReal` applies. As
above, `ν` is an arbitrary integration measure, so the set-integral form is the instance
`ν := μ.restrict A`. -/
lemma ofReal_integral_eq_lintegral_prod_tailConditionalMeasure [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ω} {X : ℕ → Ω → α} {r : ℕ}
    {B : Fin r → Set α}
    (hg_int : Integrable (fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i)) ν) :
    ENNReal.ofReal (∫ ω, ∏ i, (tailConditionalMeasure μ X ω).real (B i) ∂ν)
      = ∫⁻ ω, ∏ i, tailConditionalMeasure μ X ω (B i) ∂ν :=
  by
  simpa only [measureReal_def] using
    TauCeti.MeasureTheory.ofReal_integral_prod_toReal_eq_lintegral_prod
      (f := fun i ω => tailConditionalMeasure μ X ω (B i))
      (ae_of_all _ fun _ => ENNReal.prod_ne_top fun _ _ => measure_ne_top _ _)
      (by simpa only [measureReal_def] using hg_int)

end Probability

end TauCeti

end

end
