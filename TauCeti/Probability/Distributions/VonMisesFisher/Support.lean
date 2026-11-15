/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of von Mises--Fisher distributions

The normalized exponential density of a von Mises--Fisher law is strictly positive at every
point of a nonempty sphere. Consequently its natural-parameter form has full topological support;
this remains true in dimension zero because the sphere and its universal set are empty. The
direction/concentration form therefore has full support exactly at nonnegative concentrations;
negative concentrations give the zero measure and empty support.

## Main results

* `TauCeti.Probability.support_vonMisesFisherNaturalMeasure` identifies the support of the
  natural-parameter law.
* `TauCeti.Probability.support_vonMisesFisherMeasure` identifies the support for every
  direction and concentration.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 9.3.
-/

public section

noncomputable section

open MeasureTheory Metric Real Set
open scoped ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every point of the sphere belongs to the support of the natural-parameter von Mises--Fisher
law. In dimension zero both the support and the universal set are empty. -/
@[simp]
theorem support_vonMisesFisherNaturalMeasure (η : E) :
    (vonMisesFisherNaturalMeasure η).support = Set.univ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [vonMisesFisherNaturalMeasure_of_subsingleton, Measure.support_zero]
    exact Set.eq_univ_iff_forall.mpr fun x ↦ isEmptyElim x
  · rw [vonMisesFisherNaturalMeasure_eq_withDensity,
      Measure.support_withDensity_eq (by fun_prop) (Filter.Eventually.of_forall fun x ↦ by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact div_pos (exp_pos _) (integral_exp_inner_uniformSphereMeasure_pos η)),
      support_uniformSphereMeasure]

/-- The direction/concentration von Mises--Fisher law has full support exactly at nonnegative
concentration. At negative concentration its support is empty. -/
@[simp]
theorem support_vonMisesFisherMeasure (m : sphere (0 : E) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).support = if 0 ≤ κ then Set.univ else ∅ := by
  by_cases hκ : 0 ≤ κ
  · have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
    simp [hκ]
  · simp [hκ, vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ)]

end TauCeti.Probability
