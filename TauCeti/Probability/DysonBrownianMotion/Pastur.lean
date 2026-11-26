/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic
public import TauCeti.Probability.DysonBrownianMotion.Burgers
import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Evolution

/-!
# Existence and uniqueness of Burgers flows via the Pastur semigroup

This file connects the Pastur measure semigroup `t ↦ ν.pastur t` (constructed in
`TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic` via Schauder's fixed-point theorem
and the Pick–Nevanlinna characterization) and its differentiated Stieltjes–Burgers evolution
(`MeasureTheory.hasDerivWithinAt_resolventTransform_pastur_Ici` in
`TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Evolution`) to the integrated complex
Burgers flow predicate `TauCeti.Probability.IsBurgersFlow` and its uniqueness theorem
`TauCeti.Probability.IsBurgersFlow.eq` from `TauCeti.Probability.DysonBrownianMotion.Burgers`.

Applying `TauCeti.Probability.IsBurgersFlow.of_hasDerivWithinAt` shows that `t ↦ ν.pastur t` is a
Burgers flow for every Borel measure `ν` on `ℝ` (`TauCeti.Probability.isBurgersFlow_pastur`): when
`ν` is finite its initial measure is `ν.pastur 0 = ν`, and when `ν` is infinite `ν.pastur t = 0` is
the zero flow. Combining this existence result with `TauCeti.Probability.IsBurgersFlow.eq` shows
that every probability-measure Burgers flow started at `ν` equals `t ↦ ν.pastur t`
(`TauCeti.Probability.IsBurgersFlow.eq_pastur`), classifying all probability-measure Burgers flows
on `ℝ` (`TauCeti.Probability.isBurgersFlow_iff_eq_pastur`).

Note the sign convention: Mathlib's `MeasureTheory.resolventTransform` uses `(x - z)⁻¹`, for which
the complex Burgers equation reads `∂_t m_t(z) = m_t(z) ∂_z m_t(z)`.

## Main results

* `TauCeti.Probability.isBurgersFlow_pastur`: `t ↦ ν.pastur t` forms a Burgers flow for every
  measure `ν` on `ℝ`.
* `TauCeti.Probability.IsBurgersFlow.eq_pastur`: a Burgers flow of probability measures started at
  `ν` equals `t ↦ ν.pastur t`.
* `TauCeti.Probability.isBurgersFlow_iff_eq_pastur`: among families of probability measures on `ℝ`,
  Burgers flows are precisely the Pastur evolutions `t ↦ (μ 0).pastur t`.

## References

* L. A. Pastur, *On the spectrum of random matrices*, Teoret. Mat. Fiz. 10 (1972), 102–112.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* P. Biane, *On the free convolution with a semi-circular distribution*, Indiana Univ. Math. J.
  46 (1997), 705–718.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Proposition 4.3.10 and §4.3.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- **The Pastur flow.** For every Borel measure `ν` on `ℝ`, the Pastur evolution `t ↦ ν.pastur t`
forms a Burgers flow (with initial measure `ν.pastur 0 = ν` when `ν` is finite, and the zero flow
when `ν` is infinite). -/
theorem isBurgersFlow_pastur (ν : Measure ℝ) : IsBurgersFlow fun t ↦ ν.pastur t :=
  .of_hasDerivWithinAt (fun _ hz ↦ continuous_resolventTransform_pastur hz.ne')
    (fun _ hz _ ↦ (((continuous_resolventTransform_pastur hz.ne').mul
      (continuous_deriv_resolventTransform_pastur hz.ne')).comp
        continuous_real_toNNReal).intervalIntegrable _ _)
    fun _ hz _ ht ↦ (hasDerivWithinAt_resolventTransform_pastur_Ici hz.ne' ht).mono
      (Ici_subset_Ici.2 ht)

/-- **The Burgers flow from an arbitrary initial law.** A Burgers flow of probability measures on
`ℝ` started at `ν` is the Pastur evolution `t ↦ ν.pastur t`. -/
theorem IsBurgersFlow.eq_pastur {μ : ℝ≥0 → Measure ℝ} [∀ t, IsProbabilityMeasure (μ t)]
    {ν : Measure ℝ} (hμ : IsBurgersFlow μ) (h₀ : μ 0 = ν) :
    μ = fun t ↦ ν.pastur t := by
  subst h₀
  exact hμ.eq (isBurgersFlow_pastur (μ 0)) (Measure.pastur_zero (μ 0)).symm

/-- **Classification of probability-measure Burgers flows.** A family `(μ_t)_{t ≥ 0}` of
probability measures on `ℝ` solves the complex Burgers equation if and only if it is the Pastur
evolution `t ↦ (μ 0).pastur t` of its initial measure. -/
theorem isBurgersFlow_iff_eq_pastur {μ : ℝ≥0 → Measure ℝ} [∀ t, IsProbabilityMeasure (μ t)] :
    IsBurgersFlow μ ↔ μ = fun t ↦ (μ 0).pastur t :=
  ⟨fun hμ ↦ hμ.eq_pastur rfl, fun h ↦ by rw [h]; exact isBurgersFlow_pastur (μ 0)⟩

end TauCeti.Probability

end
