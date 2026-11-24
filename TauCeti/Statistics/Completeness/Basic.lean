/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Complete statistics

A statistic `T : X → S` is **complete** for a family of laws `P : Θ → Measure X` when no
nontrivial function of `T` estimates zero without bias: every measurable `g : S → ℝ` such that
`g ∘ T` is integrable with mean `0` under every `P θ` vanishes `P θ`-almost everywhere on the values
of `T`, for every `θ`. Completeness is a property of the family of laws of `T` alone. It is the
hypothesis under which unbiased estimators that are functions of `T` are unique, which drives the
Lehmann–Scheffé theorem, Basu's theorem and the theory of similar tests.

Following the convention that a real integral is only meaningful together with an integrability
hypothesis, the mean-zero condition is stated together with the integrability of `g ∘ T`, so that
the junk value `0` of a nonintegrable integral does not count as a mean zero.

## Main definitions

* `TauCeti.IsCompleteStatistic P T`: the statistic `T` is complete for the family `P`.

## Main results

* `TauCeti.IsCompleteStatistic.ae_eq_zero`: the elimination rule of completeness.
* `TauCeti.isCompleteStatistic_map_id_iff`: a measurable `T` is complete for `P` iff the identity is
  complete for the family of laws `(P θ).map T`.
* `TauCeti.IsCompleteStatistic.comp`: a measurable function of a complete statistic is complete.
* `TauCeti.isCompleteStatistic_dirac`: the identity is complete for the family of all Dirac laws.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Definition 1.5.1.
* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definition 2.34.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Θ X S S' : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace S']
  {P : Θ → Measure X} {T : X → S}

/-- The statistic `T : X → S` is **complete** for the family of laws `P : Θ → Measure X`: every
measurable `g : S → ℝ` such that `g ∘ T` is integrable with mean `0` under every `P θ` has
`g ∘ T = 0` almost everywhere under every `P θ`. -/
def IsCompleteStatistic (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g →
    (∀ θ, Integrable (g ∘ T) (P θ) ∧ ∫ x, g (T x) ∂P θ = 0) → ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- Unfolding `TauCeti.IsCompleteStatistic`. -/
theorem isCompleteStatistic_iff :
    IsCompleteStatistic P T ↔ ∀ g : S → ℝ, Measurable g →
      (∀ θ, Integrable (g ∘ T) (P θ) ∧ ∫ x, g (T x) ∂P θ = 0) →
        ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0 :=
  Iff.rfl

/-- **Elimination rule for completeness.** A measurable function of a complete statistic that is
integrable with mean `0` under every law of the family vanishes almost everywhere under every law
of the family. -/
theorem IsCompleteStatistic.ae_eq_zero (h : IsCompleteStatistic P T) {g : S → ℝ}
    (hg : Measurable g) (hint : ∀ θ, Integrable (g ∘ T) (P θ))
    (hzero : ∀ θ, ∫ x, g (T x) ∂P θ = 0) (θ : Θ) : ∀ᵐ x ∂P θ, g (T x) = 0 :=
  h g hg (fun θ ↦ ⟨hint θ, hzero θ⟩) θ

/-- Completeness of a measurable statistic `T` is completeness of the identity statistic for the
family of laws of `T`. -/
theorem isCompleteStatistic_map_id_iff (hT : Measurable T) :
    IsCompleteStatistic (fun θ ↦ (P θ).map T) id ↔ IsCompleteStatistic P T := by
  refine forall₂_congr fun g hg ↦ ?_
  have hset : MeasurableSet {s | g s = 0} := measurableSet_eq_fun hg measurable_const
  simp only [Function.comp_id, id_eq,
    integrable_map_measure hg.aestronglyMeasurable hT.aemeasurable,
    integral_map hT.aemeasurable hg.aestronglyMeasurable, ae_map_iff hT.aemeasurable hset]

/-- A measurable function of a complete statistic is complete. -/
theorem IsCompleteStatistic.comp (h : IsCompleteStatistic P T) {φ : S → S'} (hφ : Measurable φ) :
    IsCompleteStatistic P (φ ∘ T) :=
  fun g hg hzero ↦ h (g ∘ φ) (hg.comp hφ) hzero

/-- The identity statistic is complete for the family of all Dirac laws: a function with mean `0`
under every Dirac law vanishes at every point. -/
theorem isCompleteStatistic_dirac : IsCompleteStatistic (fun x : X ↦ Measure.dirac x) id :=
  fun g hg hzero x ↦ ae_of_all _ fun y ↦ by
    simpa [integral_dirac' _ _ hg.stronglyMeasurable] using (hzero y).2

end TauCeti
