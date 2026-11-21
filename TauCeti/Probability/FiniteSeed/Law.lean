/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Probability.FiniteSeed.Amplification
public import Mathlib.Probability.Distributions.Uniform

/-!
# The finite counting model is Mathlib's uniform probability law

This identifies the cardinality-defined probability with the measure induced
by `PMF.uniformOfFintype`. Every event on a finite seed space is measurable
with the discrete measurable space. A uniformly drawn seed sequence is the
uniform law on a finite function space.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace TauCeti.FiniteSeeds

variable (S : Type*) [Fintype S] [Nonempty S]

theorem uniformProbability_eq_uniformOuterMeasure (event : S → Prop) :
    uniformProbability S event =
      ((PMF.uniformOfFintype S).toOuterMeasure {s | event s}).toReal := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply (α := S) {s | event s}]
  simp [uniformProbability, ENNReal.toReal_div, Fintype.card_subtype]

theorem uniformProbability_eq_uniformMeasure (event : S → Prop) :
    letI : MeasurableSpace S := ⊤
    uniformProbability S event =
      ((PMF.uniformOfFintype S).toMeasure {s | event s}).toReal := by
  classical
  let : MeasurableSpace S := ⊤
  rw [PMF.toMeasure_uniformOfFintype_apply (α := S) {s | event s} (by trivial)]
  simp [uniformProbability, ENNReal.toReal_div, Fintype.card_subtype]

theorem uniformMeasure_failure_le_half_pow (accepts : S → Prop)
    (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤ uniformProbability S accepts) :
    letI : MeasurableSpace (Fin (k * R) → S) := ⊤
    ((PMF.uniformOfFintype (Fin (k * R) → S)).toMeasure
      {seeds | ∀ i, ¬accepts (seeds i)}).toReal ≤ (1 / 2 : ℝ) ^ k := by
  rw [← uniformProbability_eq_uniformMeasure]
  exact uniformProbability_failure_le_half_pow S accepts R k hR haccepts


end TauCeti.FiniteSeeds
