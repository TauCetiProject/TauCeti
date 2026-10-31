/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic

/-!
# Conditioning a function of a known and an independent variable

Let `m` be a sub-σ-algebra, `X` an `m`-measurable random variable and `Y` a random variable
independent of `m`. Given the information in `m`, the value of `X` is known while `Y` keeps its
law, so the conditional expectation of `f (X, Y)` is obtained by freezing `X` and integrating `Y`
out:

`E[f (X, Y) | m] = (fun x ↦ E[f (x, Y)]) ∘ X`  almost everywhere.

This is the computation behind every Markov property of a process with independent increments:
the state at a later time is a function of the present state, which is known, and of an increment
independent of the past.

The proof checks the defining property on each event `A` of `m`: restricted to `A`, the joint law
of `X` and `Y` is the product of the restricted law of `X` and the law of `Y`, and Fubini's
theorem integrates `Y` out first.

## Main declarations

* `TauCeti.Probability.map_restrict_prodMk_eq_prod_of_indep`: on an event of `m`, the joint law
  of `X` and `Y` is a product measure.
* `TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`: the conditional expectation
  of `f (X, Y)` given `m`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  Lemma 2.3.4 (the Independence Lemma).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α β E : Type*} {m mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → α} {Y : Ω → β}

/-- Restricted to an event `A` of `m`, the joint law of an `m`-measurable `X` and of a `Y`
independent of `m` is the product of the law of `X` under `μ.restrict A` and the law of `Y`. -/
theorem map_restrict_prodMk_eq_prod_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {A : Set Ω} (hA : MeasurableSet[m] A) :
    (μ.restrict A).map (fun ω ↦ (X ω, Y ω)) = ((μ.restrict A).map X).prod (μ.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.map_apply (hX'.prodMk hY) (hs.prod ht), Measure.map_apply hX' hs,
    Measure.map_apply hY ht, Measure.restrict_apply ((hX'.prodMk hY) (hs.prod ht)),
    Measure.restrict_apply (hX' hs), Set.mk_preimage_prod, Set.inter_right_comm, Set.inter_comm,
    (Indep_iff _ _ μ).1 hindep _ _ ⟨t, ht, rfl⟩ ((hX hs).inter hA), mul_comm]

/-- **Freezing the known variable.** If `X` is `m`-measurable and `Y` is independent of `m`, the
conditional expectation of `f (X, Y)` given `m` is almost everywhere the integral of
`y ↦ f (X ω, y)` against the law of `Y`. -/
theorem condExp_comp_prodMk_ae_eq_integral_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → E}
    (hf : StronglyMeasurable f) (hint : Integrable (fun ω ↦ f (X ω, Y ω)) μ) :
    μ[fun ω ↦ f (X ω, Y ω) | m] =ᵐ[μ] fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  have hXY : Measurable fun ω ↦ (X ω, Y ω) := hX'.prodMk hY
  have hg : StronglyMeasurable fun x ↦ ∫ y, f (x, y) ∂(μ.map Y) := hf.integral_prod_right'
  -- On an event `A` of `m`, Fubini's theorem for the product law integrates `Y` out first.
  have key (A : Set Ω) (hA : MeasurableSet[m] A) :
      IntegrableOn (fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y)) A μ ∧
        ∫ ω in A, ∫ y, f (X ω, y) ∂(μ.map Y) ∂μ = ∫ ω in A, f (X ω, Y ω) ∂μ := by
    have hprod := map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA
    have hfi : Integrable f (((μ.restrict A).map X).prod (μ.map Y)) := by
      rw [← hprod, integrable_map_measure hf.aestronglyMeasurable hXY.aemeasurable]
      exact hint.integrableOn
    refine ⟨(integrable_map_measure hg.aestronglyMeasurable hX'.aemeasurable).1
      hfi.integral_prod_left, ?_⟩
    rw [← integral_map hXY.aemeasurable hf.aestronglyMeasurable, hprod, integral_prod _ hfi,
      integral_map hX'.aemeasurable hg.aestronglyMeasurable]
  exact (ae_eq_condExp_of_forall_setIntegral_eq (g := fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y)) hm hint
    (fun A hA _ ↦ (key A hA).1) (fun A hA _ ↦ (key A hA).2)
    (hg.comp_measurable hX).aestronglyMeasurable).symm

end TauCeti.Probability
