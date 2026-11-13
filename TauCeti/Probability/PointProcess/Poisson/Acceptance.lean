/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.Prod
public import TauCeti.MeasureTheory.Measure.NNReal
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Poisson acceptance regions and monotone coupling

Restrict a Poisson random measure on a product to a measurable acceptance region, then project
onto the first coordinate. The resulting intensity is the ground measure weighted by the
masses of the vertical sections. For Lebesgue marks and a region below a measurable density,
this is precisely the measure with that density. Infinite density values are allowed.

Using the same Poisson measure for two ordered densities gives an ordered pair of random
measures on the original sample space. This is the acceptance-region construction of monotone
Poisson coupling; it does not assert independence of the two outputs or construct the driver.
No simplicity, atomlessness of the ground intensity, or topology on its space is required.

The construction follows G. Last and M. Penrose, *Lectures on the Poisson Process* (2018),
Chapter 5 (restriction, mapping, and thinning).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  {P : Measure Ω} {Λ : Measure X} {Q : Measure E} {M : Ω → Measure (X × E)}

/-- Projecting the accepted occurrences of a product-intensity Poisson random measure is
Poisson, with density equal to the mark measure of each acceptance section. Multiplicities
are retained, and the acceptance region need not have finite intensity. -/
theorem IsPoissonRandomMeasure.acceptance [SFinite Q]
    (hM : IsPoissonRandomMeasure P M (Λ.prod Q))
    {A : Set (X × E)} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict A).map Prod.fst)
      (Λ.withDensity fun x ↦ Q (Prod.mk x ⁻¹' A)) := by
  simpa only [Measure.map_fst_restrict_prod_eq_withDensity Λ Q hA] using
    (hM.restrict hA).map measurable_fst

/-- Selecting a measurable mark set from a product-intensity Poisson measure and projecting
onto the ground space multiplies the intensity by the mass of that mark set. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod [SFinite Q]
    (hM : IsPoissonRandomMeasure P M (Λ.prod Q))
    {A : Set E} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ A)).map Prod.fst)
      (Q A • Λ) := by
  simpa only [mk_preimage_prod_right (mem_univ _), withDensity_const] using
    hM.acceptance (MeasurableSet.univ.prod hA)

/-- Selecting a finite-mass mark set from a scaled product intensity multiplies the ground
scale by the mass of that mark set, including scale zero. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod_smul [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • Λ).prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ A)).map Prod.fst)
      (((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • Λ) := by
  have hscale : Q A • (r : ℝ≥0∞) • Λ =
      ((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • Λ := by
    rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal hQA, mul_comm]
  simpa only [hscale] using h.acceptance_univ_prod hA

/-- Bernoulli colour selection splits a scaled ground intensity into scales `r*p` and
`r*(1-p)`, including both endpoint parameters and scale zero. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure
    {M : Ω → Measure (X × Bool)} {r : ℝ≥0} {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • Λ).prod (bernoulliMeasure true false p))) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) := by
  have hb : ((bernoulliMeasure true false p) {b}).toNNReal =
      if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p := by
    cases b
    · simpa using eq_tsub_of_add_eq (unitInterval.toNNReal_symm_add_toNNReal p)
    · simp
  simpa only [hb] using h.acceptance_univ_prod_smul (measurableSet_singleton b)

/-- Accepting a Lebesgue mark `u` exactly when `u ≤ f x` produces a Poisson random measure
with intensity `Λ.withDensity f`, including at zero and infinite values of `f`. -/
theorem IsPoissonRandomMeasure.acceptance_le
    {M : Ω → Measure (X × ℝ≥0)}
    (hM : IsPoissonRandomMeasure P M (Λ.prod nnvolume))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    IsPoissonRandomMeasure P
      (fun ω ↦ ((M ω).restrict {p | (p.2 : ℝ≥0∞) ≤ f p.1}).map Prod.fst)
      (Λ.withDensity f) := by
  have hA : MeasurableSet {p : X × ℝ≥0 | (p.2 : ℝ≥0∞) ≤ f p.1} :=
    measurableSet_le measurable_snd.coe_nnreal_ennreal (hf.comp measurable_fst)
  simpa only [preimage_ofPred_eq, nnvolume_setOf_coe_le] using hM.acceptance hA

/-- Ordered measurable densities admit an ordered Poisson coupling on the sample space of
the given product-intensity Poisson measure. The domination holds for every sample, not just
almost surely. -/
theorem IsPoissonRandomMeasure.exists_monotone_coupling
    {M : Ω → Measure (X × ℝ≥0)}
    (hM : IsPoissonRandomMeasure P M (Λ.prod nnvolume))
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hfg : f ≤ g) :
    ∃ N₁ N₂ : Ω → Measure X,
      IsPoissonRandomMeasure P N₁ (Λ.withDensity f) ∧
      IsPoissonRandomMeasure P N₂ (Λ.withDensity g) ∧ ∀ ω, N₁ ω ≤ N₂ ω := by
  refine ⟨_, _, hM.acceptance_le hf, hM.acceptance_le hg, fun ω ↦ ?_⟩
  exact Measure.map_mono
    ((M ω).restrict_mono_set fun p hp ↦ hp.trans (hfg p.1)) measurable_fst

end TauCeti.Probability
