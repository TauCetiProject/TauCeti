/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.Prod
public import TauCeti.MeasureTheory.Measure.NNReal

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
