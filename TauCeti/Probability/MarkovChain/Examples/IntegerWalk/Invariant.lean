/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerHarmonic
public import Mathlib.Probability.Kernel.Invariance
public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Basic
import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Classification
import TauCeti.Probability.MarkovChain.Invariant

/-!
# No finite invariant law for nearest-neighbor integer walks

For any kernel on `ℤ` taking a unit step in either direction with equal probability, every finite
invariant measure is zero (`ProbabilityTheory.Kernel.Invariant.eq_zero_of_symmetric_int_steps`);
this row-level criterion applies to any construction of the symmetric walk directly from integer
harmonicity.

More generally, because every nearest-neighbor integer walk `integerWalk p` (`p : unitInterval`)
has no positive recurrent states (`TauCeti.Probability.integerWalk_not_isPositiveRecurrent`),
every finite `(integerWalk p)`-invariant measure is zero
(`ProbabilityTheory.Kernel.Invariant.eq_zero_of_integerWalk`) and no `integerWalk p` admits an
invariant probability law (`TauCeti.Probability.not_integerWalk_invariant_of_isProbabilityMeasure`),
for symmetric and biased parameters alike (including the deterministic endpoints `0` and `1`).

See J. R. Norris, *Markov Chains* (1997), §§1.6–1.7.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal

namespace ProbabilityTheory.Kernel.Invariant

/-- A finite invariant measure for symmetric nearest-neighbor walk on `ℤ` is zero.
Consequently an invariant probability cannot exist. No normalization of the
candidate invariant measure is required. -/
theorem eq_zero_of_symmetric_int_steps {κ : Kernel ℤ ℤ} {μ : Measure ℤ}
    [IsFiniteMeasure μ] (h : κ.Invariant μ)
    (hκ : ∀ z, κ z = (2 : ℝ≥0∞)⁻¹ • Measure.dirac (z + 1) +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (z - 1)) : μ = 0 := by
  apply μ.eq_zero_of_eq_average_int_translates
  calc
    μ = μ.bind κ := h.def.symm
    _ = _ := by
      ext s hs
      rw [Measure.bind_apply hs κ.aemeasurable]
      simp_rw [hκ, add_apply, smul_apply, smul_eq_mul]
      rw [lintegral_add_left (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _)]
      congr 1 <;> congr 1
      all_goals
        rw [← Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
          Measure.bind_dirac_eq_map μ (measurable_of_countable _)]

/-- Every finite invariant measure of any nearest-neighbor integer walk is zero. -/
theorem eq_zero_of_integerWalk {p : unitInterval} {μ : Measure ℤ} [IsFiniteMeasure μ]
    (hμ : (integerWalk p).Invariant μ) :
    μ = 0 :=
  hμ.eq_zero_of_forall_not_isPositiveRecurrent (integerWalk_not_isPositiveRecurrent p)

end ProbabilityTheory.Kernel.Invariant

namespace TauCeti.Probability

/-- No nearest-neighbor integer walk admits an invariant probability measure. -/
theorem not_integerWalk_invariant_of_isProbabilityMeasure (p : unitInterval) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] :
    ¬ (integerWalk p).Invariant μ :=
  Kernel.not_invariant_of_forall_not_isPositiveRecurrent (integerWalk_not_isPositiveRecurrent p) μ

end TauCeti.Probability
