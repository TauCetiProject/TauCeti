/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Topological support of negative-multinomial laws

At positive shape and valid weights, the negative-multinomial support consists of all count
vectors vanishing in the zero-weight categories. There is no constraint on the total count.
Shape zero gives singleton support at zero, and invalid parameters give empty support.

After casting into Euclidean space, the support is still a discrete lattice: each coordinate
is a nonnegative integer, and zero-weight coordinates vanish. It is not the nonnegative
orthant. The count-vector cast is a closed embedding, so no additional limit points appear.
The formulas include empty category types and success weight one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley (1997).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The native topological support, including invalid parameters and shape zero. At positive
shape the only constraints on counts come from the zero-weight categories. -/
@[simp]
theorem support_negativeMultinomialMeasure (r p₀ : ℝ) (p : ι → ℝ≥0) :
    (negativeMultinomialMeasure r p₀ p).support =
      if 0 ≤ r ∧ 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1 then
        if r = 0 then {0} else {k | ∀ i, p i = 0 → k i = 0}
      else ∅ := by
  classical
  split_ifs with h hr
  · subst r
    rw [negativeMultinomialMeasure_zero h.2.1 h.2.2]
    simp [Measure.support_dirac]
  · rw [Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simp only [mem_ofPred_eq, negativeMultinomialMeasure_singleton_ne_zero_iff h.1 h.2.1 h.2.2]
    simp [hr, lt_of_le_of_ne h.1 (Ne.symm hr)]
  · rw [negativeMultinomialMeasure_eq_zero_of_invalid h]
    exact Measure.support_zero

/-- The Euclidean topological support in intrinsic coordinates: every coordinate is a
nonnegative integer, and zero-weight coordinates vanish. Shape zero gives `{0}` and invalid
parameters give empty support. -/
@[simp]
theorem support_map_multinomialToEuclidean_negativeMultinomialMeasure
    (r p₀ : ℝ) (p : ι → ℝ≥0) :
    ((negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean).support =
      if 0 ≤ r ∧ 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1 then
        if r = 0 then {0}
        else {x | ∀ i, x i ∈ range (Nat.cast : ℕ → ℝ) ∧ (p i = 0 → x i = 0)}
      else ∅ := by
  classical
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    isClosedEmbedding_multinomialToEuclidean.continuous,
    (isClosedEmbedding_multinomialToEuclidean.isClosedMap _
      Measure.isClosed_support).closure_eq, support_negativeMultinomialMeasure]
  split_ifs with h hr
  · simp only [image_singleton]
    congr 1
    ext i
    simp
  · ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact fun i => ⟨⟨k i, (multinomialToEuclidean_apply k i).symm⟩,
        fun hi => by simp [hk i hi]⟩
    · intro hx
      choose k hk using fun i => (hx i).1
      refine ⟨k, fun i hi => ?_, ?_⟩
      · exact Nat.cast_eq_zero.mp ((hk i).trans ((hx i).2 hi))
      · ext i
        exact (multinomialToEuclidean_apply k i).trans (hk i)
  · exact image_empty _

end TauCeti.Probability
