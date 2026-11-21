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
    simp only [mem_ofPred_eq, negativeMultinomialMeasure_singleton_ne_zero_iff h.2.1 h.2.2]
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
  · -- Express the constraint as a product so the product-image lemma can match it.
    rw [show {k : ι → ℕ | ∀ i, p i = 0 → k i = 0} =
        univ.pi (fun i => {n | p i = 0 → n = 0}) by ext k; simp]
    -- The cast's body is unexposed; identify its factorization using the coordinate API.
    rw [show multinomialToEuclidean (ι := ι) =
        (EuclideanSpace.equiv ι ℝ).symm ∘ Pi.map (fun _ => (Nat.cast : ℕ → ℝ)) by
          ext k i
          exact multinomialToEuclidean_apply k i]
    rw [image_comp, piMap_image_univ_pi,
      (EuclideanSpace.equiv ι ℝ).symm.image_eq_preimage_symm]
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_ofPred_eq]
    apply forall_congr'
    intro i
    by_cases hi : p i = 0
    · have hzero : x i = 0 → x i ∈ range (Nat.cast : ℕ → ℝ) :=
        fun hx => ⟨0, by simp [hx]⟩
      simpa [hi] using hzero
    · simp [hi]
  · exact image_empty _

end TauCeti.Probability
