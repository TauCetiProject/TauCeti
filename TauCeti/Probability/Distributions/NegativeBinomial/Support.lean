/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Topological support of negative-binomial laws

A negative-binomial law of positive shape and success probability strictly between zero and one
has full support on `ℕ`. Its real-cast law has support exactly the nonnegative integers, not the
whole nonnegative half-line. At shape zero or success probability one, both supports reduce to
`{0}`. Invalid parameters give empty support because the law is zero.

The support equalities below distinguish topological support from the carrying half-line used
for cdf and quantile arguments. They follow from the singleton-mass characterization in
`NegativeBinomial.Basic` and continuous pushforward of support.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {r p : ℝ}

/-- The native topological support of a valid negative-binomial law is all naturals, except at
its two Dirac boundaries. -/
@[simp]
theorem support_negativeBinomialMeasure (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    (negativeBinomialMeasure r p).support =
      if r = 0 ∨ p = 1 then {0} else univ := by
  by_cases hdeg : r = 0 ∨ p = 1
  · rw [ite_eq_left hdeg]
    rcases hdeg with rfl | rfl
    · simp [negativeBinomialMeasure_zero hp hp1]
    · simp [negativeBinomialMeasure_eq_dirac_of_successProbability_eq_one hr]
  · rw [ite_eq_right hdeg]
    apply Set.eq_univ_of_forall
    intro k
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hk : 0 < negativeBinomialMeasure r p {k} := by
      apply pos_iff_ne_zero.mpr
      apply (negativeBinomialMeasure_singleton_ne_zero_iff hr hp hp1 k).2
      exact Or.inr ⟨lt_of_le_of_ne hr (by tauto), lt_of_le_of_ne hp1 (by tauto)⟩
    exact hk.trans_le (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- Casting a valid negative-binomial law to the reals gives support exactly the nonnegative
integers, except at shape zero or success probability one, when the support is `{0}`. -/
@[simp]
theorem support_map_cast_negativeBinomialMeasure (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).support =
      if r = 0 ∨ p = 1 then {0} else range (Nat.cast : ℕ → ℝ) := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_negativeBinomialMeasure hr hp hp1]
  split_ifs
  · simp
  · rw [image_univ, Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq]

end TauCeti.Probability
