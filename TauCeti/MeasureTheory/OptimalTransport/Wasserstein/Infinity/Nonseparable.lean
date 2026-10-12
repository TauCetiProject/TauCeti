/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.Real.Cardinality

/-!
# A nonseparable infinite-exponent Wasserstein space

Even when the ground space is complete and separable, its finite-moment Wasserstein space at
exponent `∞` need not be separable. On `ℕ`, the Bernoulli laws supported on `{0, 1}` form an
uncountable family whose distinct members are at least unit distance apart in `W_∞`: every
coupling that moves mass less than one unit almost everywhere must be diagonal, and therefore
has equal marginals. Thus `P_∞(ℕ)` contains uncountably many disjoint open balls.

The separation argument uses
`TauCeti.eq_of_pairwise_edist_ge_of_wassersteinEDist_top_lt`, which applies to any
uniformly separated metric space. This example explains why the finite-exponent
separability and Borel-space arguments cannot simply be used at exponent `∞`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

private theorem hasFiniteMoment_bernoulliMeasure (p : unitInterval) :
    HasFiniteMoment ∞ (bernoulliMeasure (0 : ℕ) 1 p) := by
  have h : ∀ᵐ n ∂bernoulliMeasure (0 : ℕ) 1 p, n ∈ ({0, 1} : Finset ℕ) := by
    apply mem_ae_iff.mpr
    simp [bernoulliMeasure_def]
  have : IsFiniteMeasure (bernoulliMeasure (0 : ℕ) 1 p) := inferInstance
  exact hasFiniteMoment_of_ae_mem_finset (p := ∞) 0 h

private def bernoulliLaw (p : unitInterval) : WassersteinSpace ∞ ℕ :=
  WassersteinSpace.mk ⟨bernoulliMeasure (0 : ℕ) 1 p, inferInstance⟩
    (hasFiniteMoment_bernoulliMeasure p)

private theorem bernoulliLaw_separated {p q : unitInterval} (hpq : p ≠ q) :
    (1 : ℝ≥0∞) ≤ edist (bernoulliLaw p) (bernoulliLaw q) := by
  by_contra h
  have hlt : edist (bernoulliLaw p) (bernoulliLaw q) < 1 := lt_of_not_ge h
  rw [WassersteinSpace.edist_def] at hlt
  have hsep : Pairwise (fun x y : ℕ ↦ (1 : ℝ≥0∞) ≤ edist x y) := by
    intro x y hxy
    rw [edist_dist]
    simpa using ENNReal.ofReal_le_ofReal (Nat.pairwise_one_le_dist hxy)
  have hm := eq_of_pairwise_edist_ge_of_wassersteinEDist_top_lt hsep hlt
  have hpm : WassersteinSpace.toProbabilityMeasure (bernoulliLaw p) =
      WassersteinSpace.toProbabilityMeasure (bernoulliLaw q) := Subtype.ext hm
  -- The inclusion into probability measures is opaque, so invoke its characteristic lemma.
  rw [show WassersteinSpace.toProbabilityMeasure (bernoulliLaw p) =
        (⟨bernoulliMeasure (0 : ℕ) 1 p, inferInstance⟩ : ProbabilityMeasure ℕ) from
      WassersteinSpace.coe_mk _ _,
    show WassersteinSpace.toProbabilityMeasure (bernoulliLaw q) =
        (⟨bernoulliMeasure (0 : ℕ) 1 q, inferInstance⟩ : ProbabilityMeasure ℕ) from
      WassersteinSpace.coe_mk _ _] at hpm
  have hv := congrArg (fun m : ProbabilityMeasure ℕ ↦ (m : Measure ℕ).real {0}) hpm
  apply hpq
  apply Subtype.ext
  simpa using hv

/-- The infinite-exponent Wasserstein space of laws on `ℕ` is not separable. The Bernoulli
laws on `{0, 1}` supply an uncountable family with pairwise `W_∞` distance at least one. -/
theorem WassersteinSpace.not_separableSpace_top_nat :
    ¬ TopologicalSpace.SeparableSpace (WassersteinSpace ∞ ℕ) := by
  intro hs
  let U : unitInterval → Set (WassersteinSpace ∞ ℕ) :=
    fun p ↦ Metric.eball (bernoulliLaw p) ((1 / 2 : ℝ≥0) : ℝ≥0∞)
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro p q hpq
    apply Metric.eball_disjoint
    convert bernoulliLaw_separated hpq using 1
    rw [← ENNReal.coe_add]
    norm_num
  have hcount : Countable unitInterval :=
    hdisj.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_eball)
      (fun p ↦ ⟨bernoulliLaw p, Metric.mem_eball_self (by norm_num)⟩)
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp (by simpa [unitInterval] using hcount)
  have := Cardinal.Real.Icc_countable_iff.mp hIcc
  linarith

end TauCeti
