/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.StdSimplex
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Parameter measurability of the multinomial distribution

The multinomial law is a measurable function of its parameters, the sample size `n : ℕ` and the
probability vector `p : StdSimplex ℝ≥0 ι`, the simplex carrying the σ-algebra induced by its
weight vector. This is what lets the multinomial law be used with random parameters: it is a
measurable map into the Giry space, hence a kernel from the parameter space.

## Main results

* `TauCeti.Probability.measurable_multinomialWeight` — each multinomial weight is a measurable
  function of the weight vector;
* `TauCeti.Probability.measurable_multinomialMeasure` — the law is a measurable function of the
  sample size and the probability vector jointly.
-/

public section

noncomputable section

open Convexity MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- Each multinomial weight is a measurable function of the weight vector. -/
@[fun_prop]
theorem measurable_multinomialWeight (k : ι → ℕ) :
    Measurable fun w : ι → ℝ≥0 => multinomialWeight w k := by
  simp_rw [multinomialWeight_def]
  fun_prop

open Classical in
/-- The multinomial weighted Dirac sum at an arbitrary weight vector is measurable in the weight
vector. Its total mass is `(∑ i, w i) ^ n`, so it is proof machinery rather than a probability
family; at the weights of a probability vector it is `multinomialMeasure`. -/
private theorem measurable_sum_multinomialWeight_smul_dirac (n : ℕ) :
    Measurable fun w : ι → ℝ≥0 =>
      ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeight w k • Measure.dirac k := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  fun_prop

open Classical in
/-- **Parameter measurability of the multinomial law**: it is a measurable function of the sample
size and the probability vector jointly. -/
@[fun_prop]
theorem measurable_multinomialMeasure :
    Measurable fun q : ℕ × StdSimplex ℝ≥0 ι => multinomialMeasure q.1 q.2 := by
  have h : (fun q : StdSimplex ℝ≥0 ι × ℕ => multinomialMeasure q.2 q.1)
      = fun q => ∑ k ∈ Finset.piAntidiag Finset.univ q.2,
          multinomialWeight q.1.weights k • Measure.dirac k := by
    funext q; rw [multinomialMeasure_def]
  have hswap : Measurable fun q : StdSimplex ℝ≥0 ι × ℕ => multinomialMeasure q.2 q.1 := by
    rw [h]
    exact measurable_from_prod_countable_left fun n =>
      (measurable_sum_multinomialWeight_smul_dirac n).comp StdSimplex.measurable_toFun_comp_weights
  exact hswap.comp measurable_swap

end Probability

end TauCeti
