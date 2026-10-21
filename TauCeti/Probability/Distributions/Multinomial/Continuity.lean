/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.StdSimplex
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Weak continuity of multinomial laws

The multinomial law varies weakly continuously with its trial count and probability vector.
The trial count has the discrete topology, and the finite simplex has its weight-coordinate
topology. Zero-weight cells and zero trials are included. Thus taking limits of valid parameters
does not require that every category have positive probability.

The proof uses the finite weighted-sum integral formula for the multinomial law and Mathlib's
`ProbabilityMeasure.continuous_iff_forall_continuous_integral`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Multinomial laws depend jointly weakly continuously on their trial count and cell weights,
including zero trials and zero-weight cells. -/
theorem continuous_multinomialMeasure :
    Continuous (Y := ProbabilityMeasure (ι → ℕ)) (fun q : ℕ × StdSimplex ℝ≥0 ι ↦
      (⟨multinomialMeasure q.1 q.2, isProbabilityMeasure_multinomialMeasure q.1 q.2⟩ :
        ProbabilityMeasure (ι → ℕ))) := by
  classical
  apply continuous_prod_of_discrete_left.2
  intro n
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  simp only [ProbabilityMeasure.coe_mk, integral_multinomialMeasure, multinomialWeightReal_def,
    smul_eq_mul]
  fun_prop

/-- Continuous trial counts and probability vectors give a weakly continuous multinomial
family on any topological parameter space. -/
@[fun_prop]
theorem _root_.Continuous.multinomialMeasure {X : Type*} [TopologicalSpace X]
    {n : X → ℕ} {p : X → StdSimplex ℝ≥0 ι} (hn : Continuous n) (hp : Continuous p) :
    Continuous (Y := ProbabilityMeasure (ι → ℕ)) (fun x ↦
      (⟨multinomialMeasure (n x) (p x), isProbabilityMeasure_multinomialMeasure (n x) (p x)⟩ :
        ProbabilityMeasure (ι → ℕ))) :=
  continuous_multinomialMeasure.comp (hn.prodMk hp)

end TauCeti.Probability
