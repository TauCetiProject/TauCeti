/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic

/-!
# Exponential moments of finite mixtures

A real observable has a finite exponential moment under a finite mixture exactly when it has
one under every positive-weight component. Thus the domain is the intersection of the active
component domains; zero-weight components impose no restriction, even if their exponential
moments diverge.

On this domain the moment-generating function is the weighted sum of component mgfs. The
cumulant-generating function is the logarithm of that sum, not the weighted sum of component
cgfs. The integrability hypothesis is essential because a nonintegrable real integral is
otherwise totalized to zero.

These results apply to arbitrary component measures and real observables, including linear
statistics of vector-valued laws. No probability or measurability assumption beyond the
integrability criterion is needed.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
  {p : StdSimplex ℝ≥0 ι} {K : ι → Measure α} {X : α → ℝ} {t : ℝ}

/-- An exponential moment of a finite mixture is finite exactly when it is finite under each
positive-weight component. Zero-weight components need not have that exponential moment. -/
@[simp]
theorem mem_integrableExpSet_finiteMixtureMeasure_iff :
    t ∈ integrableExpSet X (finiteMixtureMeasure p K) ↔
      ∀ i, 0 < p.weights i → t ∈ integrableExpSet X (K i) := by
  simp only [integrableExpSet, mem_ofPred_eq, integrable_finiteMixtureMeasure_iff]

/-- The exact exponential-integrability domain of a finite mixture is the intersection of the
component domains over the indices with positive weight. -/
theorem integrableExpSet_finiteMixtureMeasure (p : StdSimplex ℝ≥0 ι)
    (K : ι → Measure α) (X : α → ℝ) :
    integrableExpSet X (finiteMixtureMeasure p K) =
      ⋂ i, ⋂ (_ : 0 < p.weights i), integrableExpSet X (K i) := by
  ext t
  simp

/-- On its exponential-integrability domain, the mgf of a finite mixture is the weighted sum
of the component mgfs. -/
theorem mgf_finiteMixtureMeasure (ht : t ∈ integrableExpSet X (finiteMixtureMeasure p K)) :
    mgf X (finiteMixtureMeasure p K) t = ∑ i, (p.weights i : ℝ) * mgf X (K i) t := by
  simpa only [mgf, smul_eq_mul] using
    integral_finiteMixtureMeasure (integrable_of_mem_integrableExpSet ht)

/-- The cgf of a finite mixture is the logarithm of the weighted sum of component mgfs, on the
common exponential-integrability domain of its positive-weight components. -/
theorem cgf_finiteMixtureMeasure (ht : t ∈ integrableExpSet X (finiteMixtureMeasure p K)) :
    cgf X (finiteMixtureMeasure p K) t =
      Real.log (∑ i, (p.weights i : ℝ) * mgf X (K i) t) := by
  rw [cgf, mgf_finiteMixtureMeasure ht]

end TauCeti.Probability
