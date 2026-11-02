/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Existence of a law from convergent characteristic functions

A pointwise limit of characteristic functions of probability measures on a finite-dimensional
real inner product space is itself a characteristic function, provided it is continuous at zero.
The representing probability measure is unique, and the original sequence converges weakly to it.
In particular, constructing approximating laws and computing their characteristic-function limit
suffices to construct a limiting law; a candidate measure need not be supplied in advance.

`exists_probabilityMeasure_of_tendsto_charFun` supplies this existence form of Lévy's continuity
theorem. It complements Mathlib's `ProbabilityMeasure.tendsto_of_tendsto_charFun`, whose input
already includes a limiting probability measure. The proof uses Mathlib's
`isTightMeasureSet_of_tendsto_charFun` and `isCompact_closure_of_isTightMeasureSet` to obtain a
weak cluster limit, identifies its characteristic function by bounded-continuous integration,
and then applies Mathlib's convergence and characteristic-function uniqueness theorems.

## References

* P. Billingsley, *Probability and Measure*, third edition, Wiley, 1995, section 29
  (the continuity theorem for characteristic functions).
-/

public section

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lévy's continuity theorem, including existence.** If the characteristic functions of a
sequence of probability measures converge pointwise to a function continuous at zero, there is
a unique probability measure with that characteristic function, and the sequence converges
weakly to it. Continuity is required only at zero; normalization of the limit follows from the
probability measures in the sequence. -/
theorem exists_probabilityMeasure_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E}
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    ∃! μ₀ : ProbabilityMeasure E, charFun μ₀ = f ∧ Tendsto μ atTop (𝓝 μ₀) := by
  have htight : IsTightMeasureSet (range (fun n ↦ (μ n : Measure E))) :=
    isTightMeasureSet_of_tendsto_charFun hf h
  have hcompact : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (htight.subset (by
      rintro - ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact mem_range_self n))
  obtain ⟨μ₀, -, hcluster⟩ := hcompact (f := map μ atTop)
    (tendsto_principal.mpr (.of_forall fun n ↦ subset_closure (mem_range_self n)))
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hchar : charFun μ₀ = f := by
    funext t
    have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
      (innerProbChar t)
    simp only [← charFun_eq_integral_innerProbChar] at hint
    exact tendsto_nhds_unique hint ((h t).mono_left hU)
  refine ⟨μ₀, ⟨hchar, ProbabilityMeasure.tendsto_of_tendsto_charFun ?_⟩, ?_⟩
  · simpa only [hchar] using h
  · intro ν hν
    exact ProbabilityMeasure.toMeasure_injective (Measure.ext_of_charFun (hν.1.trans hchar.symm))

end TauCeti
