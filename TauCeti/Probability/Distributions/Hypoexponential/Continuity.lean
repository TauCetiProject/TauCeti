/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Transforms
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak continuity of hypoexponential laws

For a fixed finite index type, the sum of independent exponential variables depends jointly
weakly continuously on its positive rates. Coincident rates are included, and the empty
family is the constant Dirac law at zero.

Convergent positive rate families with positive limiting rates therefore give weakly
convergent sum laws, including when distinct rates approach a common positive value.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Hypoexponential laws vary jointly weakly continuously with their positive rates,
including when rates coincide and when the index type is empty. -/
theorem continuous_hypoexponentialMeasure :
    Continuous (Y := ProbabilityMeasure ℝ)
      (fun r : {r : ι → ℝ // ∀ i, 0 < r i} ↦
        (⟨hypoexponentialMeasure r.1,
          isProbabilityMeasure_hypoexponentialMeasure r.2⟩ : ProbabilityMeasure ℝ)) := by
  apply continuous_iff_seqContinuous.2
  intro r a hr
  -- Mathlib's Lévy convergence theorem.
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n ↦ ⟨hypoexponentialMeasure (r n).1,
      isProbabilityMeasure_hypoexponentialMeasure (r n).2⟩)
  intro t
  simp only [ProbabilityMeasure.coe_mk, charFun_hypoexponentialMeasure (r _).2,
    charFun_hypoexponentialMeasure a.2]
  apply tendsto_finsetProd
  intro i _
  have hi : Tendsto (fun n ↦ ((r n).1 i : ℂ)) atTop (𝓝 (a.1 i : ℂ)) := by
    have hc : Continuous (fun r : {r : ι → ℝ // ∀ i, 0 < r i} ↦ (r.1 i : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)
    exact (hc.tendsto a).comp hr
  refine hi.div (hi.sub tendsto_const_nhds) ?_
  intro h
  exact (a.2 i).ne' (by simpa using congrArg Complex.re h)

end TauCeti.Probability
