/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Transforms
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak continuity of hyperexponential laws

A finite exponential mixture depends jointly weakly continuously on its simplex weights
and rates whenever every active rate is positive. Inactive rates may be arbitrary,
including zero or negative, and components may appear or disappear as their weights vary.

For valid parameter families converging to a valid limit, this gives weak convergence of
the mixture laws, including limits where some weights vanish and the number of active
components decreases.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Hyperexponential laws vary jointly weakly continuously with weights and rates on their
full probability domain. Zero-weight components may have arbitrary rates. -/
theorem continuous_hyperexponentialMeasure :
    Continuous (Y := ProbabilityMeasure ℝ)
      (fun q : {q : Convexity.StdSimplex ℝ≥0 ι × (ι → ℝ) //
          ∀ i, 0 < q.1.weights i → 0 < q.2 i} ↦
        (⟨hyperexponentialMeasure q.1.1 q.1.2,
          isProbabilityMeasure_hyperexponentialMeasure q.2⟩ : ProbabilityMeasure ℝ)) := by
  let _ : FirstCountableTopology (Convexity.StdSimplex ℝ≥0 ι) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights_nnreal (ι := ι)).firstCountableTopology
  apply continuous_iff_seqContinuous.2
  intro q a hq
  have hparam := (continuous_subtype_val.tendsto a).comp hq
  let _ (n : ℕ) := isProbabilityMeasure_hyperexponentialMeasure (q n).2
  let _ := isProbabilityMeasure_hyperexponentialMeasure a.2
  -- Mathlib's Lévy convergence theorem.
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n ↦ ⟨hyperexponentialMeasure (q n).1.1 (q n).1.2,
      isProbabilityMeasure_hyperexponentialMeasure (q n).2⟩)
  intro t
  by_cases ht : t = 0
  · subst t
    simp
  simp only [ProbabilityMeasure.coe_mk, charFun_hyperexponentialMeasure (q _).2,
    charFun_hyperexponentialMeasure a.2]
  apply tendsto_finsetSum
  intro i _
  have hr : Tendsto (fun n ↦ ((q n).1.2 i : ℂ)) atTop (𝓝 (a.1.2 i : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pi_nhds.mp ((continuous_snd.tendsto a.1).comp hparam) i)
  have hw : Tendsto (fun n ↦ ((q n).1.1.weights i : ℂ)) atTop
      (𝓝 (a.1.1.weights i : ℂ)) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (Convexity.StdSimplex.continuous_weights_apply_nnreal i))).continuousAt.tendsto.comp
        ((continuous_fst.tendsto a.1).comp hparam)
  refine (hw.mul hr).div (hr.sub tendsto_const_nhds) ?_
  intro h
  have him := congrArg Complex.im h
  exact ht (by simpa using him)

end TauCeti.Probability
