/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

import TauCeti.Probability.Moments.Determinacy

/-!
# Local Laplace determinacy on real inner product spaces

A finite measure with exponential moments on a neighbourhood of zero is determined by its
Laplace transform there. The proof uses scalar MGF determinacy for each real projection and
Mathlib's characteristic-function uniqueness theorem.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), proof of Theorem 2.12.
* M. J. Schervish, *Theory of Statistics* (1995), proof of Theorem 2.74.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Topology

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ ν : Measure E}

/-- Laplace transforms agreeing near zero determine a finite measure on a complete,
second-countable real inner product space. Exponential integrability near zero is
only required of the first measure. -/
theorem ext_of_integral_exp_inner_eq [IsFiniteMeasure ν]
    (hint : ∀ᶠ u in 𝓝 (0 : E), Integrable (fun x ↦ exp ⟪u, x⟫) μ)
    (heq : (fun u ↦ ∫ x, exp ⟪u, x⟫ ∂μ) =ᶠ[𝓝 (0 : E)]
      (fun u ↦ ∫ x, exp ⟪u, x⟫ ∂ν)) :
    μ = ν := by
  have hμ : IsFiniteMeasure μ := by
    simpa [integrable_const_iff] using hint.self_of_nhds
  apply Measure.ext_of_charFun
  funext y
  let proj : E → ℝ := fun x ↦ ⟪x, y⟫
  have hmeas : Measurable proj := by fun_prop
  have hline : Tendsto (fun t : ℝ ↦ t • y) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ t • y) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hline_inner (t : ℝ) (x : E) : ⟪t • y, x⟫ = t * proj x := by
    simp only [proj, real_inner_smul_left, real_inner_comm y x]
  have hproj : μ.map proj = ν.map proj := by
    apply TauCeti.Measure.ext_of_mgf
    · rw [mem_interior_iff_mem_nhds]
      filter_upwards [hline.eventually hint] with t ht
      have hmap := integrable_map_measure (g := fun s : ℝ ↦ exp (t * s))
        (by fun_prop) (μ := μ) hmeas.aemeasurable
      exact hmap.mpr (by simpa only [hline_inner, Function.comp_def] using ht)
    · filter_upwards [hline.eventually heq] with t ht
      have hm : AEStronglyMeasurable (fun s : ℝ ↦ exp (t * s)) (μ.map proj) := by fun_prop
      have hn : AEStronglyMeasurable (fun s : ℝ ↦ exp (t * s)) (ν.map proj) := by fun_prop
      simpa only [mgf, id_eq, integral_map hmeas.aemeasurable hm,
        integral_map hmeas.aemeasurable hn, Function.comp_def, hline_inner] using ht
  simpa only [Measure.map_id] using
    calc
      charFun (μ.map id) y = charFun (μ.map proj) 1 :=
        charFun_map_eq_charFun_map_inner_one aemeasurable_id y
      _ = charFun (ν.map proj) 1 := by rw [hproj]
      _ = charFun (ν.map id) y :=
        (charFun_map_eq_charFun_map_inner_one aemeasurable_id y).symm

end MeasureTheory.Measure
