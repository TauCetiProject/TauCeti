/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Completeness.Basic
public import TauCeti.Statistics.ExponentialFamily.Basic

import TauCeti.Probability.Moments.LaplaceDeterminacy.InnerProduct

/-!
# Completeness of natural exponential families

The natural statistic `T` of a natural exponential family is complete for the family laws
`exponentialFamilyMeasure ν T η` with natural parameter `η` in an open subset of the natural
parameter space. If `g ∘ T` has mean `0` under every such law, then `exp ⟪η, T⟫ * g ∘ T` has
integral `0` against `ν` for every `η` in the open set, and the signed form of Laplace
determinacy, applied after a shift to the law of `T` under `ν`, gives `g ∘ T = 0` almost
everywhere.

## Main results

* `TauCeti.isCompleteStatistic_exponentialFamilyMeasure`: completeness of the natural statistic
  on an open set of natural parameters.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Theorem 2.12.
* J. Pfanzagl, *Parametric Statistical Theory* (1994), Theorem 1.6.10.
* M. J. Schervish, *Theory of Statistics* (1995), Theorem 2.74.

The proof is adapted from `isCompleteStatistic_withDensity_exp_inner` in the file
`CKSD/Inference/ExponentialFamily.lean` of lean-CKSD, stated there for `EuclideanSpace ℝ (Fin d)`
and explicitly normalized densities.
-/

public section

open Filter MeasureTheory Real
open scoped RealInnerProductSpace Topology

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- **Completeness of natural exponential families.** The natural statistic `T` is complete for
the family laws `exponentialFamilyMeasure ν T η` with natural parameter `η` in an open subset
`U` of the natural parameter space. -/
theorem isCompleteStatistic_exponentialFamilyMeasure (ν : Measure X) (T : X → E)
    (hT : AEMeasurable T ν) (U : Set E) (hU : IsOpen U)
    (hUN : U ⊆ naturalParameterSpace ν T) :
    IsCompleteStatistic (fun η : U ↦ exponentialFamilyMeasure ν T η.val) T := by
  rw [isCompleteStatistic_iff]
  rintro g hg hzero ⟨η₀, hη₀⟩
  have key (η : E) (hη : η ∈ U) :
      Integrable (fun x ↦ exp ⟪η, T x⟫ * g (T x)) ν ∧ ∫ x, exp ⟪η, T x⟫ * g (T x) ∂ν = 0 :=
    by simpa only [smul_eq_mul, Function.comp_apply] using
      And.intro ((integrable_exponentialFamilyMeasure_iff (hUN hη)).mp (hzero ⟨η, hη⟩).1)
        ((integral_exponentialFamilyMeasure_eq_zero_iff (hUN hη)).mp (hzero ⟨η, hη⟩).2)
  -- Shift the parameter to `η₀` and pass to the law of `T` under `ν`.
  have hshift (u t : E) : exp ⟪u, t⟫ * (exp ⟪η₀, t⟫ * g t) = exp ⟪η₀ + u, t⟫ * g t := by
    rw [inner_add_left, exp_add]
    ring
  have hev : ∀ᶠ u in 𝓝 (0 : E), η₀ + u ∈ U :=
    (continuous_const_add η₀).tendsto' 0 η₀ (add_zero η₀) |>.eventually (hU.mem_nhds hη₀)
  have hae : (fun t ↦ exp ⟪η₀, t⟫ * g t) =ᵐ[ν.map T] 0 := by
    refine ae_eq_zero_of_integral_exp_inner_mul_eq_zero ?_ ?_
    · filter_upwards [hev] with u hu
      rw [integrable_map_measure (by fun_prop) hT]
      simpa only [Function.comp_def, hshift] using (key _ hu).1
    · filter_upwards [hev] with u hu
      rw [integral_map hT (by fun_prop)]
      simpa only [hshift] using (key _ hu).2
  simp only [Filter.EventuallyEq, Pi.zero_apply] at hae
  rw [ae_map_iff hT (measurableSet_eq_fun (by fun_prop) measurable_const)] at hae
  rw [exponentialFamilyMeasure_def]
  refine (tilted_absolutelyContinuous ν _).ae_le ?_
  filter_upwards [hae] with x hx
  exact (mul_eq_zero.mp hx).resolve_left (exp_pos _).ne'

end TauCeti
