/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Completeness.Basic
public import TauCeti.Statistics.ExponentialFamily.Basic

import TauCeti.MeasureTheory.Function.StronglyMeasurable.AEScalarTests
import TauCeti.Probability.Moments.LaplaceDeterminacy.InnerProduct

/-!
# Completeness of natural exponential families

The natural statistic `T` of a natural exponential family is complete for the family laws
`exponentialFamilyMeasure ν T η` with natural parameter `η` in a subset `U` of the natural
parameter space with nonempty interior: for every measurable `g` such that `g ∘ T` is integrable
with zero mean under every family law, `g ∘ T = 0` almost everywhere under each family law. If
`U` is empty, there is nothing to prove.

For the proof, fix `η₀` in the interior of `U`. Integrability of `exp ⟪η, T⟫` for `η` near `η₀`
makes every projection `⟪u, T⟫` almost everywhere measurable, hence `T` itself. For `η` near
`η₀`, `exp ⟪η, T⟫ * g ∘ T` is integrable with vanishing Bochner integral against `ν`; the signed
form of Laplace determinacy, applied after the shift by `η₀` to the law of `T` under `ν`, gives
`g ∘ T = 0` `ν`-almost everywhere, and every family law is absolutely continuous with respect
to `ν`.

## Main results

* `TauCeti.isCompleteStatistic_exponentialFamilyMeasure`: completeness of the natural statistic
  on a set of natural parameters with nonempty interior.

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
the family laws `exponentialFamilyMeasure ν T η` with natural parameter `η` in a subset `U` of the
natural parameter space whose interior is nonempty when `U` is, for instance a nonempty open
set. No measurability of `T` is assumed: it follows from the integrability of the exponential
weights near an interior point. -/
theorem isCompleteStatistic_exponentialFamilyMeasure {ν : Measure X} (T : X → E) (U : Set E)
    (hU : U.Nonempty → (interior U).Nonempty) (hUN : U ⊆ naturalParameterSpace ν T) :
    IsCompleteStatistic (fun η : U ↦ exponentialFamilyMeasure ν T η.val) T := by
  rw [isCompleteStatistic_iff]
  rintro g hg hzero ⟨η, hη⟩
  obtain ⟨η₀, hη₀⟩ := hU ⟨η, hη⟩
  have hev : ∀ᶠ u in 𝓝 (0 : E), η₀ + u ∈ U :=
    (continuous_const_add η₀).tendsto' 0 η₀ (add_zero η₀) |>.eventually
      (mem_interior_iff_mem_nhds.mp hη₀)
  -- `T` is a.e. measurable: each projection `⟪u, T⟫` is a difference quotient of the
  -- a.e. measurable exponents `⟪η₀ + ε • u, T⟫ = log (exp ⟪η₀ + ε • u, T⟫)`.
  have hlin (ζ : E) (hζ : ζ ∈ U) : AEMeasurable (fun x ↦ ⟪ζ, T x⟫) ν := by
    simpa only [Function.comp_def, log_exp] using measurable_log.comp_aemeasurable
      (mem_naturalParameterSpace.mp (hUN hζ)).aestronglyMeasurable.aemeasurable
  have hT : AEMeasurable T ν := by
    refine (aestronglyMeasurable_of_forall_aemeasurable_inner fun u ↦ ?_).aemeasurable
    have hsmul : Tendsto (fun ε : ℝ ↦ ε • u) (𝓝[≠] 0) (𝓝 0) :=
      ((Continuous.tendsto' (f := fun ε : ℝ ↦ ε • u) (by fun_prop) 0 0 (by simp))).mono_left
        nhdsWithin_le_nhds
    obtain ⟨ε, hεU, hε⟩ := ((hsmul.eventually hev).and self_mem_nhdsWithin).exists
    have heq : (fun x ↦ ⟪u, T x⟫) =
        fun x ↦ ε⁻¹ * (⟪η₀ + ε • u, T x⟫ - ⟪η₀, T x⟫) := by
      ext x
      have hε : ε ≠ 0 := hε
      rw [inner_add_left, real_inner_smul_left]
      field_simp
      ring
    rw [heq]
    exact ((hlin _ hεU).sub (hlin _ (by simpa using hev.self_of_nhds))).const_mul _
  have key (ζ : E) (hζ : ζ ∈ U) :
      Integrable (fun x ↦ exp ⟪ζ, T x⟫ * g (T x)) ν ∧ ∫ x, exp ⟪ζ, T x⟫ * g (T x) ∂ν = 0 :=
    by simpa only [smul_eq_mul, Function.comp_apply] using
      And.intro ((integrable_exponentialFamilyMeasure_iff (hUN hζ)).mp (hzero ⟨ζ, hζ⟩).1)
        ((integral_exponentialFamilyMeasure_eq_zero_iff (hUN hζ)).mp (hzero ⟨ζ, hζ⟩).2)
  -- Shift the parameter to `η₀` and pass to the law of `T` under `ν`.
  have hshift (u t : E) : exp ⟪u, t⟫ * (exp ⟪η₀, t⟫ * g t) = exp ⟪η₀ + u, t⟫ * g t := by
    rw [inner_add_left, exp_add]
    ring
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
