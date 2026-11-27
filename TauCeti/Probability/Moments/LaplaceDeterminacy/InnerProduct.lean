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
Mathlib's characteristic-function uniqueness theorem. In signed form: a real function whose
products with the exponentials `exp ⟪u, ·⟫` are integrable with integral zero for all `u` near
zero vanishes almost everywhere.

## Main results

* `MeasureTheory.Measure.ext_of_integral_exp_inner_eq`: Laplace transforms agreeing near zero
  determine a finite measure.
* `MeasureTheory.ae_eq_zero_of_integral_exp_inner_mul_eq_zero`: a real function whose products
  with `exp ⟪u, ·⟫` are integrable with integral zero for all `u` near zero vanishes almost
  everywhere, for any measure.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), proof of Theorem 2.12.
* M. J. Schervish, *Theory of Statistics* (1995), proof of Theorem 2.74.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ ν : Measure E}

/-- Laplace transforms agreeing near zero determine a finite measure on a complete,
second-countable real inner product space. Exponential integrability near zero is
only required of the first measure. -/
theorem Measure.ext_of_integral_exp_inner_eq [IsFiniteMeasure ν]
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

/-- A real function `h` such that `exp ⟪u, ·⟫ * h` is integrable with integral `0` for all `u`
near zero vanishes almost everywhere. This is the signed form of
`MeasureTheory.Measure.ext_of_integral_exp_inner_eq`; the measure need not be finite. -/
theorem ae_eq_zero_of_integral_exp_inner_mul_eq_zero {h : E → ℝ}
    (hint : ∀ᶠ u in 𝓝 (0 : E), Integrable (fun x ↦ exp ⟪u, x⟫ * h x) μ)
    (hzero : ∀ᶠ u in 𝓝 (0 : E), ∫ x, exp ⟪u, x⟫ * h x ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  have hh : Integrable h μ := by simpa using hint.self_of_nhds
  -- The positive and negative parts of `h` as densities: `μ.withDensity (ofReal ∘ k)` for
  -- `k = h` and `k = -h`. Their Laplace transforms are lower integrals against `μ`.
  have hlint (k : E → ℝ) (hk : AEMeasurable k μ) (u : E) :
      ∫⁻ x, ENNReal.ofReal (exp ⟪u, x⟫) ∂μ.withDensity (fun x ↦ ENNReal.ofReal (k x)) =
        ∫⁻ x, ENNReal.ofReal (exp ⟪u, x⟫ * k x) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hk.ennreal_ofReal (by fun_prop)]
    congr with x
    rw [Pi.mul_apply, ENNReal.ofReal_mul (exp_pos _).le, mul_comm]
  have hexp (ρ : Measure E) (u : E) : AEStronglyMeasurable (fun x ↦ exp ⟪u, x⟫) ρ :=
    (by fun_prop : Continuous fun x : E ↦ exp ⟪u, x⟫).aestronglyMeasurable
  have hpos (ρ : Measure E) (u : E) : 0 ≤ᵐ[ρ] fun x ↦ exp ⟪u, x⟫ :=
    ae_of_all _ fun x ↦ (exp_pos _).le
  have hneg (u : E) (x : E) : exp ⟪u, x⟫ * -h x = -(exp ⟪u, x⟫ * h x) := mul_neg _ _
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (-h x)) :=
    isFiniteMeasure_withDensity_ofReal hh.neg.hasFiniteIntegral
  have heq : μ.withDensity (fun x ↦ ENNReal.ofReal (h x)) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (-h x)) := by
    refine Measure.ext_of_integral_exp_inner_eq ?_ ?_
    · filter_upwards [hint] with u hu
      rw [← lintegral_ofReal_ne_top_iff_integrable (hexp _ u) (hpos _ u), hlint h hh.aemeasurable]
      exact hu.lintegral_lt_top.ne
    · filter_upwards [hint, hzero] with u hu hu0
      rw [integral_eq_lintegral_of_nonneg_ae (hpos _ u) (hexp _ u),
        integral_eq_lintegral_of_nonneg_ae (hpos _ u) (hexp _ u), hlint h hh.aemeasurable,
        hlint (fun x ↦ -h x) hh.aemeasurable.neg]
      simp only [hneg]
      rwa [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu, sub_eq_zero] at hu0
  filter_upwards [(withDensity_eq_iff hh.aemeasurable.ennreal_ofReal
    hh.aemeasurable.neg.ennreal_ofReal hh.lintegral_lt_top.ne).mp heq] with x hx
  have hmax := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at hmax
  simpa [hmax] using (max_zero_sub_eq_self (h x)).symm

end MeasureTheory
