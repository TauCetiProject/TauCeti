/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Weak continuity of beta laws

The beta law varies jointly weakly continuously with its two positive shape parameters.
The statement uses `ProbabilityMeasure ℝ`, with its topology of weak convergence.

The densities can be unbounded at either endpoint. Locally in parameter space, the beta
kernel is bounded by the integrable kernel with both shapes halved. Dominated convergence
for bounded continuous test functions and continuity of the Gamma normalizer then give
continuity of the laws.

The proof uses Mathlib's bounded-continuous-test-function characterization of weak
convergence and Tau Ceti's real beta integral. For the classical beta density, see
Johnson, Kotz, and Balakrishnan, *Continuous Univariate Distributions*, volume 2, Chapter 25.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- Beta laws depend jointly weakly continuously on their positive shape parameters. -/
theorem continuous_betaMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦
      (⟨betaMeasure p.1 p.2,
        isProbabilityMeasureBeta (mem_Ioi.mp p.1.2) (mem_Ioi.mp p.2.2)⟩ :
          ProbabilityMeasure ℝ)) := by
  -- The Gamma quotient is continuous and strictly positive on the parameter domain.
  have ha : Continuous fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hb : Continuous fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦ (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hG := Real.differentiableOn_Gamma_Ioi.continuousOn
  have hB : Continuous fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦ (1 / beta p.1 p.2) := by
    simp only [beta]
    exact continuous_const.div
      (((hG.comp_continuous ha fun p ↦ p.1.2).mul
        (hG.comp_continuous hb fun p ↦ p.2.2)).div
        (hG.comp_continuous (ha.add hb) fun p ↦ add_pos p.1.2 p.2.2)
        (fun p ↦ (Real.Gamma_pos_of_pos (add_pos p.1.2 p.2.2)).ne'))
      (fun p ↦ (beta_pos p.1.2 p.2.2).ne')
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  -- Separate the normalizing constant from the kernel on the open unit interval.
  have heq (p : Ioi (0 : ℝ) × Ioi (0 : ℝ)) :
      ∫ x, f x ∂betaMeasure p.1 p.2 =
        (1 / beta p.1 p.2) * ∫ x in Ioo (0 : ℝ) 1,
          x ^ ((p.1 : ℝ) - 1) * (1 - x) ^ ((p.2 : ℝ) - 1) * f x := by
    rw [integral_betaMeasure_eq p.1.2 p.2.2]
    calc
      _ = ∫ x, (Ioo (0 : ℝ) 1).indicator (fun x ↦
          (1 / beta p.1 p.2) *
            (x ^ ((p.1 : ℝ) - 1) * (1 - x) ^ ((p.2 : ℝ) - 1) * f x)) x := by
        congr 1
        funext x
        by_cases hx : 0 < x ∧ x < 1 <;>
          simp [betaPDFReal, mem_Ioo, hx, smul_eq_mul, mul_assoc]
      _ = _ := by rw [integral_indicator measurableSet_Ioo, integral_const_mul]
  simp only [ProbabilityMeasure.coe_mk, heq]
  refine hB.mul (continuous_iff_continuousAt.2 fun p ↦ ?_)
  -- Halving the shapes gives a locally uniform integrable bound at both endpoints.
  let bound : ℝ → ℝ := fun x ↦
    ‖f‖ * (x ^ ((p.1 : ℝ) / 2 - 1) * (1 - x) ^ ((p.2 : ℝ) / 2 - 1))
  have hbound : Integrable bound (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff.2
      ⟨half_pos p.1.2, half_pos p.2.2⟩).const_mul ‖f‖
  apply continuousAt_of_dominated (bound := bound)
  · exact .of_forall fun q ↦
      (((by fun_prop : Measurable fun x : ℝ ↦
        x ^ ((q.1 : ℝ) - 1) * (1 - x) ^ ((q.2 : ℝ) - 1))).mul
        f.continuous.measurable).aestronglyMeasurable
  · have hpa : ∀ᶠ q in 𝓝 p, (p.1 : ℝ) / 2 < (q.1 : ℝ) :=
      ha.continuousAt (lt_mem_nhds (half_lt_self p.1.2))
    have hpb : ∀ᶠ q in 𝓝 p, (p.2 : ℝ) / 2 < (q.2 : ℝ) :=
      hb.continuousAt (lt_mem_nhds (half_lt_self p.2.2))
    filter_upwards [hpa, hpb] with q hqa hqb
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxa := Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le
      (sub_le_sub_right hqa.le 1)
    have hxb := Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hx.2)
      (sub_le_self 1 hx.1.le) (sub_le_sub_right hqb.le 1)
    have hnonneg : 0 ≤ x ^ ((q.1 : ℝ) - 1) * (1 - x) ^ ((q.2 : ℝ) - 1) :=
      mul_nonneg (Real.rpow_nonneg hx.1.le _)
        (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
    calc
      _ = ‖f x‖ *
          (x ^ ((q.1 : ℝ) - 1) * (1 - x) ^ ((q.2 : ℝ) - 1)) := by
        rw [norm_mul, Real.norm_of_nonneg hnonneg, mul_comm]
      _ ≤ bound x := mul_le_mul (f.norm_coe_le_norm x)
        (mul_le_mul hxa hxb (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
          (Real.rpow_nonneg hx.1.le _)) hnonneg (norm_nonneg _)
  · exact hbound
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((((Real.continuous_const_rpow hx.1.ne').comp (ha.sub continuous_const)).mul
      ((Real.continuous_const_rpow (sub_pos.mpr hx.2).ne').comp
        (hb.sub continuous_const))).mul continuous_const).continuousAt

end TauCeti.Probability
