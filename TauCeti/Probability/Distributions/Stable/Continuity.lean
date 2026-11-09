/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import TauCeti.Probability.Distributions.Affine
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak continuity of scalar stable laws

Nolan's `S₀` stable laws depend jointly weakly continuously on their shape, skewness,
nonnegative scale, and location on the valid parameter domain. This includes shape one,
the Gaussian endpoint at shape two, both full-skewness boundaries, and the zero-scale
Dirac laws. The topology is that of `ProbabilityMeasure ℝ`.

The shape-one continuity of `stableCharacteristicExponent` supplies pointwise convergence
of the standardized characteristic functions. Mathlib's Lévy convergence theorem gives
weak continuity of the standardized laws. Joint continuity of pushforward then transports
this to the full family, including collapsing scales.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1, the `S₀` parameterization.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Scalar stable laws in the `S₀` parameterization depend jointly weakly continuously on
all valid parameters, including shape one, shape two, and zero scale. -/
theorem continuous_stableMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p :
        (Ioc (0 : ℝ) 2 × Icc (-1 : ℝ) 1) × ℝ≥0 × ℝ ↦
      (⟨stableMeasure p.1.1 p.1.2 p.2.1 p.2.2,
        isProbabilityMeasure_stableMeasure p.1.1.2 (abs_le.mpr p.1.2.2) _ _⟩ :
        ProbabilityMeasure ℝ)) := by
  let μ (p : Ioc (0 : ℝ) 2 × Icc (-1 : ℝ) 1) : ProbabilityMeasure ℝ :=
    ⟨stableMeasure p.1 p.2 1 0,
      isProbabilityMeasure_stableMeasure p.1.2 (abs_le.mpr p.2.2) 1 0⟩
  have hμ (p) : (μ p : Measure ℝ) = stableMeasure p.1 p.2 1 0 := (rfl)
  have hstd : Continuous μ := by
    apply continuous_iff_seqContinuous.mpr
    intro p a hp
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun (μ := fun n ↦ μ (p n))
    intro t
    have hc := (Complex.continuous_exp.comp
      ((continuous_stableCharacteristicExponent_params t).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).tendsto a
    simpa only [hμ, charFun_stableMeasure (p _).1.2 (abs_le.mpr (p _).2.2),
      charFun_stableMeasure a.1.2 (abs_le.mpr a.2.2), NNReal.coe_one, one_mul, zero_mul,
      Complex.ofReal_zero, zero_add, Function.comp_def] using hc.comp hp
  have hm := ProbabilityMeasure.continuous_map_of_continuous_uncurry
    (f := fun q : ℝ≥0 × ℝ ↦ fun x : ℝ ↦ q.2 + q.1 * x) (by fun_prop)
  have h := hm.comp (continuous_snd.prodMk (hstd.comp continuous_fst))
  apply h.congr
  intro p
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map, hμ,
    ProbabilityMeasure.coe_mk]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_affine, charFun_stableMeasure p.1.1.2 (abs_le.mpr p.1.2.2),
    charFun_stableMeasure p.1.1.2 (abs_le.mpr p.1.2.2)]
  simp only [NNReal.coe_one, one_mul, zero_mul, Complex.ofReal_zero, zero_add,
    Complex.exp_add, Complex.ofReal_mul]

/-- Continuous valid stable parameters on any topological space give a weakly continuous
family of probability measures. -/
@[fun_prop]
theorem _root_.Continuous.stableMeasure {T : Type*} [TopologicalSpace T]
    {α β : T → ℝ} {s : T → ℝ≥0} {m : T → ℝ}
    (hα : Continuous α) (hβ : Continuous β) (hs : Continuous s) (hm : Continuous m)
    (hα' : ∀ t, α t ∈ Ioc 0 2) (hβ' : ∀ t, |β t| ≤ 1) :
    Continuous (Y := ProbabilityMeasure ℝ) (fun t ↦
      (⟨stableMeasure (α t) (β t) (s t) (m t),
        isProbabilityMeasure_stableMeasure (hα' t) (hβ' t) _ _⟩ : ProbabilityMeasure ℝ)) := by
  exact continuous_stableMeasure.comp
    (((hα.subtype_mk hα').prodMk (hβ.subtype_mk fun t ↦ abs_le.mp (hβ' t))).prodMk
      (hs.prodMk hm))

end TauCeti.Probability
