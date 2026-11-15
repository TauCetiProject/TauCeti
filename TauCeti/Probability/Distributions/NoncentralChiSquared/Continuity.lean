/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Distributions.NoncentralChiSquared.CharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Weak continuity of noncentral chi-squared laws

Noncentral chi-squared laws depend jointly weakly continuously on their nonnegative degree
and noncentrality. This includes the degree-zero laws with an atom at zero and the Dirac law
when both parameters vanish. The topology is that of `ProbabilityMeasure ℝ`.

The characteristic-function formula remains valid at these boundaries. Its principal complex
power has a fixed base of real part one, so continuity in the exponent and in the exponential
factor gives weak continuity through Mathlib's Lévy convergence theorem,
`ProbabilityMeasure.tendsto_of_tendsto_charFun`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Noncentral chi-squared laws depend jointly weakly continuously on their nonnegative degree
and noncentrality, including the degree-zero and double-zero boundaries. -/
theorem continuous_noncentralChiSquaredMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : ℝ≥0 × ℝ≥0 ↦
      (⟨noncentralChiSquaredMeasure p.1 p.2,
        isProbabilityMeasure_noncentralChiSquaredMeasure p.1.coe_nonneg p.2⟩ :
          ProbabilityMeasure ℝ)) := by
  apply continuous_iff_seqContinuous.2
  intro p a hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n ↦ ⟨noncentralChiSquaredMeasure (p n).1 (p n).2,
      isProbabilityMeasure_noncentralChiSquaredMeasure (p n).1.coe_nonneg (p n).2⟩)
  intro t
  simp only [ProbabilityMeasure.coe_mk,
    charFun_noncentralChiSquaredMeasure (p _).1.coe_nonneg,
    charFun_noncentralChiSquaredMeasure a.1.coe_nonneg]
  have hk : Tendsto (fun n ↦ ((p n).1 : ℂ)) atTop (𝓝 (a.1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((NNReal.continuous_coe.comp continuous_fst).tendsto a |>.comp hp)
  have hl : Tendsto (fun n ↦ ((p n).2 : ℂ)) atTop (𝓝 (a.2 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((NNReal.continuous_coe.comp continuous_snd).tendsto a |>.comp hp)
  have hbase : 1 - 2 * Complex.I * (t : ℂ) ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simp)
  exact ((hk.neg.div_const 2).const_cpow (Or.inl hbase)).mul
    (((hl.mul_const Complex.I).mul_const (t : ℂ)).div_const _).cexp

/-- Continuous valid degree and noncentrality parameters give a weakly continuous family of
noncentral chi-squared laws on an arbitrary topological parameter space. -/
@[fun_prop]
theorem _root_.Continuous.noncentralChiSquaredMeasure {X : Type*} [TopologicalSpace X]
    {k : X → ℝ} {l : X → ℝ≥0} (hk : Continuous k) (hl : Continuous l)
    (hk0 : ∀ x, 0 ≤ k x) :
    Continuous (Y := ProbabilityMeasure ℝ) (fun x ↦
      (⟨noncentralChiSquaredMeasure (k x) (l x),
        isProbabilityMeasure_noncentralChiSquaredMeasure (hk0 x) (l x)⟩ :
          ProbabilityMeasure ℝ)) := by
  exact continuous_noncentralChiSquaredMeasure.comp ((hk.subtype_mk hk0).prodMk hl)

end TauCeti.Probability
