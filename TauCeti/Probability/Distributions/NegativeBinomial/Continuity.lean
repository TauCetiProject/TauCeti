/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Discrete
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Polynomial

/-!
# Weak continuity of negative-binomial laws

The native negative-binomial law depends jointly weakly continuously on its nonnegative
real shape and success probability in `(0, 1]`. This includes both Dirac boundaries:
shape zero and success probability one. The probability-zero boundary is excluded.

The multichoose expression for each mass extends to shape zero. Expressing this coefficient
as an ascending Pochhammer polynomial divided by a factorial gives continuity of the masses,
and hence of the laws on the countable discrete carrier. No limiting density is required.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 5.

The coefficient calculation uses Mathlib's
`Ring.factorial_nsmul_multichoose_eq_ascPochhammer`.
-/

public section

open MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Negative-binomial laws depend jointly weakly continuously on their nonnegative shape
and success probability in `(0, 1]`, including both Dirac boundaries. -/
theorem continuous_negativeBinomialMeasure :
    Continuous (Y := ProbabilityMeasure ℕ) (fun q : ℝ≥0 × Ioc (0 : ℝ) 1 ↦
      (⟨negativeBinomialMeasure q.1 q.2,
        isProbabilityMeasure_negativeBinomialMeasure q.1.2 q.2.2.1 q.2.2.2⟩ :
          ProbabilityMeasure ℕ)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_singleton.2
  intro k
  apply NNReal.isEmbedding_coe.continuous_iff.2
  have heq (q : ℝ≥0 × Ioc (0 : ℝ) 1) :
      (negativeBinomialMeasure q.1 q.2).real {k} =
        (ascPochhammer ℝ k).eval (q.1 : ℝ) / k.factorial *
          (q.2 : ℝ) ^ (q.1 : ℝ) * (1 - (q.2 : ℝ)) ^ k := by
    rw [negativeBinomialMeasure_real_singleton (r := (q.1 : ℝ)) (p := (q.2 : ℝ))
      q.1.2 q.2.2.1 q.2.2.2 k, negativeBinomialWeightReal_eq_coeff
        (r := (q.1 : ℝ)) (p := (q.2 : ℝ)) q.1.2 k]
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (q.1 : ℝ) k
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h, mul_div_cancel_left₀ _ (by positivity : (k.factorial : ℝ) ≠ 0),
      Real.rpow_eq_pow]
  simp only [Function.comp_def, ProbabilityMeasure.mk_apply,
    ENNReal.coe_toNNReal_eq_toReal, ← measureReal_def, heq]
  have hr : Continuous fun q : ℝ≥0 × Ioc (0 : ℝ) 1 ↦ (q.1 : ℝ) :=
    NNReal.continuous_coe.comp continuous_fst
  have hp : Continuous fun q : ℝ≥0 × Ioc (0 : ℝ) 1 ↦ (q.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  exact ((((Polynomial.continuous _).comp hr).div_const _).mul
    (hp.rpow hr fun q ↦ Or.inl q.2.2.1.ne')).mul
      ((continuous_const.sub hp).pow k)

/-- Continuous valid parameters give a weakly continuous family of native negative-binomial
laws. -/
@[fun_prop]
theorem _root_.Continuous.negativeBinomialMeasure {X : Type*} [TopologicalSpace X]
    {r p : X → ℝ} (hr : Continuous r) (hp : Continuous p)
    (hr0 : ∀ x, 0 ≤ r x) (hp0 : ∀ x, 0 < p x) (hp1 : ∀ x, p x ≤ 1) :
    Continuous (Y := ProbabilityMeasure ℕ) (fun x ↦
      (⟨negativeBinomialMeasure (r x) (p x),
        isProbabilityMeasure_negativeBinomialMeasure (hr0 x) (hp0 x) (hp1 x)⟩ :
          ProbabilityMeasure ℕ)) := by
  exact continuous_negativeBinomialMeasure.comp
    ((hr.subtype_mk hr0).prodMk (hp.subtype_mk fun x ↦ ⟨hp0 x, hp1 x⟩))

end TauCeti.Probability
