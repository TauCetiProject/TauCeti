/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Exponential rays of the completely monotone cone

An exponential `t ↦ exp (-p t)` with nonnegative rate `p` cannot be decomposed as a sum of two
completely monotone functions except by splitting its positive coefficient. The Bernstein
representation turns such a decomposition into one of a Dirac measure; both summands must then
be concentrated at the same rate.

This is the extreme-ray property of the exponential building blocks in Bernstein's theorem.
The functions are compared on `[0, ∞)`, the domain on which the representation is unique.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NNReal

open TauCeti

/-- The exponential of rate `p` spans an extreme ray of the cone of completely monotone
functions on `[0, ∞)`: every positive decomposition splits only its coefficient. -/
theorem exp_neg_mul_extreme_ray {f g : ℝ → ℝ} (p : ℝ≥0)
    (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hg : IsContinuousCompletelyMonotoneOnIoi g)
    (hfg : ∀ t : ℝ, 0 ≤ t → f t + g t = Real.exp (-(t * (p : ℝ)))) :
    ∃ a b : ℝ≥0, (a : ℝ) + b = 1 ∧
      (∀ t : ℝ, 0 ≤ t → f t = (a : ℝ) * Real.exp (-(t * (p : ℝ)))) ∧
      (∀ t : ℝ, 0 ≤ t → g t = (b : ℝ) * Real.exp (-(t * (p : ℝ)))) := by
  let μ := bernsteinMeasure f
  let ν := bernsteinMeasure g
  have hμ := representsLaplace_bernsteinMeasure hf
  have hν := representsLaplace_bernsteinMeasure hg
  have hsum : μ + ν = Measure.dirac p :=
    (hμ.add hν).unique ((representsLaplace_dirac p).congr (fun t ht => hfg t ht))
  obtain ⟨hμdirac, hνdirac⟩ := eq_smul_dirac_and_eq_smul_dirac_of_add_eq_dirac hsum
  let a : ℝ≥0 := (μ Set.univ).toNNReal
  let b : ℝ≥0 := (ν Set.univ).toNNReal
  have ha : (a : ℝ≥0∞) = μ Set.univ := ENNReal.coe_toNNReal (measure_ne_top μ Set.univ)
  have hb : (b : ℝ≥0∞) = ν Set.univ := ENNReal.coe_toNNReal (measure_ne_top ν Set.univ)
  have hfa : RepresentsLaplace μ (fun t => (a : ℝ) * Real.exp (-(t * (p : ℝ)))) := by
    rw [hμdirac, ← ha]
    exact (representsLaplace_dirac p).smul a
  have hgb : RepresentsLaplace ν (fun t => (b : ℝ) * Real.exp (-(t * (p : ℝ)))) := by
    rw [hνdirac, ← hb]
    exact (representsLaplace_dirac p).smul b
  refine ⟨a, b, ?_, ?_, ?_⟩
  · have h0 := hfg 0 le_rfl
    have hfa0 : f 0 = (a : ℝ) := by
      rw [← bernsteinMeasure_real_univ hf, measureReal_def, ← ha, ENNReal.coe_toReal]
    have hgb0 : g 0 = (b : ℝ) := by
      rw [← bernsteinMeasure_real_univ hg, measureReal_def, ← hb, ENNReal.coe_toReal]
    simp only [zero_mul, neg_zero, Real.exp_zero] at h0
    linarith
  · intro t ht
    exact (hμ.eq_laplaceTransform ht).trans (hfa.eq_laplaceTransform ht).symm
  · intro t ht
    exact (hν.eq_laplaceTransform ht).trans (hgb.eq_laplaceTransform ht).symm

end NNReal
