/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Power
import TauCeti.Probability.Independence.ConvolutionPower

/-!
# Sums and sample means of real Gaussian laws

Iterating Mathlib's `ProbabilityTheory.gaussianReal_conv_gaussianReal`, the `n`-fold convolution
power of `gaussianReal m v` is `gaussianReal (n * m) (n * v)`: this is the law of a sum of `n`
independent random variables with common law `gaussianReal m v`. Rescaling, their sample mean has
law `gaussianReal m (v / n)`.

## Main results

* `TauCeti.Probability.gaussianReal_convolutionPower`: the convolution powers of a real Gaussian
  law.
* `ProbabilityTheory.iIndepFun.hasLaw_finset_sum_div_card_gaussianReal`: the law of the sample
  mean of independent random variables with a common real Gaussian law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- The `n`-fold convolution power of `gaussianReal m v` is `gaussianReal (n * m) (n * v)`. -/
@[simp]
theorem gaussianReal_convolutionPower (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (gaussianReal m v).convolutionPower n = gaussianReal (n * m) (n * v) := by
  induction n with
  | zero => simp [gaussianReal_zero_var]
  | succ n ih =>
    rw [Measure.convolutionPower_succ, ih, gaussianReal_conv_gaussianReal]
    congr 1 <;> push_cast <;> ring

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

/-- The mean `(∑ i ∈ s, X i) / #s` of independent random variables with common law
`gaussianReal m v`, over a nonempty finite set `s`, has law `gaussianReal m (v / #s)`. Only the
variables indexed by `s` need be independent and Gaussian. -/
theorem hasLaw_finset_sum_div_card_gaussianReal {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι} (hind : iIndepFun (s.restrict X) P) {m : ℝ}
    {v : ℝ≥0} (hX : ∀ i ∈ s, HasLaw (X i) (gaussianReal m v) P) (hs : s.Nonempty) :
    HasLaw (fun ω => (∑ i ∈ s, X i ω) / s.card) (gaussianReal m ((s.card : ℝ≥0)⁻¹ * v)) P := by
  have hsum := hind.hasLaw_sum_convolutionPower fun i => hX i i.property
  rw [Fintype.card_coe, gaussianReal_convolutionPower] at hsum
  have hmean := gaussianReal_div_const hsum s.card
  simp only [Finset.sum_apply, Finset.restrict_def] at hmean
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
  convert hmean using 2 with ω
  · rw [← Finset.sum_coe_sort s]
  · field_simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]
    field_simp

end ProbabilityTheory.iIndepFun
