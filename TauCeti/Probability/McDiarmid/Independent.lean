/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.McDiarmid.Basic
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Bounded differences for independent random variables

If changing only coordinate `i` changes a measurable real function `f` by at most `c i`, then
`f(X) - E f(X)` is sub-Gaussian with variance proxy `∑ i, (c i)² / 4` for independent `X i`.
The variables may take values in different measurable spaces and have different laws; almost
everywhere measurability of each coordinate suffices.

The one-sided and two-sided McDiarmid inequalities have exponent `-2 t² / ∑ i, (c i)²`.
When this denominator vanishes, the statistic equals its mean almost everywhere, including
for an empty coordinate family. No moment assumptions on the coordinates are needed.

## References

* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 141 (1989),
  148–188.
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Theorem 6.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ∀ i, Ω → β i}

/-- **McDiarmid's MGF bound for independent coordinates.** A measurable function with coordinate
oscillations bounded by `c i` is sub-Gaussian about its mean, with variance proxy
`∑ i, (c i)² / 4`. The coordinates need only be almost everywhere measurable. -/
theorem hasSubgaussianMGF_of_bounded_differences (h : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (f : (∀ i, β i) → ℝ) (hf : Measurable f)
    (c : ι → ℝ≥0)
    (hbd : ∀ (i : ι) (x x' : ∀ i, β i),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i) :
    HasSubgaussianMGF
      (fun ω => f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P)
      (∑ i, c i ^ 2 / 4) P := by
  let ν i := P.map (X i)
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (Measure.isProbabilityMeasure_map_iff (hX i)).mpr inferInstance
  have hlaw := h.hasLaw_pi (fun i => hasLaw_map (hX i))
  have hsub := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences
    ν f hf (fun i => (c i : ℝ)) hbd
  simp only [Real.toNNReal_coe] at hsub
  have hmean := hlaw.integral_comp hf.aestronglyMeasurable
  rw [← hmean] at hsub
  rw [← hlaw.map_eq] at hsub
  simpa only [Function.comp_def] using HasSubgaussianMGF.of_map hlaw.aemeasurable hsub

/-- The real exponent obtained from McDiarmid's variance proxy. -/
private theorem exponent_variance_proxy (c : ι → ℝ≥0) (t : ℝ) :
    -t ^ 2 / (2 * ((∑ i, c i ^ 2 / 4 : ℝ≥0) : ℝ)) =
      -2 * t ^ 2 / (∑ i, (c i : ℝ) ^ 2) := by
  simp only [NNReal.coe_sum, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat,
    ← Finset.sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- **One-sided McDiarmid inequality.** For independent coordinates and bounded differences
`c i`, the probability of an upward deviation of at least `t ≥ 0` is at most
`exp (-2 t² / ∑ i, (c i)²)`. -/
theorem measureReal_sub_ge_le_of_bounded_differences (h : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (f : (∀ i, β i) → ℝ) (hf : Measurable f)
    (c : ι → ℝ≥0)
    (hbd : ∀ (i : ι) (x x' : ∀ i, β i),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P} ≤
      Real.exp (-2 * t ^ 2 / (∑ i, (c i : ℝ) ^ 2)) := by
  have htail := (h.hasSubgaussianMGF_of_bounded_differences hX f hf c hbd).measure_ge_le ht
  rwa [exponent_variance_proxy] at htail

/-- **Two-sided McDiarmid inequality.** For independent coordinates and bounded differences
`c i`, the probability of an absolute deviation of at least `t ≥ 0` is at most
`2 exp (-2 t² / ∑ i, (c i)²)`. When every bound is zero, use
`TauCeti.Probability.eq_integral_of_bounded_differences_of_sum_sq_eq_zero`
for the exact conclusion. -/
theorem measureReal_abs_sub_ge_le_of_bounded_differences (h : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (f : (∀ i, β i) → ℝ) (hf : Measurable f)
    (c : ι → ℝ≥0)
    (hbd : ∀ (i : ι) (x x' : ∀ i, β i),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P|} ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i, (c i : ℝ) ^ 2)) := by
  have hsub := h.hasSubgaussianMGF_of_bounded_differences hX f hf c hbd
  have hu := hsub.measure_ge_le ht
  have hl := hsub.neg.measure_ge_le ht
  simp only [Pi.neg_apply] at hl
  rw [exponent_variance_proxy] at hu hl
  exact (TauCeti.measureReal_le_abs_le_add).trans (by linarith)

end ProbabilityTheory.iIndepFun
