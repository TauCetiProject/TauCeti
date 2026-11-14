/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.LocationScale
public import TauCeti.Probability.FreeProbability.FreeConvolution.Additive.Power
public import TauCeti.Probability.FreeProbability.Semicircular.Law

/-!
# Free additive convolution of Wigner semicircle laws

The location-scale Wigner semicircle laws `TauCeti.Probability.semicircleReal m v` on `ℝ` form a
two-parameter semigroup under Voiculescu's free additive convolution
`MeasureTheory.Measure.freeConv` (`⊞`), playing the role of Gaussian laws under classical
convolution: both centres and variances add, including in the degenerate zero-variance Dirac cases.

In the centred case `m₁ = m₂ = 0`, realizing both semicircle laws by freely independent selfadjoint
elements via `MeasureTheory.Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv` reduces
the convolution identity to `TauCeti.IsFreelyIndependentElements.isSemicircular_add`; the general
location-scale case follows by affine equivariance (`MeasureTheory.Measure.freeConv_map_affine`),
and induction yields the `n`-fold free convolution power `semicircleReal (n * m) (n • v)`.

## Main results

* `TauCeti.Probability.semicircleReal_freeConv_semicircleReal`:
  `(semicircleReal m₁ v₁).freeConv (semicircleReal m₂ v₂) = semicircleReal (m₁ + m₂) (v₁ + v₂)`.
* `TauCeti.Probability.semicircleReal_freeConvolutionPower`:
  `(semicircleReal m v).freeConvolutionPower n = semicircleReal (n * m) (n • v)`.

## References

* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 2, 11, and 12.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder NNReal

namespace TauCeti.Probability

/-- **Free additive convolution of Wigner semicircle laws.** Both centres and variances add, for all
`m₁, m₂ : ℝ` and `v₁, v₂ : ℝ≥0` (including the degenerate zero-variance Dirac cases). -/
theorem semicircleReal_freeConv_semicircleReal (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) :
    (semicircleReal m₁ v₁).freeConv (semicircleReal m₂ v₂) =
      semicircleReal (m₁ + m₂) (v₁ + v₂) := by
  have hcentred : (semicircleReal 0 v₁).freeConv (semicircleReal 0 v₂) =
      semicircleReal 0 (v₁ + v₂) := by
    obtain ⟨A, _, _, _, φ, g, -, hg_free, hg1_sa, hg2_sa, -, -, hg1_law, hg2_law, hadd_law⟩ :=
      Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv
        (isCompact_support_semicircleReal 0 v₁) (isCompact_support_semicircleReal 0 v₂)
    have hg1 : IsSemicircular φ.toLinearMap (g true) ((v₁ : ℝ) : ℂ) :=
      (φ.law_eq_semicircleReal_iff hg1_sa v₁).mp hg1_law
    have hg2 : IsSemicircular φ.toLinearMap (g false) ((v₂ : ℝ) : ℂ) :=
      (φ.law_eq_semicircleReal_iff hg2_sa v₂).mp hg2_law
    have hsum : IsSemicircular φ.toLinearMap (g true + g false) (((v₁ + v₂ : ℝ≥0) : ℝ) : ℂ) := by
      simpa [NNReal.coe_add] using hg_free.isSemicircular_add Bool.false_ne_true.symm hg1 hg2
    rw [← hadd_law]
    exact (φ.law_eq_semicircleReal_iff (hg1_sa.add hg2_sa) (v₁ + v₂)).mpr hsum
  have hshift (m : ℝ) (v : ℝ≥0) :
      semicircleReal m v = (semicircleReal 0 v).map fun x => m + 1 * x := by
    simpa using (map_affine_semicircleReal 0 m 1 v).symm
  rw [hshift m₁ v₁, hshift m₂ v₂,
    Measure.freeConv_map_affine (isCompact_support_semicircleReal 0 v₁)
      (isCompact_support_semicircleReal 0 v₂) m₁ m₂ 1,
    hcentred, ← hshift (m₁ + m₂) (v₁ + v₂)]

/-- **Free convolution powers of Wigner semicircle laws.** -/
theorem semicircleReal_freeConvolutionPower (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (semicircleReal m v).freeConvolutionPower n = semicircleReal (n * m) (n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Measure.freeConvolutionPower_succ, ih, semicircleReal_freeConv_semicircleReal, succ_nsmul]
      congr 1
      push_cast
      ring

end TauCeti.Probability
