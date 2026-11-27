/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.LocationScale
public import TauCeti.Probability.FreeProbability.FreeConvolution.Additive.Power
public import TauCeti.Probability.FreeProbability.Semicircular.Law
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Free additive convolution of Wigner semicircle laws

The location-scale Wigner semicircle laws `TauCeti.Probability.semicircleReal m v` on `ℝ` form a
two-parameter semigroup under `MeasureTheory.Measure.freeConv`: both centres and variances
add, including in the degenerate zero-variance Dirac cases. Consequently, taking the `n`-fold free
additive convolution power scales both the centre and the variance by `n`, including `n = 0`.

## Main results

* `TauCeti.Probability.semicircleReal_freeConv_semicircleReal`:
  `(semicircleReal m₁ v₁).freeConv (semicircleReal m₂ v₂) = semicircleReal (m₁ + m₂) (v₁ + v₂)`.
* `TauCeti.Probability.semicircleReal_freeConvPow`:
  `(semicircleReal m v).freeConvPow n = semicircleReal (n * m) (n • v)`.

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
@[simp] theorem semicircleReal_freeConv_semicircleReal (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) :
    (semicircleReal m₁ v₁).freeConv (semicircleReal m₂ v₂) =
      semicircleReal (m₁ + m₂) (v₁ + v₂) := by
  have hcentred : (semicircleReal 0 v₁).freeConv (semicircleReal 0 v₂) =
      semicircleReal 0 (v₁ + v₂) := by
    obtain ⟨A, _, _, _, φ, g, _, hfree, hg1, hg2, _, _, hlaw1, hlaw2, hadd⟩ :=
      Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv
        (isCompact_support_semicircleReal 0 v₁) (isCompact_support_semicircleReal 0 v₂)
    have hsum : IsSemicircular φ.toLinearMap (g true + g false) (((v₁ + v₂ : ℝ≥0) : ℝ) : ℂ) := by
      simpa [NNReal.coe_add] using
        hfree.isSemicircular_add Bool.false_ne_true.symm
          ((φ.law_eq_semicircleReal_iff hg1 v₁).mp hlaw1)
          ((φ.law_eq_semicircleReal_iff hg2 v₂).mp hlaw2)
    exact hadd.symm.trans <| (φ.law_eq_semicircleReal_iff (hg1.add hg2) _).mpr hsum
  have hshift (m : ℝ) (v : ℝ≥0) :
      semicircleReal m v = (semicircleReal 0 v).map fun x => m + 1 * x := by
    simpa using (map_affine_semicircleReal 0 m 1 v).symm
  rw [hshift m₁ v₁, hshift m₂ v₂, Measure.freeConv_map_affine
    (isCompact_support_semicircleReal 0 v₁) (isCompact_support_semicircleReal 0 v₂) m₁ m₂ 1,
    hcentred, ← hshift (m₁ + m₂) (v₁ + v₂)]

/-- **Free convolution powers of Wigner semicircle laws.** -/
@[simp] theorem semicircleReal_freeConvPow (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (semicircleReal m v).freeConvPow n = semicircleReal (n * m) (n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Measure.freeConvPow_succ, ih, semicircleReal_freeConv_semicircleReal, succ_nsmul]
      congr 1; push_cast; ring

end TauCeti.Probability
