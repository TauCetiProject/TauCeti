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
    let τ : Fin 2 → Measure ℝ := ![semicircleReal 0 v₁, semicircleReal 0 v₂]
    have : ∀ i, IsProbabilityMeasure (τ i) := Fin.forall_fin_two.2
      ⟨isProbabilityMeasure_semicircleReal 0 v₁, isProbabilityMeasure_semicircleReal 0 v₂⟩
    have : ∀ i, CompactSpace (τ i).support := Fin.forall_fin_two.2
      ⟨isCompact_iff_compactSpace.mp (isCompact_support_semicircleReal 0 v₁),
       isCompact_iff_compactSpace.mp (isCompact_support_semicircleReal 0 v₂)⟩
    let φ := FreeLawRealization.state τ
    let x := FreeLawRealization.generator τ 0
    let y := FreeLawRealization.generator τ 1
    have hx := FreeLawRealization.isSelfAdjoint_generator τ 0
    have hy := FreeLawRealization.isSelfAdjoint_generator τ 1
    have h0 : φ.law x = semicircleReal 0 v₁ := by
      rw [FreeLawRealization.law_generator τ 0]; simp [τ]
    have h1 : φ.law y = semicircleReal 0 v₂ := by
      rw [FreeLawRealization.law_generator τ 1]; simp [τ]
    have hsum : IsSemicircular φ.toLinearMap (x + y) (((v₁ + v₂ : ℝ≥0) : ℝ) : ℂ) := by
      simpa [NNReal.coe_add] using
        (FreeLawRealization.isFreelyIndependentElements_generator τ).isSemicircular_add
          (by decide : (0 : Fin 2) ≠ 1)
          ((φ.law_eq_semicircleReal_iff hx v₁).mp h0)
          ((φ.law_eq_semicircleReal_iff hy v₂).mp h1)
    have hadd : φ.law (x + y) = (semicircleReal 0 v₁).freeConv (semicircleReal 0 v₂) := by
      rw [FreeLawRealization.law_add_generator τ (by decide : (0 : Fin 2) ≠ 1)]; simp [τ]
    exact hadd.symm.trans <| (φ.law_eq_semicircleReal_iff (hx.add hy) _).mpr hsum
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
