/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Concentration.Poincare.Herbst
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Analysis.Matrix.HoffmanWielandt
import TauCeti.Probability.Concentration.SubgaussianTail

/-!
# Concentration of Wigner linear spectral statistics

On the unscaled Hilbert space of upper-triangular Wigner coordinates, integrating a
`K`-Lipschitz test against the empirical spectral measure is `√2 K / n`-Lipschitz.
The factor `√2` accounts for the two matrix entries contributed by each strictly upper
coordinate. A joint coordinate law with logarithmic Sobolev constant `C` therefore gives
sub-Gaussian fluctuations with variance proxy `2 C K² / n²`.

The argument follows Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*,
§2.3, especially Lemma 2.3.1 and Theorem 2.3.5. The logarithmic Sobolev hypothesis is on the
joint law, so the concentration transfer also applies to dependent coordinates.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace TauCeti

variable {n : ℕ} {K C : ℝ≥0} {f : ℝ → ℝ}

/-- A `K`-Lipschitz test integrated against the empirical spectral measure of a normalized
Wigner matrix is `√2 K / n`-Lipschitz in its unscaled Hilbert coordinates. -/
theorem lipschitzWith_integral_spectralMeasure_wignerMatrixOfCoordinates [NeZero n] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} (hg : LipschitzWith K g) :
    LipschitzWith (NNReal.sqrt 2 * K / n)
      (fun x : PiLp 2 (@WignerCoordinateType n) ↦
        ∫ z, g z ∂((wignerMatrixOfCoordinates x.ofLp).spectralMeasure
          (wignerMatrixOfCoordinates_isHermitian x.ofLp) : Measure ℝ)) := by
  refine lipschitzWith_iff_norm_sub_le.mpr fun x y ↦ ?_
  by_cases hE : CompleteSpace E
  swap
  · simp only [integral_of_not_completeSpace hE, sub_self, norm_zero]
    positivity
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn
  have hmatrix := lipschitzWith_iff_norm_sub_le.mp lipschitzWith_wignerMatrixOfCoordinates x y
  push_cast at hmatrix
  calc
    _ ≤ K * ‖wignerMatrixOfCoordinates x.ofLp - wignerMatrixOfCoordinates y.ofLp‖ /
        √(n : ℝ) := by
      simpa only [Fintype.card_fin] using
        Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le
          (wignerMatrixOfCoordinates_isHermitian x.ofLp)
          (wignerMatrixOfCoordinates_isHermitian y.ofLp) hg
    _ ≤ K * (√2 / √(n : ℝ) * ‖x - y‖) / √(n : ℝ) := by gcongr
    _ = _ := by
      push_cast
      field_simp [hs.ne', hn.ne']
      rw [Real.sq_sqrt hn.le]
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (PiLp 2 (@WignerCoordinateType n))}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Under a logarithmic Sobolev inequality for the joint law of the unscaled Wigner
coordinates, a centered Lipschitz spectral statistic is sub-Gaussian with variance proxy
`2 C K² / n²`. -/
theorem hasSubgaussianMGF_integral_spectralMeasure_wignerMatrix [NeZero n]
    (hμ : μ.LogSobolevInequality C)
    (hcoords : HasLaw (fun ω ↦ WithLp.toLp 2 (wignerCoordinates ξ η n ω)) μ P)
    (hf : LipschitzWith K f) :
    HasSubgaussianMGF
      (fun ω ↦
        (∫ z, f z ∂((wignerMatrix ξ η n ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω n) : Measure ℝ)) -
        ∫ ω', ∫ z, f z ∂((wignerMatrix ξ η n ω').spectralMeasure
          (wignerMatrix_isHermitian ξ η ω' n) : Measure ℝ) ∂P)
      (2 * C * K ^ 2 / (n : ℝ≥0) ^ 2) P := by
  let := hcoords.isProbabilityMeasure_iff.mp (inferInstance : IsProbabilityMeasure P)
  have hL := lipschitzWith_integral_spectralMeasure_wignerMatrixOfCoordinates (n := n) hf
  have hsub := hμ.hasSubgaussianMGF_of_lipschitzWith hL
  have hproxy : (C : ℝ).toNNReal * (NNReal.sqrt 2 * K / n) ^ 2 =
      2 * C * K ^ 2 / (n : ℝ≥0) ^ 2 := by
    rw [Real.toNNReal_coe, div_pow, mul_pow, NNReal.sq_sqrt, ← mul_div_assoc]
    ring
  rw [hproxy] at hsub
  have hmean := hcoords.integral_comp hL.continuous.aestronglyMeasurable
  rw [← hcoords.map_eq] at hmean
  have hsub' := HasSubgaussianMGF.of_map hcoords.aemeasurable (hcoords.map_eq.symm ▸ hsub)
  simpa only [← hmean, Function.comp_def, WithLp.ofLp_toLp,
    ← wignerMatrix_eq_wignerMatrixOfCoordinates] using hsub'

/-- A Lipschitz Wigner spectral statistic has a two-sided Gaussian tail at speed `n²`
under the logarithmic Sobolev inequality for the joint coordinate law. -/
theorem measureReal_abs_integral_spectralMeasure_wignerMatrix_sub_ge_le [NeZero n]
    (hμ : μ.LogSobolevInequality C)
    (hcoords : HasLaw (fun ω ↦ WithLp.toLp 2 (wignerCoordinates ξ η n ω)) μ P)
    (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω |
      t ≤ |(∫ z, f z ∂((wignerMatrix ξ η n ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω n) : Measure ℝ)) -
        ∫ ω', ∫ z, f z ∂((wignerMatrix ξ η n ω').spectralMeasure
          (wignerMatrix_isHermitian ξ η ω' n) : Measure ℝ) ∂P|} ≤
      2 * Real.exp (-((n : ℝ) ^ 2 * t ^ 2) / (4 * C * K ^ 2)) := by
  have hsub := hasSubgaussianMGF_integral_spectralMeasure_wignerMatrix hμ hcoords hf
  convert hsub.measureReal_abs_ge_le ht using 3
  push_cast
  simp only [← mul_div_assoc, div_div_eq_mul_div]
  ring

end TauCeti
