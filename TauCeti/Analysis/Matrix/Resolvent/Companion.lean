/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence

/-!
# Companion covariance resolvents

Rectangular Gram matrices formed from the same data have the same nonzero spectrum.
Their transforms differ by the exact dimension correction at zero. Expressing the
correction in the field of scalars gives a single identity for both orders of the two
dimensions. The companion of `XXᴴ/n` is `XᴴX/n`, with the same divisor.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory
open scoped Topology

namespace Matrix

variable {p n : Type*} [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]
  [Nonempty p] [Nonempty n]

/-- The difference in the masses at zero of the two Gram spectra gives a signed dimension
correction in their resolvent transforms. The two Gram matrices have a common real scale. -/
theorem card_mul_resolventTransform_spectralMeasure_smul_conjTranspose_mul_self
    (X : Matrix p n ℂ) (c : ℝ) (z : ℂ) :
    let A := c • (X * Xᴴ)
    let B := c • (Xᴴ * X)
    let hA : A.IsHermitian := (isHermitian_mul_conjTranspose_self X).smul (by simp [IsSelfAdjoint])
    let hB : B.IsHermitian := (isHermitian_conjTranspose_mul_self X).smul (by simp [IsSelfAdjoint])
    (Fintype.card n : ℂ) * resolventTransform (B.spectralMeasure hB : Measure ℝ) z =
      Fintype.card p * resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
        ((Fintype.card n : ℂ) - Fintype.card p) * z⁻¹ := by
  dsimp only
  have hp : (Fintype.card p : ℂ) ≠ 0 := by simp
  have hn : (Fintype.card n : ℂ) ≠ 0 := by simp
  have hA : (c • (X * Xᴴ)).IsHermitian :=
    (isHermitian_mul_conjTranspose_self X).smul (by simp [IsSelfAdjoint])
  have hB : (c • (Xᴴ * X)).IsHermitian :=
    (isHermitian_conjTranspose_mul_self X).smul (by simp [IsSelfAdjoint])
  rcases le_total (Fintype.card p) (Fintype.card n) with h | h
  · have hchar := charpoly_mul_comm_of_le Xᴴ (c • X) h
    rw [Matrix.mul_smul, Matrix.smul_mul] at hchar
    rw [resolventTransform_spectralMeasure_of_charpoly_eq_X_pow_mul hB hA hchar,
      Nat.cast_sub h]
    field_simp
  · have hchar := charpoly_mul_comm_of_le (c • X) Xᴴ h
    rw [Matrix.mul_smul, Matrix.smul_mul] at hchar
    rw [resolventTransform_spectralMeasure_of_charpoly_eq_X_pow_mul hA hB hchar,
      Nat.cast_sub h]
    field_simp
    ring

/-- The companion transform of a sample covariance matrix is the original transform times
the aspect ratio, plus the signed correction at zero. The companion uses the original column
count as its divisor. -/
theorem resolventTransform_spectralMeasure_sampleCovariance_companion
    (X : Matrix p n ℂ) (z : ℂ) :
    let y := (Fintype.card p : ℂ) / Fintype.card n
    let B := (1 / (Fintype.card n : ℝ)) • (Xᴴ * X)
    let hB : B.IsHermitian :=
      (isHermitian_conjTranspose_mul_self X).smul (by simp [IsSelfAdjoint])
    resolventTransform (B.spectralMeasure hB : Measure ℝ) z =
      y * resolventTransform
        ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z -
      (1 - y) * z⁻¹ := by
  dsimp only
  have hn : (Fintype.card n : ℂ) ≠ 0 := by simp
  apply mul_left_cancel₀ hn
  have h := card_mul_resolventTransform_spectralMeasure_smul_conjTranspose_mul_self X
    (1 / (Fintype.card n : ℝ)) z
  simp only [sampleCovariance_def]
  rw [h]
  field_simp

end Matrix

namespace TauCeti

/-- A weak limit of sample covariance spectra and a limit of the aspect ratios determine
the limit of the companion transforms at every nonreal parameter. The companion at each
index uses the same divisor as the sample covariance itself. -/
theorem tendsto_resolventTransform_sampleCovariance_companion
    {ι : Type*} {l : Filter ι} {p n : ι → ℕ} [∀ i, NeZero (p i)] [∀ i, NeZero (n i)]
    (X : (i : ι) → Matrix (Fin (p i)) (Fin (n i)) ℂ)
    {y : ℝ} (hy : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 y))
    {μ : ProbabilityMeasure ℝ}
    (hμ : Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ))
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i ↦
      let B := (1 / (n i : ℝ)) • ((X i)ᴴ * X i)
      let hB : B.IsHermitian :=
        (isHermitian_conjTranspose_mul_self _).smul (by simp [IsSelfAdjoint])
      resolventTransform (B.spectralMeasure hB : Measure ℝ) z) l
      (𝓝 ((y : ℂ) * resolventTransform (μ : Measure ℝ) z - (1 - (y : ℂ)) * z⁻¹)) := by
  have hcomp (i : ι) :=
    resolventTransform_spectralMeasure_sampleCovariance_companion (X i) z
  simp only [Fintype.card_fin] at hcomp
  have hθ := (Complex.continuous_ofReal.tendsto y).comp hy
  have hm := ProbabilityMeasure.tendsto_resolventTransform_of_tendsto hμ hz
  simp_rw [hcomp]
  simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast] using
    (hθ.mul hm).sub ((tendsto_const_nhds (x := (1 : ℂ))).sub hθ |>.mul_const z⁻¹)

end TauCeti
