/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HoffmanWielandt
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Wasserstein bounds for empirical spectral measures

Pair the decreasingly sorted eigenvalues of two Hermitian matrices, with multiplicity, to
couple their empirical spectral measures. The quadratic cost of this coupling is the average
squared displacement of the sorted eigenvalues. The Hoffman–Wielandt inequality therefore gives

`W₂(L_A, L_B) ≤ ‖A - B‖_F / √(card n)`.

The same estimate holds for `W₁` by monotonicity in the exponent. These bounds transfer small
Frobenius perturbations of matrices to small transport distances between their spectral laws,
with the dimension normalization needed for truncation arguments in global spectral limits.
The norms in this file are Frobenius norms, through `Matrix.Norms.Frobenius`.

The construction reuses `TauCeti.Probability.empiricalMeasureOfFintype`; the matrix inequality
is `Matrix.IsHermitian.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Lemma 2.1.19 and §2.3.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti TauCeti.Probability
open scoped ENNReal Matrix.Norms.Frobenius

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [RCLike 𝕜]
  (A B : Matrix n n 𝕜) (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- The empirical coupling pairing the decreasingly sorted eigenvalues of `A` and `B`,
with mass `1 / card n` at each pair, counted with multiplicity. -/
def spectralCoupling : ProbabilityMeasure (ℝ × ℝ) :=
  empiricalMeasureOfFintype fun i ↦ (hA.eigenvalues₀ i, hB.eigenvalues₀ i)

/-- The spectral coupling is the empirical law of the sorted eigenvalue pairs. -/
theorem spectralCoupling_def :
    spectralCoupling A B hA hB =
      empiricalMeasureOfFintype (fun i ↦ (hA.eigenvalues₀ i, hB.eigenvalues₀ i)) :=
  (rfl)

/-- The first marginal of the sorted spectral coupling is the spectral measure of `A`. -/
@[simp]
theorem fst_spectralCoupling :
    (spectralCoupling A B hA hB : Measure (ℝ × ℝ)).fst = A.spectralMeasure hA := by
  rw [Measure.fst, ← ProbabilityMeasure.toMeasure_map, spectralCoupling_def,
    map_empiricalMeasureOfFintype measurable_fst,
    spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀]
  rfl

/-- The second marginal of the sorted spectral coupling is the spectral measure of `B`. -/
@[simp]
theorem snd_spectralCoupling :
    (spectralCoupling A B hA hB : Measure (ℝ × ℝ)).snd = B.spectralMeasure hB := by
  rw [Measure.snd, ← ProbabilityMeasure.toMeasure_map, spectralCoupling_def,
    map_empiricalMeasureOfFintype measurable_snd,
    spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀]
  rfl

/-- Pairing sorted eigenvalues gives a coupling of the two spectral measures. -/
theorem isCoupling_spectralCoupling :
    IsCoupling (spectralCoupling A B hA hB : Measure (ℝ × ℝ))
      (A.spectralMeasure hA) (B.spectralMeasure hB) :=
  ⟨fst_spectralCoupling A B hA hB, snd_spectralCoupling A B hA hB⟩

/-- Integrating a nonnegative cost against the sorted spectral coupling averages the cost
of the corresponding eigenvalue pairs. -/
theorem lintegral_spectralCoupling {f : ℝ × ℝ → ℝ≥0∞} :
    ∫⁻ z, f z ∂(spectralCoupling A B hA hB : Measure (ℝ × ℝ)) =
      (Fintype.card n : ℝ≥0∞)⁻¹ * ∑ i, f (hA.eigenvalues₀ i, hB.eigenvalues₀ i) := by
  rw [spectralCoupling_def, empiricalMeasureOfFintype_toMeasure]
  simp [lintegral_finsetSum_measure, Finset.mul_sum]

/-- The quadratic transport cost of the sorted spectral coupling is the mean squared
sorted eigenvalue displacement. -/
theorem lintegral_edist_sq_spectralCoupling :
    ∫⁻ z, edist z.1 z.2 ^ 2 ∂(spectralCoupling A B hA hB : Measure (ℝ × ℝ)) =
      ENNReal.ofReal ((Fintype.card n : ℝ)⁻¹ *
        ∑ i, (hA.eigenvalues₀ i - hB.eigenvalues₀ i) ^ 2) := by
  rw [lintegral_spectralCoupling A B hA hB]
  simp only [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]

/-- **Spectral Wasserstein bound, squared form.** The squared `W₂` distance between the
empirical spectral measures is at most the normalized squared Frobenius distance. -/
theorem wassersteinEDist_two_spectralMeasure_sq_le :
    wassersteinEDist 2 (A.spectralMeasure hA : Measure ℝ)
        (B.spectralMeasure hB : Measure ℝ) ^ 2 ≤
      ENNReal.ofReal (‖A - B‖ ^ 2 / Fintype.card n) := by
  have h := wassersteinEDist_rpow_le_lintegral (p := 2) (by fun_prop)
    (by norm_num) (by norm_num) (isCoupling_spectralCoupling A B hA hB)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  refine h.trans ?_
  rw [lintegral_edist_sq_spectralCoupling]
  apply ENNReal.ofReal_le_ofReal
  simpa [div_eq_inv_mul] using mul_le_mul_of_nonneg_left
    (hA.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq hB)
    (by positivity : 0 ≤ (Fintype.card n : ℝ)⁻¹)

/-- **Spectral `W₂` bound.** A Frobenius perturbation of size `ε` moves the empirical spectral
measure by at most `ε / √(card n)` in quadratic Wasserstein distance. -/
theorem wassersteinEDist_two_spectralMeasure_le :
    wassersteinEDist 2 (A.spectralMeasure hA : Measure ℝ)
        (B.spectralMeasure hB : Measure ℝ) ≤
      ENNReal.ofReal (‖A - B‖ / Real.sqrt (Fintype.card n)) := by
  have h := wassersteinEDist_two_spectralMeasure_sq_le A B hA hB
  have heq : (‖A - B‖ / Real.sqrt (Fintype.card n)) ^ 2 =
      ‖A - B‖ ^ 2 / Fintype.card n := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← heq, ENNReal.ofReal_pow (by positivity)] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    (by simpa only [ENNReal.rpow_two] using h)

/-- **Spectral `W₁` bound.** The normalized Frobenius bound also controls the linear
Wasserstein distance between empirical spectral measures. -/
theorem wassersteinEDist_one_spectralMeasure_le :
    wassersteinEDist 1 (A.spectralMeasure hA : Measure ℝ)
        (B.spectralMeasure hB : Measure ℝ) ≤
      ENNReal.ofReal (‖A - B‖ / Real.sqrt (Fintype.card n)) :=
  (wassersteinEDist_mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2) _ _).trans
    (wassersteinEDist_two_spectralMeasure_le A B hA hB)

end Matrix
