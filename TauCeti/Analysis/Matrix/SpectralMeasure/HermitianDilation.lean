/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

import TauCeti.Analysis.Matrix.Resolvent.HermitianDilation
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# Spectral measures of Hermitian dilations

The spectral measure of the Hermitian dilation `[[0, Aᴴ], [A, 0]]` of a square matrix
is the symmetrized singular-value measure of `A`. Its resolvent transform at `z` equals
`z` times the transform of the squared singular-value measure at `z²`.
In particular, for `A = X - a • 1`, block resolvent estimates for the dilation give
information about the singular values needed in Girko's hermitization.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probability Surveys 9 (2012),
  Lemma 4.19.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder ENNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The resolvent transform of the Hermitian dilation of a square matrix at `z` equals
`z` times the Gram spectral transform at `z²`, for nonreal `z`. -/
theorem resolventTransform_spectralMeasure_fromBlocks_zero_conjTranspose
    (A : Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD : D.IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero (conjTranspose_conjTranspose A) isHermitian_zero
    resolventTransform (D.spectralMeasure hD : Measure ℝ) z =
      z * resolventTransform
        ((Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A) : Measure ℝ) (z ^ 2) := by
  dsimp only
  have houtside {B : Matrix n n ℂ} (hB : B.PosSemidef) : z ^ 2 ∉ spectrum ℂ B := by
    rw [hB.isHermitian.spectrum_eq_image_range, RCLike.ofReal_eq_complex_ofReal]
    rintro ⟨_, ⟨i, rfl⟩, hi⟩
    have him := congrArg Complex.im hi
    simp only [Complex.ofReal_im, pow_two, Complex.mul_im] at him
    have hzr : z.re = 0 := (mul_eq_zero.mp (by linarith only [him] :
      z.re * z.im = 0)).resolve_right hz
    have hre := congrArg Complex.re hi
    simp only [Complex.ofReal_re, pow_two, Complex.mul_re, hzr, zero_mul, zero_sub] at hre
    nlinarith [hB.eigenvalues_nonneg i, sq_pos_of_ne_zero hz]
  have hgram := spectralMeasure_eq_of_charpoly_eq (isHermitian_mul_conjTranspose_self A)
    (isHermitian_conjTranspose_mul_self A) (charpoly_mul_comm A Aᴴ)
  have hright := resolventTransform_spectralMeasure _ (isHermitian_conjTranspose_mul_self A)
    (houtside (posSemidef_conjTranspose_mul_self A))
  have hleft := resolventTransform_spectralMeasure _ (isHermitian_mul_conjTranspose_self A)
    (houtside (posSemidef_self_mul_conjTranspose A))
  rw [hgram] at hleft
  have hd := IsHermitian.fromBlocks isHermitian_zero
    (conjTranspose_conjTranspose A) isHermitian_zero
  rw [resolventTransform_spectralMeasure _ hd (hd.notMem_spectrum_of_im_ne_zero hz),
    inv_fromBlocks_zero_conjTranspose_sub_smul_one A hz, trace_fromBlocks, trace_smul, trace_smul,
    Fintype.card_sum, Nat.cast_add, smul_eq_mul, smul_eq_mul, hright]
  rw [hright] at hleft
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by simp
  have htrace := mul_left_cancel₀ (inv_ne_zero hcard) hleft
  rw [← htrace]
  field_simp

/-- The empirical spectrum of the Hermitian dilation of a square matrix consists of the positive
and negative copies of its singular values, with the two copies of each zero retained. -/
theorem spectralMeasure_fromBlocks_zero_conjTranspose (A : Matrix n n ℂ) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD : D.IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero (conjTranspose_conjTranspose A) isHermitian_zero
    D.spectralMeasure hD =
      ProbabilityMeasure.convexComb ENNReal.inv_two_add_inv_two A.singularValueMeasure
        (A.singularValueMeasure.map (fun x : ℝ ↦ -x)) := by
  dsimp only
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_resolventTransform fun z hz ↦ ?_
  let ν : Measure ℝ := A.singularValueMeasure
  have hc := (Complex.continuous_resolvent_real hz.ne').stronglyMeasurable
  have hi : Integrable (resolvent z) ν := integrable_resolvent_of_im_ne_zero hz.ne'
  have hin : Integrable (resolvent z) (ν.map (fun x : ℝ ↦ -x)) :=
    integrable_resolvent_of_im_ne_zero hz.ne'
  have hkernel (x : ℝ) :
      (2 : ℂ)⁻¹ * (resolvent z x + resolvent z (-x)) = z * resolvent (z ^ 2) (x ^ 2) := by
    have hne (y : ℝ) : (y : ℂ) - z ≠ 0 := fun h ↦
      hz.ne' (by simpa using congrArg Complex.im h)
    have hfactor : ((x : ℂ) ^ 2 - z ^ 2) = ((x : ℂ) - z) * ((x : ℂ) + z) := by ring
    have hplus : (x : ℂ) + z ≠ 0 := fun h ↦ hz.ne' (by simpa using congrArg Complex.im h)
    simp only [Complex.resolvent_real_eq_inv, Complex.ofReal_pow, Complex.ofReal_neg]
    have hneg : -(x : ℂ) - z ≠ 0 := by simpa using hne (-x)
    field_simp [hne x, hneg, hfactor, hplus]
    ring
  have hsq : (A.singularValueMeasure.map (fun x : ℝ ↦ x ^ 2) : Measure ℝ) =
      ν.map (fun x : ℝ ↦ x ^ 2) := ProbabilityMeasure.toMeasure_map _
  rw [resolventTransform_spectralMeasure_fromBlocks_zero_conjTranspose A hz.ne',
    ← map_singularValueMeasure_sq, hsq, ProbabilityMeasure.toMeasure_convexComb,
    ProbabilityMeasure.toMeasure_map, resolventTransform_apply, resolventTransform_apply,
    integral_add_measure (hi.smul_measure (by simp)) (hin.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_map_of_stronglyMeasurable measurable_neg hc,
    integral_map_of_stronglyMeasurable (by fun_prop : Measurable (fun x : ℝ ↦ x ^ 2))
      (by fun_prop)]
  have hin' : Integrable (fun x : ℝ ↦ resolvent z (-x)) ν :=
    (integrable_map_measure hc.aestronglyMeasurable measurable_neg.aemeasurable).mp hin
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_ofNat]
  rw [← mul_add, ← integral_add hi hin', ← integral_const_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (hkernel x).symm)

/-- Taking absolute values in the empirical spectrum of the dilation recovers the singular
values with their original normalization. -/
@[simp]
theorem map_abs_spectralMeasure_fromBlocks_zero_conjTranspose (A : Matrix n n ℂ) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD : D.IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero (conjTranspose_conjTranspose A) isHermitian_zero
    (D.spectralMeasure hD).map abs = A.singularValueMeasure := by
  dsimp only
  rw [spectralMeasure_fromBlocks_zero_conjTranspose, ProbabilityMeasure.map_convexComb
    continuous_abs.measurable]
  have habs : A.singularValueMeasure.map abs = A.singularValueMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact Measure.map_congr (ae_nonneg_singularValueMeasure A |>.mono fun x hx ↦ abs_of_nonneg hx)
      |>.trans Measure.map_id
  have hneg : (A.singularValueMeasure.map (fun x : ℝ ↦ -x)).map abs =
      A.singularValueMeasure.map abs := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [ProbabilityMeasure.toMeasure_map, Measure.map_map continuous_abs.measurable
      measurable_neg, Function.comp_def]
  rw [hneg, habs, ProbabilityMeasure.convexComb_self]

end Matrix
