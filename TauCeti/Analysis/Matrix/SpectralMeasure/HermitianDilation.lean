/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.HermitianDilation
public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

import TauCeti.Analysis.Complex.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# Spectral measures of Hermitian dilations

The spectral measure of the Hermitian dilation `[[0, Aᴴ], [A, 0]]` of a square matrix
is the symmetrized singular-value measure of `A`. For nonreal `z`, its resolvent transform
at `z` equals `z` times the transform of the squared singular-value measure at `z²`.
In particular, for `A = X - a • 1`, block resolvent estimates for the dilation give
information about the singular values needed in Girko's hermitization.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probability Surveys 9 (2012),
  Lemma 4.19.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The resolvent transform of the Hermitian dilation of a square matrix at `z` equals
`z` times the Gram spectral transform at `z²`, for nonreal `z`. -/
theorem resolventTransform_spectralMeasure_fromBlocks_zero_conjTranspose
    (A : Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD := isHermitian_fromBlocks_zero_conjTranspose A
    resolventTransform (D.spectralMeasure hD : Measure ℝ) z =
      z * resolventTransform
        ((Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A) : Measure ℝ) (z ^ 2) := by
  dsimp only
  have htrace := trace_inv_sub_smul_one_eq_of_charpoly_eq (charpoly_mul_comm A Aᴴ) (z ^ 2)
  have hright := resolventTransform_spectralMeasure _ (isHermitian_conjTranspose_mul_self A)
    ((posSemidef_conjTranspose_mul_self A).sq_notMem_spectrum_of_im_ne_zero hz)
  have hd := isHermitian_fromBlocks_zero_conjTranspose A
  rw [resolventTransform_spectralMeasure _ hd (hd.notMem_spectrum_of_im_ne_zero hz), hright,
    normalizedResolventTrace_sum, normalizedResolventTrace_def]
  simp [inv_fromBlocks_zero_conjTranspose_sub_smul_one A hz, trace_fromBlocks, htrace, ← two_mul]
  ring

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The empirical spectrum of the Hermitian dilation of a square matrix consists of the positive
and negative copies of its singular values, with the two copies of each zero retained. -/
theorem spectralMeasure_fromBlocks_zero_conjTranspose (A : Matrix n n 𝕜) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD := isHermitian_fromBlocks_zero_conjTranspose A
    D.spectralMeasure hD =
      ProbabilityMeasure.convexComb ENNReal.inv_two_add_inv_two A.singularValueMeasure
        (A.singularValueMeasure.map (fun x : ℝ ↦ -x)) := by
  dsimp only
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_resolventTransform fun z hz ↦ ?_
  let f := TauCeti.toComplexStarAlgHom 𝕜
  have hstar := conjTranspose_map f (map_star f) (A := A)
  have hD : (fromBlocks 0 Aᴴ A 0).map f = fromBlocks 0 (A.map f)ᴴ (A.map f) 0 := by
    rw [fromBlocks_map, hstar, Matrix.map_zero f (map_zero f)]
  have hG : (Aᴴ * A).map f = (A.map f)ᴴ * A.map f := by rw [Matrix.map_mul, hstar]
  have htransform := resolventTransform_spectralMeasure_fromBlocks_zero_conjTranspose
    (A.map f) hz.ne'
  simp only [← hD, ← hG, spectralMeasure_map] at htransform
  simpa only [htransform, ← map_singularValueMeasure_sq, ProbabilityMeasure.toMeasure_convexComb,
    ProbabilityMeasure.toMeasure_map] using
    (Measure.resolventTransform_smul_add_smul_map_neg (A.singularValueMeasure : Measure ℝ)
      hz.ne').symm

/-- Taking absolute values in the empirical spectrum of the dilation recovers the singular
values with their original normalization. -/
@[simp]
theorem map_abs_spectralMeasure_fromBlocks_zero_conjTranspose (A : Matrix n n 𝕜) :
    let D := fromBlocks 0 Aᴴ A 0
    let hD := isHermitian_fromBlocks_zero_conjTranspose A
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
