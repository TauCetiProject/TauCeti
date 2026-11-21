/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Measure
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Explicit invariant densities of the GOE and GUE

For `0 < n`, `goeMeasure n` and `gueMeasure n` are nonsingular scalar multiples of `stdGaussian` on
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)`. Rescaling `stdGaussian` via
`map_smul_stdGaussian_eq_withDensity_norm` and comparing `volume` with `symmetricLebesgue n` and
`hermitianLebesgue n` yields the AGZ (2.5.1) densities (rescaled by `√n`), valid for all `n : ℕ`,
and equivalence with the independent-entry characterizations.

## Main definitions and results

* `TauCeti.Probability.goePDFReal`, `TauCeti.Probability.goePDF`, `TauCeti.Probability.guePDFReal`,
  `TauCeti.Probability.guePDF`.
* `TauCeti.Probability.goeMeasure_eq_withDensity_symmetricLebesgue`,
  `TauCeti.Probability.gueMeasure_eq_withDensity_hermitianLebesgue`,
  `TauCeti.Probability.hasLaw_withDensity_goePDF_iff`,
  `TauCeti.Probability.hasLaw_withDensity_guePDF_iff`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.5.1, (2.5.1).
-/

public section

noncomputable section

open MeasureTheory Matrix Module ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace TauCeti.Probability

/-- The **GOE density** relative to `TauCeti.symmetricLebesgue n`:
`2 ^ (-n(n + 3)/4) * (n / π) ^ (n(n + 1)/4) * exp (-(n / 4) * tr(H ^ 2))` (AGZ (2.5.1)). -/
def goePDFReal (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ :=
  (2 : ℝ) ^ (-((n : ℝ) * ((n : ℝ) + 3)) / 4) *
    ((n : ℝ) / Real.pi) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
    Real.exp (-((n : ℝ) / 4) * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace)

/-- Defining formula for `TauCeti.Probability.goePDFReal`. -/
theorem goePDFReal_def (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n H = (2 : ℝ) ^ (-((n : ℝ) * ((n : ℝ) + 3)) / 4) *
      ((n : ℝ) / Real.pi) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
      Real.exp (-((n : ℝ) / 4) * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace) := (rfl)

/-- The `ℝ≥0∞`-valued GOE density relative to `TauCeti.symmetricLebesgue n`. -/
def goePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (goePDFReal n H)

/-- Defining formula for `TauCeti.Probability.goePDF`. -/
theorem goePDF_def (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n H = ENNReal.ofReal (goePDFReal n H) := (rfl)

/-- In dimension zero, `TauCeti.Probability.goePDFReal` equals `1`. -/
@[simp] theorem goePDFReal_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    goePDFReal 0 H = 1 := by simp [goePDFReal]

/-- In dimension zero, `TauCeti.Probability.goePDF` equals `1`. -/
@[simp] theorem goePDF_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    goePDF 0 H = 1 := by simp [goePDF]

/-- The real-valued GOE density is nonnegative. -/
theorem goePDFReal_nonneg (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ goePDFReal n H := by unfold goePDFReal; positivity

/-- The real-valued GOE density is strictly positive everywhere. -/
theorem goePDFReal_pos (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDFReal n H := by
  rcases n.eq_zero_or_pos with rfl | hn; · simp
  unfold goePDFReal; positivity

/-- The `ℝ≥0∞`-valued GOE density is strictly positive everywhere. -/
theorem goePDF_pos (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDF n H := ENNReal.ofReal_pos.mpr (goePDFReal_pos n H)

/-- The `ℝ≥0∞`-valued GOE density is finite everywhere. -/
@[simp] theorem goePDF_ne_top (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n H ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `ENNReal.toReal` of `TauCeti.Probability.goePDF` recovers `TauCeti.Probability.goePDFReal`. -/
@[simp] theorem toReal_goePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    (goePDF n H).toReal = goePDFReal n H := ENNReal.toReal_ofReal (goePDFReal_nonneg n H)

/-- `TauCeti.Probability.goePDFReal` is continuous on the real symmetric subspace. -/
@[fun_prop] theorem continuous_goePDFReal (n : ℕ) : Continuous (goePDFReal n) := by
  unfold goePDFReal
  simp_rw [← selfAdjoint.norm_sq_eq_trace_sq]
  fun_prop

/-- `TauCeti.Probability.goePDFReal` is measurable. -/
@[fun_prop] theorem measurable_goePDFReal (n : ℕ) : Measurable (goePDFReal n) :=
  (continuous_goePDFReal n).measurable

/-- `TauCeti.Probability.goePDF` is measurable. -/
@[fun_prop] theorem measurable_goePDF (n : ℕ) : Measurable (goePDF n) :=
  (measurable_goePDFReal n).ennreal_ofReal

/-- `TauCeti.Probability.goePDFReal` is invariant under orthogonal conjugation. -/
@[simp] theorem goePDFReal_symmetricConj {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n (Matrix.UnitaryGroup.symmetricConj U H) = goePDFReal n H := by
  simp only [goePDFReal, ← selfAdjoint.norm_sq_eq_trace_sq, LinearIsometryEquiv.norm_map]

/-- `TauCeti.Probability.goePDF` is invariant under orthogonal conjugation. -/
@[simp] theorem goePDF_symmetricConj {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n (Matrix.UnitaryGroup.symmetricConj U H) = goePDF n H := by simp [goePDF]

/-- `goeMeasure n` has density `((n / (4π)) ^ (n(n + 1)/4)) * exp (-(n / 4) * tr(H ^ 2))` against
`volume`. -/
theorem goeMeasure_eq_withDensity_volume (n : ℕ) :
    goeMeasure n = volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      ENNReal.ofReal (((n : ℝ) / (4 * Real.pi)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        Real.exp (-((n : ℝ) / 4) * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [volume_symmetricMatrix_eq_smul_symmetricLebesgue, symmetricLebesgue_zero]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : Real.sqrt 2 / Real.sqrt n ≠ 0 := by positivity
  have hfinrank : (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [finrank_symmetricMatrix,
      Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_succ_self n)) (by norm_num)]
    push_cast; ring
  rw [goeMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity_norm
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hnR.le, hfinrank,
    selfAdjoint.norm_sq_eq_trace_sq]
  congr 1
  · have hbase : 2 * Real.pi * (2 / (n : ℝ)) = ((n : ℝ) / (4 * Real.pi))⁻¹ := by field_simp; ring
    have hexp : -((n : ℝ) * ((n : ℝ) + 1) / 2) / 2 = -(((n : ℝ) * ((n : ℝ) + 1)) / 4) := by ring
    rw [hbase, hexp, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  · exact congrArg Real.exp (by field_simp; ring)

/-- `goeMeasure n` has density `goePDF n` against `symmetricLebesgue n`. -/
theorem goeMeasure_eq_withDensity_symmetricLebesgue (n : ℕ) :
    goeMeasure n = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_volume n, volume_symmetricMatrix_eq_smul_symmetricLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, goePDF, goePDFReal]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine congrArg ENNReal.ofReal ?_
  have hsplit : ((n : ℝ) / (4 * Real.pi)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) =
      (2 : ℝ) ^ (-2 * ((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        ((n : ℝ) / Real.pi) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
    have h4 : (n : ℝ) / (4 * Real.pi) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ * ((n : ℝ) / Real.pi) := by
      norm_num; ring
    rw [h4, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_natCast 2 2, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    exact congrArg (· * _) (congrArg _ (by ring))
  rw [hsplit, ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  exact congrArg (· * _ * _) (congrArg _ (by ring))

/-- A random matrix with law `goeMeasure n` has a PDF with respect to `symmetricLebesgue n`. -/
theorem hasPDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) : HasPDF H P (symmetricLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (goeMeasure_eq_withDensity_symmetricLebesgue n ▸ hH)

/-- The PDF of a GOE random matrix against `symmetricLebesgue n` is a.e. `goePDF n`. -/
theorem pdf_eq_goePDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) :
    pdf H P (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (goeMeasure_eq_withDensity_symmetricLebesgue n ▸ hH)

/-- The Radon–Nikodym derivative of `goeMeasure n` against `symmetricLebesgue n` is `goePDF n`. -/
theorem rnDeriv_goeMeasure (n : ℕ) :
    (goeMeasure n).rnDeriv (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_goePDF n)

/-- The **GUE density** relative to `TauCeti.hermitianLebesgue n`:
`2 ^ (-n / 2) * (n / π) ^ (n ^ 2 / 2) * exp (-(n / 2) * Re tr(H ^ 2))` (AGZ (2.5.1), `√n` scale). -/
def guePDFReal (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * ((n : ℝ) / Real.pi) ^ (((n : ℝ) ^ 2) / 2) *
    Real.exp (-((n : ℝ) / 2) * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re)

/-- Defining formula for `TauCeti.Probability.guePDFReal`. -/
theorem guePDFReal_def (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n H = (2 : ℝ) ^ (-(n : ℝ) / 2) * ((n : ℝ) / Real.pi) ^ (((n : ℝ) ^ 2) / 2) *
      Real.exp (-((n : ℝ) / 2) * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re) := (rfl)

/-- The `ℝ≥0∞`-valued GUE density relative to `TauCeti.hermitianLebesgue n`. -/
def guePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (guePDFReal n H)

/-- Defining formula for `TauCeti.Probability.guePDF`. -/
theorem guePDF_def (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n H = ENNReal.ofReal (guePDFReal n H) := (rfl)

/-- In dimension zero, `TauCeti.Probability.guePDFReal` equals `1`. -/
@[simp] theorem guePDFReal_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ)) :
    guePDFReal 0 H = 1 := by simp [guePDFReal]

/-- In dimension zero, `TauCeti.Probability.guePDF` equals `1`. -/
@[simp] theorem guePDF_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ)) :
    guePDF 0 H = 1 := by simp [guePDF]

/-- The real-valued GUE density is nonnegative. -/
theorem guePDFReal_nonneg (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 ≤ guePDFReal n H := by unfold guePDFReal; positivity

/-- The real-valued GUE density is strictly positive everywhere. -/
theorem guePDFReal_pos (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDFReal n H := by
  rcases n.eq_zero_or_pos with rfl | hn; · simp
  unfold guePDFReal; positivity

/-- The `ℝ≥0∞`-valued GUE density is strictly positive everywhere. -/
theorem guePDF_pos (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDF n H := ENNReal.ofReal_pos.mpr (guePDFReal_pos n H)

/-- The `ℝ≥0∞`-valued GUE density is finite everywhere. -/
@[simp] theorem guePDF_ne_top (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n H ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `ENNReal.toReal` of `TauCeti.Probability.guePDF` recovers `TauCeti.Probability.guePDFReal`. -/
@[simp] theorem toReal_guePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (guePDF n H).toReal = guePDFReal n H := ENNReal.toReal_ofReal (guePDFReal_nonneg n H)

/-- `TauCeti.Probability.guePDFReal` is continuous on the complex Hermitian subspace. -/
@[fun_prop] theorem continuous_guePDFReal (n : ℕ) : Continuous (guePDFReal n) := by
  unfold guePDFReal
  simp_rw [← selfAdjoint.norm_sq_eq_re_trace_sq]
  fun_prop

/-- `TauCeti.Probability.guePDFReal` is measurable. -/
@[fun_prop] theorem measurable_guePDFReal (n : ℕ) : Measurable (guePDFReal n) :=
  (continuous_guePDFReal n).measurable

/-- `TauCeti.Probability.guePDF` is measurable. -/
@[fun_prop] theorem measurable_guePDF (n : ℕ) : Measurable (guePDF n) :=
  (measurable_guePDFReal n).ennreal_ofReal

/-- `TauCeti.Probability.guePDFReal` is invariant under unitary conjugation. -/
@[simp] theorem guePDFReal_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n (Matrix.UnitaryGroup.hermitianConj U H) = guePDFReal n H := by
  simp only [guePDFReal, ← selfAdjoint.norm_sq_eq_re_trace_sq, LinearIsometryEquiv.norm_map]

/-- `TauCeti.Probability.guePDF` is invariant under unitary conjugation. -/
@[simp] theorem guePDF_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n (Matrix.UnitaryGroup.hermitianConj U H) = guePDF n H := by simp [guePDF]

/-- `gueMeasure n` has density `((n / (2π)) ^ (n ^ 2 / 2)) * exp (-(n / 2) * Re tr(H ^ 2))` against
`volume`. -/
theorem gueMeasure_eq_withDensity_volume (n : ℕ) :
    gueMeasure n = volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
      ENNReal.ofReal (((n : ℝ) / (2 * Real.pi)) ^ (((n : ℝ) ^ 2) / 2) *
        Real.exp (-((n : ℝ) / 2) * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [volume_hermitianMatrix_eq_smul_hermitianLebesgue, hermitianLebesgue_zero]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : (Real.sqrt n)⁻¹ ≠ 0 := by positivity
  rw [gueMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity_norm
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  rw [inv_pow, Real.sq_sqrt hnR.le, finrank_hermitianMatrix, Nat.cast_pow,
    selfAdjoint.norm_sq_eq_re_trace_sq]
  congr 1
  · have hbase : 2 * Real.pi * (n : ℝ)⁻¹ = ((n : ℝ) / (2 * Real.pi))⁻¹ := by field_simp
    rw [hbase, neg_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  · exact congrArg Real.exp (by field_simp)

/-- `gueMeasure n` has density `guePDF n` against `hermitianLebesgue n`. -/
theorem gueMeasure_eq_withDensity_hermitianLebesgue (n : ℕ) :
    gueMeasure n = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_volume n, volume_hermitianMatrix_eq_smul_hermitianLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, guePDF, guePDFReal]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine congrArg ENNReal.ofReal ?_
  have h2 : (n : ℝ) / (2 * Real.pi) = (2 : ℝ)⁻¹ * ((n : ℝ) / Real.pi) := by ring
  rw [h2, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by norm_num),
    ← Real.rpow_neg (by norm_num), ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  exact congrArg (· * _ * _) (congrArg _ (by ring))

/-- A random matrix with law `gueMeasure n` has a PDF with respect to `hermitianLebesgue n`. -/
theorem hasPDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) : HasPDF H P (hermitianLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (gueMeasure_eq_withDensity_hermitianLebesgue n ▸ hH)

/-- The PDF of a GUE random matrix against `hermitianLebesgue n` is a.e. `guePDF n`. -/
theorem pdf_eq_guePDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    pdf H P (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (gueMeasure_eq_withDensity_hermitianLebesgue n ▸ hH)

/-- The Radon–Nikodym derivative of `gueMeasure n` against `hermitianLebesgue n` is `guePDF n`. -/
theorem rnDeriv_gueMeasure (n : ℕ) :
    (gueMeasure n).rnDeriv (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_guePDF n)

/-- **Equivalence of the invariant-density and independent-entry characterizations of the GOE**
(AGZ (2.5.1), p. 52). -/
theorem hasLaw_withDensity_goePDF_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H ((symmetricLebesgue n).withDensity (goePDF n)) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦
          (H ω : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i)
          (gaussianReal 0 (2 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j)
            (gaussianReal 0 (1 / n)) P) := by
  rw [← goeMeasure_eq_withDensity_symmetricLebesgue n, hasLaw_goeMeasure_iff]

/-- **Equivalence of the invariant-density and independent-entry characterizations of the GUE**
(AGZ (2.5.1), p. 52). -/
theorem hasLaw_withDensity_guePDF_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H ((hermitianLebesgue n).withDensity (guePDF n)) P ↔
      iIndepFun (fun (ij : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ij) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
            (gaussianReal 0 (1 / (2 * n))) P ∧
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
            (gaussianReal 0 (1 / (2 * n))) P) := by
  rw [← gueMeasure_eq_withDensity_hermitianLebesgue n, hasLaw_gueMeasure_iff]

end TauCeti.Probability
