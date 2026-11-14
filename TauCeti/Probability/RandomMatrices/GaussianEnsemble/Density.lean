/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Measure
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Explicit invariant densities and entry characterizations of the GOE and GUE

For `0 < n`, `TauCeti.Probability.goeMeasure n` and `TauCeti.Probability.gueMeasure n` are
nonsingular scalar multiples of `ProbabilityTheory.stdGaussian` on the finite-dimensional real
Frobenius inner product spaces `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` and
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`. Rescaling `stdGaussian` via
`TauCeti.Probability.map_smul_stdGaussian_eq_withDensity_norm` and comparing `volume` with
`TauCeti.symmetricLebesgue n` and `TauCeti.hermitianLebesgue n` yields the classical coordinate
densities (AGZ (2.5.1), rescaled by `√n`) and the equivalence between the independent-entry and
invariant-density characterizations.

## Main definitions and results

* `TauCeti.Probability.goePDFReal`, `TauCeti.Probability.goePDF`, `TauCeti.Probability.guePDFReal`,
  `TauCeti.Probability.guePDF` — GOE and GUE densities against `symmetricLebesgue` and
  `hermitianLebesgue`.
* `TauCeti.Probability.goeMeasure_eq_withDensity_symmetricLebesgue`,
  `TauCeti.Probability.goeMeasure_eq_withDensity_volume`,
  `TauCeti.Probability.gueMeasure_eq_withDensity_hermitianLebesgue`,
  `TauCeti.Probability.gueMeasure_eq_withDensity_volume` — explicit densities for `0 < n`.
* `TauCeti.Probability.hasPDF_of_hasLaw_goeMeasure`, `TauCeti.Probability.rnDeriv_goeMeasure`,
  `TauCeti.Probability.hasPDF_of_hasLaw_gueMeasure`, `TauCeti.Probability.rnDeriv_gueMeasure`,
  `TauCeti.Probability.hasLaw_goeMeasure_iff`, `TauCeti.Probability.hasLaw_withDensity_goePDF_iff`,
  `TauCeti.Probability.hasLaw_gueMeasure_iff`, `TauCeti.Probability.hasLaw_withDensity_guePDF_iff` —
  `HasPDF`, Radon–Nikodym, and independent-entry characterizations.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.1, (2.5.1).
-/

public section

noncomputable section

open MeasureTheory Matrix Module ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace TauCeti.Probability

/-! ### Explicit invariant densities on the real self-adjoint spaces -/

/-- The **GOE density** on `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` relative to
`TauCeti.symmetricLebesgue n`:
`2 ^ (-n(n + 3)/4) * (n / π) ^ (n(n + 1)/4) * exp (-(n / 4) * tr(H ^ 2))`
(AGZ (2.5.1) for `β = 1`, rescaled by `√n`). -/
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

/-- The real-valued GOE density is nonnegative. -/
theorem goePDFReal_nonneg (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ goePDFReal n H := by unfold goePDFReal; positivity

/-- For `0 < n`, the real-valued GOE density is strictly positive everywhere. -/
theorem goePDFReal_pos {n : ℕ} (hn : 0 < n)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : 0 < goePDFReal n H := by
  unfold goePDFReal; positivity

/-- For `0 < n`, the `ℝ≥0∞`-valued GOE density is strictly positive everywhere. -/
theorem goePDF_pos {n : ℕ} (hn : 0 < n)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : 0 < goePDF n H :=
  ENNReal.ofReal_pos.mpr (goePDFReal_pos hn H)

/-- The `ℝ≥0∞`-valued GOE density is finite everywhere. -/
@[simp] theorem goePDF_ne_top (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n H ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `ENNReal.toReal` of `TauCeti.Probability.goePDF` recovers `TauCeti.Probability.goePDFReal`. -/
@[simp] theorem toReal_goePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    (goePDF n H).toReal = goePDFReal n H := ENNReal.toReal_ofReal (goePDFReal_nonneg n H)

/-- `TauCeti.Probability.goePDFReal` is continuous on the real symmetric subspace. -/
theorem continuous_goePDFReal (n : ℕ) : Continuous (goePDFReal n) := by
  simp only [show goePDFReal n = fun H ↦ (2 : ℝ) ^ (-((n : ℝ) * ((n : ℝ) + 3)) / 4) *
      ((n : ℝ) / Real.pi) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
      Real.exp (-((n : ℝ) / 4) * ‖H‖ ^ 2)
    from funext fun H ↦ by rw [goePDFReal, selfAdjoint.norm_sq_eq_trace_sq]]; fun_prop

/-- `TauCeti.Probability.goePDFReal` is measurable. -/
@[fun_prop] theorem measurable_goePDFReal (n : ℕ) : Measurable (goePDFReal n) :=
  (continuous_goePDFReal n).measurable

/-- `TauCeti.Probability.goePDF` is measurable. -/
@[fun_prop] theorem measurable_goePDF (n : ℕ) : Measurable (goePDF n) :=
  (measurable_goePDFReal n).ennreal_ofReal

/-- `TauCeti.Probability.goePDFReal` is invariant under orthogonal conjugation. -/
@[simp] theorem goePDFReal_symmetricConj {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n (Matrix.unitaryGroup.symmetricConj U H) = goePDFReal n H := by
  simp only [goePDFReal, ← selfAdjoint.norm_sq_eq_trace_sq, LinearIsometryEquiv.norm_map]

/-- `TauCeti.Probability.goePDF` is invariant under orthogonal conjugation. -/
@[simp] theorem goePDF_symmetricConj {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n (Matrix.unitaryGroup.symmetricConj U H) = goePDF n H := by simp [goePDF]

/-- For `0 < n`, `TauCeti.Probability.goeMeasure n` has density
`((n / (4π)) ^ (n(n + 1)/4)) * exp (-(n / 4) * tr(H ^ 2))` against the Frobenius `volume`. -/
theorem goeMeasure_eq_withDensity_volume {n : ℕ} (hn : 0 < n) :
    goeMeasure n = volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      ENNReal.ofReal (((n : ℝ) / (4 * Real.pi)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        Real.exp (-((n : ℝ) / 4) * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : Real.sqrt 2 / Real.sqrt n ≠ 0 := by positivity
  have hfinrank : (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [finrank_symmetricMatrix,
      Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_succ_self n)) (by norm_num)]
    push_cast; rfl
  rw [goeMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity_norm _ hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hnR.le, hfinrank,
    selfAdjoint.norm_sq_eq_trace_sq,
    show 2 * Real.pi * (2 / (n : ℝ)) = ((n : ℝ) / (4 * Real.pi))⁻¹ by field_simp; ring,
    show -((n : ℝ) * ((n : ℝ) + 1) / 2) / 2 = -(((n : ℝ) * ((n : ℝ) + 1)) / 4) by ring,
    Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
    show -((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace / (2 * (2 / (n : ℝ))) =
      -((n : ℝ) / 4) * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace by field_simp; ring]

/-- For `0 < n`, `TauCeti.Probability.goeMeasure n` has density `TauCeti.Probability.goePDF n`
against `TauCeti.symmetricLebesgue n`. -/
theorem goeMeasure_eq_withDensity_symmetricLebesgue {n : ℕ} (hn : 0 < n) :
    goeMeasure n = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_volume hn, volume_symmetricMatrix_eq_smul_symmetricLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, goePDF, goePDFReal]
  rw [show Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 4) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) from rfl,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine congrArg ENNReal.ofReal ?_
  have hsplit : ((n : ℝ) / (4 * Real.pi)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) =
      (2 : ℝ) ^ (-2 * ((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        ((n : ℝ) / Real.pi) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
    rw [show (n : ℝ) / (4 * Real.pi) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ * ((n : ℝ) / Real.pi) by
        norm_num; ring,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_natCast 2 2, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    exact congrArg (· * _) (congrArg _ (by ring))
  rw [hsplit, ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  exact congrArg (· * _ * _) (congrArg _ (by ring))

/-- For `0 < n`, a random matrix with law `TauCeti.Probability.goeMeasure n` has a PDF with
respect to `TauCeti.symmetricLebesgue n`. -/
theorem hasPDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (hn : 0 < n) {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) : HasPDF H P (symmetricLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (goeMeasure_eq_withDensity_symmetricLebesgue hn ▸ hH)

/-- For `0 < n`, the PDF of a GOE random matrix against `TauCeti.symmetricLebesgue n` coincides
almost everywhere with `TauCeti.Probability.goePDF n`. -/
theorem pdf_eq_goePDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (hn : 0 < n) {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) :
    pdf H P (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (goeMeasure_eq_withDensity_symmetricLebesgue hn ▸ hH)

/-- For `0 < n`, the Radon–Nikodym derivative of `TauCeti.Probability.goeMeasure n` against
`TauCeti.symmetricLebesgue n` is `TauCeti.Probability.goePDF n`. -/
theorem rnDeriv_goeMeasure {n : ℕ} (hn : 0 < n) :
    (goeMeasure n).rnDeriv (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue hn]
  exact Measure.rnDeriv_withDensity _ (measurable_goePDF n)

/-- The **GUE density** on `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)` relative to
`TauCeti.hermitianLebesgue n`:
`2 ^ (-n / 2) * (n / π) ^ (n ^ 2 / 2) * exp (-(n / 2) * Re tr(H ^ 2))`
(AGZ (2.5.1) for `β = 2`, rescaled by `√n`). -/
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

/-- The real-valued GUE density is nonnegative. -/
theorem guePDFReal_nonneg (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 ≤ guePDFReal n H := by unfold guePDFReal; positivity

/-- For `0 < n`, the real-valued GUE density is strictly positive everywhere. -/
theorem guePDFReal_pos {n : ℕ} (hn : 0 < n)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : 0 < guePDFReal n H := by
  unfold guePDFReal; positivity

/-- For `0 < n`, the `ℝ≥0∞`-valued GUE density is strictly positive everywhere. -/
theorem guePDF_pos {n : ℕ} (hn : 0 < n)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : 0 < guePDF n H :=
  ENNReal.ofReal_pos.mpr (guePDFReal_pos hn H)

/-- The `ℝ≥0∞`-valued GUE density is finite everywhere. -/
@[simp] theorem guePDF_ne_top (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n H ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `ENNReal.toReal` of `TauCeti.Probability.guePDF` recovers `TauCeti.Probability.guePDFReal`. -/
@[simp]
theorem toReal_guePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (guePDF n H).toReal = guePDFReal n H := ENNReal.toReal_ofReal (guePDFReal_nonneg n H)

/-- `TauCeti.Probability.guePDFReal` is continuous on the complex Hermitian subspace. -/
theorem continuous_guePDFReal (n : ℕ) : Continuous (guePDFReal n) := by
  simp only [show guePDFReal n = fun H ↦
      (2 : ℝ) ^ (-(n : ℝ) / 2) * ((n : ℝ) / Real.pi) ^ (((n : ℝ) ^ 2) / 2) *
        Real.exp (-((n : ℝ) / 2) * ‖H‖ ^ 2)
    from funext fun H ↦ by rw [guePDFReal, selfAdjoint.norm_sq_eq_re_trace_sq]]
  fun_prop

/-- `TauCeti.Probability.guePDFReal` is measurable. -/
@[fun_prop]
theorem measurable_guePDFReal (n : ℕ) : Measurable (guePDFReal n) :=
  (continuous_guePDFReal n).measurable

/-- `TauCeti.Probability.guePDF` is measurable. -/
@[fun_prop]
theorem measurable_guePDF (n : ℕ) : Measurable (guePDF n) :=
  (measurable_guePDFReal n).ennreal_ofReal

/-- `TauCeti.Probability.guePDFReal` is invariant under unitary conjugation. -/
@[simp]
theorem guePDFReal_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n (Matrix.unitaryGroup.hermitianConj U H) = guePDFReal n H := by
  simp only [guePDFReal, ← selfAdjoint.norm_sq_eq_re_trace_sq, LinearIsometryEquiv.norm_map]

/-- `TauCeti.Probability.guePDF` is invariant under unitary conjugation. -/
@[simp]
theorem guePDF_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n (Matrix.unitaryGroup.hermitianConj U H) = guePDF n H := by simp [guePDF]

/-- For `0 < n`, `TauCeti.Probability.gueMeasure n` has density
`((n / (2π)) ^ (n ^ 2 / 2)) * exp (-(n / 2) * Re tr(H ^ 2))` against the trace-inner-product
`volume`. -/
theorem gueMeasure_eq_withDensity_volume {n : ℕ} (hn : 0 < n) :
    gueMeasure n =
      volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
        ENNReal.ofReal
          (((n : ℝ) / (2 * Real.pi)) ^ (((n : ℝ) ^ 2) / 2) *
            Real.exp (-((n : ℝ) / 2) * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : (Real.sqrt n)⁻¹ ≠ 0 := by positivity
  rw [gueMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity_norm _ hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  rw [inv_pow, Real.sq_sqrt hnR.le, finrank_hermitianMatrix, Nat.cast_pow,
    selfAdjoint.norm_sq_eq_re_trace_sq,
    show 2 * Real.pi * (n : ℝ)⁻¹ = ((n : ℝ) / (2 * Real.pi))⁻¹ by field_simp,
    show -((n : ℝ) ^ 2) / 2 = -(((n : ℝ) ^ 2) / 2) by ring,
    Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
    show -((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re / (2 * (n : ℝ)⁻¹) =
      -((n : ℝ) / 2) * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re by field_simp]

/-- For `0 < n`, `TauCeti.Probability.gueMeasure n` has density `TauCeti.Probability.guePDF n`
against `TauCeti.hermitianLebesgue n`. -/
theorem gueMeasure_eq_withDensity_hermitianLebesgue {n : ℕ} (hn : 0 < n) :
    gueMeasure n = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_volume hn, volume_hermitianMatrix_eq_smul_hermitianLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, guePDF, guePDFReal]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine congrArg ENNReal.ofReal ?_
  rw [show (n : ℝ) / (2 * Real.pi) = (2 : ℝ)⁻¹ * ((n : ℝ) / Real.pi) by ring,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by norm_num),
    ← Real.rpow_neg (by norm_num), ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  exact congrArg (· * _ * _) (congrArg _ (by ring))

/-- For `0 < n`, a random matrix with law `TauCeti.Probability.gueMeasure n` has a PDF with
respect to `TauCeti.hermitianLebesgue n`. -/
theorem hasPDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 0 < n) {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    HasPDF H P (hermitianLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (gueMeasure_eq_withDensity_hermitianLebesgue hn ▸ hH)

/-- For `0 < n`, the PDF of a GUE random matrix against `TauCeti.hermitianLebesgue n` coincides
almost everywhere with `TauCeti.Probability.guePDF n`. -/
theorem pdf_eq_guePDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 0 < n) {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    pdf H P (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (gueMeasure_eq_withDensity_hermitianLebesgue hn ▸ hH)

/-- For `0 < n`, the Radon–Nikodym derivative of `TauCeti.Probability.gueMeasure n` against
`TauCeti.hermitianLebesgue n` is `TauCeti.Probability.guePDF n`. -/
theorem rnDeriv_gueMeasure {n : ℕ} (hn : 0 < n) :
    (gueMeasure n).rnDeriv (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue hn]
  exact Measure.rnDeriv_withDensity _ (measurable_guePDF n)

/-! ### Equivalence of the independent-entry and invariant-density characterizations -/

private theorem map_const_mul_gaussianReal_std (c : ℝ) {v : ℝ≥0} (hv : c ^ 2 = v) :
    (gaussianReal 0 1).map (c * ·) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  exact congrArg (gaussianReal 0) (NNReal.eq hv)

/-- Under `TauCeti.Probability.goeMeasure n`, the upper-triangular coordinates are independent real
Gaussians: `N(0, 2 / n)` on the diagonal and `N(0, 1 / n)` above it. -/
theorem map_symmetricCoordinates_goeMeasure (n : ℕ) :
    (goeMeasure n).map (symmetricCoordinates n) =
      Measure.pi fun ij : upperTriangle n ↦
        if ij.1.1 = ij.1.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n) := by
  have hproj := measurePreserving_pi_comp_embedding
    (fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
    (Function.Embedding.subtype fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2)
  let scale : upperTriangle n → ℝ → ℝ := fun ij t ↦
    (Real.sqrt n)⁻¹ * ((if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * t)
  have hfactor (ij : upperTriangle n) : (gaussianReal 0 1).map (scale ij) =
      if ij.1.1 = ij.1.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n) := by
    simp only [scale, ← mul_assoc]
    split_ifs with hd <;> refine map_const_mul_gaussianReal_std _ ?_
    · rw [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast, mul_pow, inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by norm_num), div_eq_inv_mul]
    · rw [mul_one, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast, inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg n), one_div]
  have : ∀ ij : upperTriangle n, SigmaFinite ((gaussianReal 0 1).map (scale ij)) :=
    fun ij ↦ hfactor ij ▸ inferInstance
  have hm_scale : Measurable fun (x : upperTriangle n → ℝ) ij ↦ scale ij (x ij) := by fun_prop
  rw [goeMeasure_def, Measure.map_map (symmetricCoordinates n).continuous.measurable
    (measurable_goeMatrix n),
    show (symmetricCoordinates n ∘ goeMatrix n : (Fin n × Fin n → ℝ) → upperTriangle n → ℝ) =
      (fun (x : upperTriangle n → ℝ) ij ↦ scale ij (x ij)) ∘
        fun g ij ↦ g ((Function.Embedding.subtype fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2) ij)
      from funext fun g ↦ funext (symmetricCoordinates_goeMatrix n g),
    ← Measure.map_map hm_scale hproj.measurable, hproj.map_eq,
    Measure.pi_map_pi fun ij ↦ by fun_prop]
  exact congrArg Measure.pi (funext hfactor)

/-- Under `TauCeti.Probability.gueMeasure n`, `TauCeti.hermitianCoordinates n` has independent
Gaussian coordinates: `N(0, 1 / n)` on the diagonal and `N(0, 1 / (2 * n))` off the diagonal. -/
theorem map_hermitianCoordinates_gueMeasure (n : ℕ) :
    (gueMeasure n).map (hermitianCoordinates n) =
      Measure.pi fun ij : Fin n × Fin n ↦
        if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n)) := by
  let scale : Fin n × Fin n → ℝ → ℝ := fun ij t ↦
    (Real.sqrt n)⁻¹ * ((if ij.1 = ij.2 then 1 else (Real.sqrt 2)⁻¹) * t)
  have hfactor (ij : Fin n × Fin n) : (gaussianReal 0 1).map (scale ij) =
      if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n)) := by
    simp only [scale, ← mul_assoc]
    split_ifs with hd <;> refine map_const_mul_gaussianReal_std _ ?_
    · rw [mul_one, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast, inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg n), one_div]
    · rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
        mul_pow, inv_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by norm_num),
        one_div, mul_inv, mul_comm (2 : ℝ)⁻¹]
  have : ∀ ij : Fin n × Fin n, SigmaFinite ((gaussianReal 0 1).map (scale ij)) :=
    fun ij ↦ hfactor ij ▸ inferInstance
  rw [gueMeasure_def, Measure.map_map (hermitianCoordinates n).continuous.measurable
    (measurable_gueMatrix n),
    show (hermitianCoordinates n ∘ gueMatrix n : (Fin n × Fin n → ℝ) → Fin n × Fin n → ℝ) =
      fun g ij ↦ scale ij (g ij) from funext fun g ↦ funext (hermitianCoordinates_gueMatrix n g),
    Measure.pi_map_pi fun ij ↦ by fun_prop]
  exact congrArg Measure.pi (funext hfactor)

/-- **Characterization of the GOE by independent Gaussian entries.** A random symmetric matrix `H`
has law `TauCeti.Probability.goeMeasure n` if and only if its on-or-above-diagonal entries are
mutually independent, with `H i i ~ N(0, 2 / n)` and `H i j ~ N(0, 1 / n)` for `i < j`. -/
theorem hasLaw_goeMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦
          (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i)
          (gaussianReal 0 (2 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j)
            (gaussianReal 0 (1 / n)) P) := by
  let μ : upperTriangle n → Measure ℝ := fun ij ↦
    if ij.1.1 = ij.1.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n)
  have hm :
      MeasurePreserving (symmetricCoordinatesMeasurableEquiv n) (goeMeasure n) (Measure.pi μ) :=
    ⟨(symmetricCoordinatesMeasurableEquiv n).measurable,
      symmetricCoordinatesMeasurableEquiv_coe n ▸ map_symmetricCoordinates_goeMeasure n⟩
  have hsc : (fun ω (ij : upperTriangle n) ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) =
      fun ω ↦ symmetricCoordinates n (H ω) :=
    funext fun ω ↦ funext fun ij ↦ (symmetricCoordinates_apply n (H ω) ij).symm
  constructor
  · intro hH
    have hcoord : HasLaw (fun ω (ij : upperTriangle n) ↦
        (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) (Measure.pi μ) P :=
      hsc ▸ by simpa using hm.fun_comp_hasLaw hH
    have heach (ij : upperTriangle n) := (measurePreserving_eval μ ij).fun_comp_hasLaw hcoord
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi heach).2 hcoord,
      fun i ↦ by simpa [μ] using heach ⟨(i, i), le_rfl⟩,
      fun i j hij ↦ by simpa [μ, hij.ne] using heach ⟨(i, j), hij.le⟩⟩
  · rintro ⟨hindep, hdiag, hoff⟩
    have heach (ij : upperTriangle n) :
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) (μ ij) P := by
      rcases ij.2.eq_or_lt with h | hlt
      · obtain ⟨⟨i, j⟩, _⟩ := ij; cases h; simpa [μ] using hdiag i
      · simpa [μ, hlt.ne] using hoff hlt
    have hcoord : HasLaw (fun ω ↦ symmetricCoordinates n (H ω)) (Measure.pi μ) P :=
      hsc ▸ hindep.hasLaw_pi heach
    simpa using (hm.symm (symmetricCoordinatesMeasurableEquiv n)).fun_comp_hasLaw hcoord

/-- **Equivalence of the invariant-density and independent-entry characterizations of the GOE**
(AGZ (2.5.1) and following paragraph, p. 52). For `0 < n`, a random symmetric matrix `H` has law
`(symmetricLebesgue n).withDensity (goePDF n)` if and only if its on-or-above-diagonal entries are
mutually independent with `H i i ~ N(0, 2 / n)` and `H i j ~ N(0, 1 / n)` for `i < j`. -/
theorem hasLaw_withDensity_goePDF_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 0 < n)
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H ((symmetricLebesgue n).withDensity (goePDF n)) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦
          (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i)
          (gaussianReal 0 (2 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j)
            (gaussianReal 0 (1 / n)) P) := by
  rw [← goeMeasure_eq_withDensity_symmetricLebesgue hn]
  exact ⟨fun hH ↦ let _ := hH.isProbabilityMeasure; hasLaw_goeMeasure_iff.mp hH,
    fun h ↦ let _ := (h.2.1 ⟨0, hn⟩).isProbabilityMeasure; hasLaw_goeMeasure_iff.mpr h⟩

/-- **Characterization of the GUE by independent Gaussian entries.** A random Hermitian matrix `H`
has law `TauCeti.Probability.gueMeasure n` if and only if the `n ^ 2` real coordinates
`TauCeti.hermitianCoordinates n (H ω)` — namely `(H i i).re` on the diagonal together with
`(H i j).re` and `(H i j).im` above the diagonal — are mutually independent, with
`(H i i).re ~ N(0, 1 / n)` and `(H i j).re, (H i j).im ~ N(0, 1 / (2 * n))` for `i < j`. -/
theorem hasLaw_gueMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      iIndepFun (fun (ij : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ij) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
            (gaussianReal 0 (1 / (2 * n))) P ∧
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
            (gaussianReal 0 (1 / (2 * n))) P) := by
  let μ : Fin n × Fin n → Measure ℝ := fun ij ↦
    if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n))
  have hm :
      MeasurePreserving (hermitianCoordinatesMeasurableEquiv n) (gueMeasure n) (Measure.pi μ) :=
    ⟨(hermitianCoordinatesMeasurableEquiv n).measurable,
      hermitianCoordinatesMeasurableEquiv_coe n ▸ map_hermitianCoordinates_gueMeasure n⟩
  constructor
  · intro hH
    have hcoord : HasLaw (fun ω ↦ hermitianCoordinates n (H ω)) (Measure.pi μ) P := by
      simpa using hm.fun_comp_hasLaw hH
    have heach (ij : Fin n × Fin n) := (measurePreserving_eval μ ij).fun_comp_hasLaw hcoord
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi heach).2 hcoord,
      fun i ↦ by simpa [μ] using heach (i, i),
      fun i j hij ↦ ⟨by simpa [μ, hij.le, hij.ne] using heach (i, j),
        by simpa [μ, hij, hij.ne'] using heach (j, i)⟩⟩
  · rintro ⟨hindep, hdiag, hoff⟩
    have heach : ∀ ij : Fin n × Fin n,
        HasLaw (fun ω ↦ hermitianCoordinates n (H ω) ij) (μ ij) P
      | (i, j) => by
        rcases lt_trichotomy i j with h | rfl | h
        · simpa [μ, h.le, h.ne] using (hoff h).1
        · simpa [μ] using hdiag i
        · simpa [μ, h, h.ne'] using (hoff h).2
    simpa using (hm.symm (hermitianCoordinatesMeasurableEquiv n)).fun_comp_hasLaw
      (hindep.hasLaw_pi heach)

/-- **Equivalence of the invariant-density and independent-entry characterizations of the GUE**
(AGZ (2.5.1) and following paragraph, p. 52). For `0 < n`, a random Hermitian matrix `H` has law
`(hermitianLebesgue n).withDensity (guePDF n)` if and only if its `n ^ 2` real coordinates
`TauCeti.hermitianCoordinates n (H ω)` are mutually independent with `(H i i).re ~ N(0, 1 / n)`
and `(H i j).re, (H i j).im ~ N(0, 1 / (2 * n))` for `i < j`. -/
theorem hasLaw_withDensity_guePDF_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 0 < n)
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
  rw [← gueMeasure_eq_withDensity_hermitianLebesgue hn]
  exact ⟨fun hH ↦ let _ := hH.isProbabilityMeasure; hasLaw_gueMeasure_iff.mp hH,
    fun h ↦ let _ := (h.2.1 ⟨0, hn⟩).isProbabilityMeasure; hasLaw_gueMeasure_iff.mpr h⟩

end TauCeti.Probability
