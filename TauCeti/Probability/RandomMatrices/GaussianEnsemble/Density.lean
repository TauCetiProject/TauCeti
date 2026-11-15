/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Law

/-!
# Invariant trace densities and characterizations of the GOE and GUE

From the rescaled `ProbabilityTheory.stdGaussian` representations of
`TauCeti.Probability.goeMeasure` and `TauCeti.Probability.gueMeasure` in
`TauCeti.Probability.RandomMatrices.GaussianEnsemble.Law` and the Frobenius-volume comparisons on
the symmetric and Hermitian subspaces, this file establishes:
1. the exact densities `TauCeti.Probability.goePDF` with respect to `TauCeti.symmetricLebesgue n`
   and `TauCeti.Probability.guePDF` with respect to `TauCeti.hermitianLebesgue n` (as well as with
   respect to the Frobenius `volume`) at every dimension `n : ℕ`;
2. Radon–Nikodym, `MeasureTheory.HasPDF`, and `MeasureTheory.pdf` bridges for GOE and GUE random
   matrices;
3. the equivalence of the independent-Gaussian entry characterization and the invariant
   trace-density characterization for both ensembles (`goe_iIndepFun_iff_withDensity` and
   `gue_iIndepFun_iff_withDensity`).

## Main definitions

* `TauCeti.Probability.goePDFReal`, `TauCeti.Probability.goePDF`: the GOE trace density on the real
  symmetric subspace.
* `TauCeti.Probability.guePDFReal`, `TauCeti.Probability.guePDF`: the GUE trace density on the
  complex Hermitian subspace.

## Main results

* `TauCeti.Probability.goeMeasure_eq_withDensity_symmetricLebesgue` and
  `TauCeti.Probability.gueMeasure_eq_withDensity_hermitianLebesgue`: the exact coordinate Lebesgue
  densities, with `HasPDF` and `pdf` bridges `hasPDF_of_hasLaw_goeMeasure`,
  `pdf_eq_goePDF_of_hasLaw_goeMeasure`, `hasPDF_of_hasLaw_gueMeasure`, and
  `pdf_eq_guePDF_of_hasLaw_gueMeasure`.
* `TauCeti.Probability.hasLaw_goeMeasure_iff_iIndepFun`,
  `TauCeti.Probability.goe_iIndepFun_iff_withDensity`,
  `TauCeti.Probability.hasLaw_gueMeasure_iff_iIndepFun`, and
  `TauCeti.Probability.gue_iIndepFun_iff_withDensity`: equivalence of the entry and
  invariant-density characterizations.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5, (2.5.1), p. 52.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012), §2.6.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory Real
open scoped ENNReal NNReal ComplexConjugate RealInnerProductSpace

namespace TauCeti.Probability

/-! ### Exact trace densities on the self-adjoint spaces -/

/-- The real-valued **GOE density** on the `n × n` real symmetric subspace with respect to
`TauCeti.symmetricLebesgue n`:
`2 ^ (-n / 2) * (2 * π / n) ^ (-n * (n + 1) / 4) * exp (-n / 4 * tr (A²))` (AGZ (2.5.1), p. 52,
rescaled by `√n`). -/
def goePDFReal (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
    Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace)

theorem goePDFReal_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n A =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace) :=
  (rfl)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.goePDFReal`. -/
def goePDF (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (goePDFReal n A)

theorem goePDF_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n A = ENNReal.ofReal (goePDFReal n A) :=
  (rfl)

/-- The real-valued **GUE density** on the `n × n` complex Hermitian subspace with respect to
`TauCeti.hermitianLebesgue n`:
`2 ^ (-n / 2) * (π / n) ^ (-n² / 2) * exp (-n / 2 * Re tr (A²))`. -/
def guePDFReal (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * (π / n) ^ (-(n : ℝ) ^ 2 / 2) *
    Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re)

theorem guePDFReal_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n A =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * (π / n) ^ (-(n : ℝ) ^ 2 / 2) *
        Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re) :=
  (rfl)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.guePDFReal`. -/
def guePDF (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (guePDFReal n A)

theorem guePDF_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n A = ENNReal.ofReal (guePDFReal n A) :=
  (rfl)

theorem goePDFReal_pos (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDFReal n A := by
  unfold goePDFReal
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · positivity

theorem goePDFReal_nonneg (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ goePDFReal n A :=
  (goePDFReal_pos n A).le

theorem guePDFReal_pos (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDFReal n A := by
  unfold guePDFReal
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · positivity

theorem guePDFReal_nonneg (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 ≤ guePDFReal n A :=
  (guePDFReal_pos n A).le

@[fun_prop]
theorem continuous_goePDFReal (n : ℕ) : Continuous (goePDFReal n) := by
  have : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace := by
    simp only [← selfAdjoint.inner_eq_trace_mul]; exact continuous_id.inner continuous_id
  unfold goePDFReal; fun_prop

@[fun_prop]
theorem measurable_goePDFReal (n : ℕ) : Measurable (goePDFReal n) :=
  (continuous_goePDFReal n).measurable

@[fun_prop]
theorem measurable_goePDF (n : ℕ) : Measurable (goePDF n) :=
  (measurable_goePDFReal n).ennreal_ofReal

@[fun_prop]
theorem continuous_guePDFReal (n : ℕ) : Continuous (guePDFReal n) := by
  have : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
      ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re := by
    simp only [← selfAdjoint.norm_sq_eq_re_trace_mul_self]; fun_prop
  unfold guePDFReal; fun_prop

@[fun_prop]
theorem measurable_guePDFReal (n : ℕ) : Measurable (guePDFReal n) :=
  (continuous_guePDFReal n).measurable

@[fun_prop]
theorem measurable_guePDF (n : ℕ) : Measurable (guePDF n) :=
  (measurable_guePDFReal n).ennreal_ofReal

/-- `goePDFReal` is invariant under orthogonal conjugation. -/
@[simp]
theorem goePDFReal_symmetricConj {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n (Matrix.UnitaryGroup.symmetricConj O A) = goePDFReal n A := by
  simp only [goePDFReal, Matrix.UnitaryGroup.trace_mul_self_symmetricConj_apply]

@[simp]
theorem goePDF_symmetricConj {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n (Matrix.UnitaryGroup.symmetricConj O A) = goePDF n A := by
  simp only [goePDF, goePDFReal_symmetricConj]

/-- `guePDFReal` is invariant under unitary conjugation. -/
@[simp]
theorem guePDFReal_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n (Matrix.UnitaryGroup.hermitianConj U A) = guePDFReal n A := by
  simp only [guePDFReal, Matrix.UnitaryGroup.re_trace_mul_self_hermitianConj_apply]

@[simp]
theorem guePDF_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n (Matrix.UnitaryGroup.hermitianConj U A) = guePDF n A := by
  simp only [guePDF, guePDFReal_hermitianConj]

private theorem map_smul_stdGaussian_eq_withDensity_volume (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {c : ℝ} (hc : 0 < c) :
    (stdGaussian E).map (fun A ↦ c • A) =
      (volume : Measure E).withDensity fun A ↦ ENNReal.ofReal
        (|(c ^ Module.finrank ℝ E)⁻¹| * (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-‖c⁻¹ • A‖ ^ 2 / 2)) := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have hfun : (fun A : E ↦ c • A) = fun A ↦ 0 + L A := funext fun _ ↦ by simp [L, Units.smul_def]
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) = c ^ Module.finrank ℝ E := by
    rw [show (L : E →ₗ[ℝ] E) = c • LinearMap.id by ext; simp [L, Units.smul_def],
      LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [stdGaussian_eq_withDensity_norm E, hfun, Measure.map_affine_withDensity volume L 0, hdet]
  refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
  dsimp only
  have hsymm : L.symm (A - 0) = c⁻¹ • A :=
    L.symm_apply_eq.2 (by simp [L, Units.smul_def, smul_smul, inv_mul_cancel₀ hc.ne'])
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, hsymm]

private theorem two_mul_finrank_symmetricMatrix (n : ℕ) :
    2 * (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) := by
  rw [finrank_symmetricMatrix]
  exact_mod_cast Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

/-- `goeMeasure n` has density `(4 * π / n) ^ (-n * (n + 1) / 4) * exp (-n / 4 * tr (A²))` with
respect to the Frobenius `volume` on the real symmetric subspace. -/
theorem goeMeasure_eq_withDensity_volume (n : ℕ) :
    goeMeasure n =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).withDensity
        fun A ↦ ENNReal.ofReal
          ((4 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
            Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hvol : (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ))) =
        Measure.dirac 0 := by
      rw [volume_symmetricMatrix_eq_smul_symmetricLebesgue 0, symmetricLebesgue_zero]; simp
    rw [goeMeasure_zero, hvol]; push_cast
    rw [show (fun A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) ↦ ENNReal.ofReal
      ((4 * π / (0 : ℝ)) ^ (-((0 : ℝ) * ((0 : ℝ) + 1)) / 4) *
        Real.exp (-(0 : ℝ) / 4 * ((A : Matrix (Fin 0) (Fin 0) ℝ) * A).trace))) = 1 from
      funext fun _ ↦ by simp, withDensity_one]
  · set E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
    rw [goeMeasure_eq_map_stdGaussian,
      map_smul_stdGaussian_eq_withDensity_volume E (by positivity)]
    refine withDensity_congr_ae (.of_forall fun A ↦ congrArg ENNReal.ofReal ?_)
    have hnorm : ‖(Real.sqrt (2 / n))⁻¹ • A‖ ^ 2 =
        (n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / n), inv_div,
        ← real_inner_self_eq_norm_sq, selfAdjoint.inner_eq_trace_mul]
    have hcd : |((Real.sqrt (2 / n)) ^ Module.finrank ℝ E)⁻¹| *
        (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
        (4 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
      rw [abs_of_pos (by positivity), ← inv_pow, Real.sqrt_eq_rpow,
        ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 / n),
        ← Real.rpow_natCast _ (Module.finrank ℝ E),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / n),
        show -(1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) = -((n : ℝ) * ((n : ℝ) + 1)) / 4 by
          linarith [two_mul_finrank_symmetricMatrix n],
        show -(Module.finrank ℝ E : ℝ) / 2 = -((n : ℝ) * ((n : ℝ) + 1)) / 4 by
          linarith [two_mul_finrank_symmetricMatrix n],
        ← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / n) (by positivity : (0 : ℝ) ≤ 2 * π)]
      congr 1; ring
    rw [hnorm, hcd]; congr 2; ring

/-- **Density of the GOE on the real symmetric subspace** (AGZ (2.5.1), p. 52). `goeMeasure n` is
`TauCeti.symmetricLebesgue n` weighted by `TauCeti.Probability.goePDF n`. -/
theorem goeMeasure_eq_withDensity_symmetricLebesgue (n : ℕ) :
    goeMeasure n = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_volume n, volume_symmetricMatrix_eq_smul_symmetricLebesgue n,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, goePDF, goePDFReal]
  rw [show Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 4) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) from rfl, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (4 * π / (n : ℝ)) = 2 * (2 * π / n) by ring, Real.mul_rpow (by norm_num) (by positivity),
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  congr 2; congr 1; ring

/-- The Radon–Nikodym derivative of `goeMeasure n` with respect to `symmetricLebesgue n` is
`goePDF n`. -/
theorem rnDeriv_goeMeasure_symmetricLebesgue (n : ℕ) :
    (goeMeasure n).rnDeriv (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_goePDF n)

/-- A random real symmetric matrix with law `goeMeasure n` has a density with respect to
`TauCeti.symmetricLebesgue n`. -/
theorem hasPDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) : HasPDF H P (symmetricLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue n])

/-- The density of a GOE random matrix with respect to `TauCeti.symmetricLebesgue n` is
`TauCeti.Probability.goePDF n`. -/
theorem pdf_eq_goePDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) :
    pdf H P (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue n])

/-- `gueMeasure n` has density `(2 * π / n) ^ (-n² / 2) * exp (-n / 2 * Re tr (A²))` with respect
to the Frobenius `volume` on the complex Hermitian subspace. -/
theorem gueMeasure_eq_withDensity_volume (n : ℕ) :
    gueMeasure n =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).withDensity
        fun A ↦ ENNReal.ofReal
          ((2 * π / n) ^ (-(n : ℝ) ^ 2 / 2) *
            Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hvol : (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ))) =
        Measure.dirac 0 := by
      rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue 0, hermitianLebesgue_zero]; simp
    rw [gueMeasure_zero, hvol]; push_cast
    rw [show (fun A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ) ↦ ENNReal.ofReal
      ((2 * π / (0 : ℝ)) ^ (-(0 : ℝ) ^ 2 / 2) *
        Real.exp (-(0 : ℝ) / 2 * ((A : Matrix (Fin 0) (Fin 0) ℂ) * A).trace.re))) = 1 from
      funext fun _ ↦ by simp, withDensity_one]
  · set E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)
    rw [gueMeasure_eq_map_stdGaussian,
      map_smul_stdGaussian_eq_withDensity_volume E (by positivity)]
    refine withDensity_congr_ae (.of_forall fun A ↦ congrArg ENNReal.ofReal ?_)
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hnorm : ‖((Real.sqrt n)⁻¹)⁻¹ • A‖ ^ 2 =
        (n : ℝ) * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_inv,
        Real.sq_sqrt (Nat.cast_nonneg n), selfAdjoint.norm_sq_eq_re_trace_mul_self]
    have hcd : |(((Real.sqrt n)⁻¹) ^ Module.finrank ℝ E)⁻¹| *
        (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
        (2 * π / n) ^ (-(n : ℝ) ^ 2 / 2) := by
      rw [abs_of_pos (by positivity), ← inv_pow, inv_inv, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast _ (Module.finrank ℝ E), ← Real.rpow_mul hn0.le,
        finrank_hermitianMatrix]
      push_cast
      rw [show (1 / 2 : ℝ) * (n : ℝ) ^ 2 = -(-(n : ℝ) ^ 2 / 2) by ring, Real.rpow_neg hn0.le,
        ← Real.inv_rpow hn0.le, ← Real.mul_rpow (inv_nonneg.2 hn0.le) (by positivity)]
      congr 1; ring
    rw [hnorm, hcd]; congr 2; ring

/-- **Density of the GUE on the complex Hermitian subspace.** `gueMeasure n` is
`TauCeti.hermitianLebesgue n` weighted by `TauCeti.Probability.guePDF n`. -/
theorem gueMeasure_eq_withDensity_hermitianLebesgue (n : ℕ) :
    gueMeasure n = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_volume n, volume_hermitianMatrix_eq_smul_hermitianLebesgue n,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, guePDF, guePDFReal]
  rw [show Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 2) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) from rfl, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (2 * π / (n : ℝ)) = 2 * (π / n) by ring, Real.mul_rpow (by norm_num) (by positivity),
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  congr 2; congr 1; ring

/-- The Radon–Nikodym derivative of `gueMeasure n` with respect to `hermitianLebesgue n` is
`guePDF n`. -/
theorem rnDeriv_gueMeasure_hermitianLebesgue (n : ℕ) :
    (gueMeasure n).rnDeriv (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_guePDF n)

/-- A random complex Hermitian matrix with law `gueMeasure n` has a density with respect to
`TauCeti.hermitianLebesgue n`. -/
theorem hasPDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) : HasPDF H P (hermitianLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue n])

/-- The density of a GUE random matrix with respect to `TauCeti.hermitianLebesgue n` is
`TauCeti.Probability.guePDF n`. -/
theorem pdf_eq_guePDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    pdf H P (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue n])

/-! ### Equivalence of the entry and invariant-density characterizations -/

section Characterizations

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private theorem hasLaw_iff_iIndepFun_of_map_eq {E ι : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    {μ : Measure E} {ν : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (ν i)]
    (e : E ≃L[ℝ] (ι → ℝ)) (hμ : μ.map e = Measure.pi ν) [IsProbabilityMeasure P] {H : Ω → E} :
    HasLaw H μ P ↔
      iIndepFun (fun i ω ↦ e (H ω) i) P ∧ ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := by
  have he : HasLaw H μ P ↔ HasLaw (fun ω ↦ e (H ω)) (Measure.pi ν) P := by
    rw [← hμ]
    refine ⟨fun h ↦ HasLaw.comp ⟨e.continuous.aemeasurable, rfl⟩ h, fun h ↦ ?_⟩
    have hinv : HasLaw e.symm μ (μ.map e) := ⟨e.symm.continuous.aemeasurable, by
      rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]; simp⟩
    simpa [Function.comp_def] using hinv.comp h
  rw [he]
  refine ⟨fun h ↦ ?_, fun ⟨hind, hc⟩ ↦ hind.hasLaw_pi hc⟩
  have hc : ∀ i, HasLaw (fun ω ↦ e (H ω) i) (ν i) P := fun i ↦
    HasLaw.comp ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval ν i).map_eq⟩ h
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hc).2 h, hc⟩

/-- **Independent-Gaussian entry characterization of the GOE.** A random real symmetric matrix `H`
on a probability space `(Ω, P)` has law `goeMeasure n` if and only if its on-or-above-diagonal
entries are mutually independent centred Gaussians of variance `2 / n` on the diagonal and `1 / n`
above the diagonal. -/
theorem hasLaw_goeMeasure_iff_iIndepFun [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
        (∀ i : Fin n,
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i) (gaussianReal 0 (2 / n)) P) ∧
        (∀ i j : Fin n, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j) (gaussianReal 0 (1 / n)) P) := by
  rw [hasLaw_iff_iIndepFun_of_map_eq (symmetricCoordinates n)
    (map_symmetricCoordinates_goeMeasure n)]
  simp only [symmetricCoordinates_apply]
  refine and_congr_right' ⟨fun hc ↦ ⟨fun i ↦ by simpa using hc ⟨(i, i), le_rfl⟩,
      fun i j hij ↦ by simpa [hij.ne] using hc ⟨(i, j), hij.le⟩⟩,
    fun ⟨hdiag, hoff⟩ ⟨⟨i, j⟩, hij⟩ ↦ ?_⟩
  rcases (show i ≤ j from hij).eq_or_lt with rfl | hlt
  · simpa using hdiag i
  · simpa [hlt.ne] using hoff i j hlt

/-- **Invariant-density characterization of the GOE.** `H` has law `goeMeasure n` if and only if
`H` is `P`-almost-everywhere measurable and `P.map H` is `symmetricLebesgue n` weighted by
`goePDF n`. -/
theorem hasLaw_goeMeasure_iff_withDensity {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      AEMeasurable H P ∧ P.map H = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue n]
  exact ⟨fun h ↦ ⟨h.aemeasurable, h.map_eq⟩, fun ⟨hm, heq⟩ ↦ ⟨hm, heq⟩⟩

/-- **Equivalence of the entry and invariant-density characterizations of the GOE**
(AGZ (2.5.1), p. 52). On a probability space `(Ω, P)`, the independent-Gaussian entry conditions on
a real symmetric random matrix `H` hold if and only if `H` is `P`-almost-everywhere measurable with
law `(symmetricLebesgue n).withDensity (goePDF n)`. -/
theorem goe_iIndepFun_iff_withDensity [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    (iIndepFun (fun (ij : upperTriangle n) ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
      (∀ i : Fin n,
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i) (gaussianReal 0 (2 / n)) P) ∧
      (∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j) (gaussianReal 0 (1 / n)) P)) ↔
      (AEMeasurable H P ∧ P.map H = (symmetricLebesgue n).withDensity (goePDF n)) := by
  rw [← hasLaw_goeMeasure_iff_iIndepFun, hasLaw_goeMeasure_iff_withDensity]

/-- **Independent-Gaussian coordinate characterization of the GUE.** A random complex Hermitian
matrix `H` on a probability space `(Ω, P)` has law `gueMeasure n` if and only if its `n²` real
coordinates `hermitianCoordinates n ∘ H` are mutually independent with diagonal real parts
`N(0, 1 / n)` and strictly upper-triangular real and imaginary parts `N(0, 1 / (2 * n))`. -/
theorem hasLaw_gueMeasure_iff_iIndepFun [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      iIndepFun (fun (ab : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ab) P ∧
        (∀ i : Fin n,
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
            (gaussianReal 0 (1 / n)) P) ∧
        (∀ i j : Fin n, i < j →
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
            (gaussianReal 0 (1 / (2 * n))) P ∧
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
            (gaussianReal 0 (1 / (2 * n))) P) := by
  rw [hasLaw_iff_iIndepFun_of_map_eq (hermitianCoordinates n)
    (map_hermitianCoordinates_gueMeasure n)]
  refine and_congr_right' ⟨fun hc ↦ ⟨?_, ?_⟩, fun ⟨hdiag, hoff⟩ ⟨i, j⟩ ↦ ?_⟩
  · intro i
    simpa [hermitianCoordinates_apply_self] using hc (i, i)
  · intro i j hij
    exact ⟨by simpa [hermitianCoordinates_apply_of_le n _ hij.le, hij.ne] using hc (i, j),
      by simpa [hermitianCoordinates_apply_of_gt n _ hij, hij.ne'] using hc (j, i)⟩
  · rcases lt_trichotomy i j with hij | rfl | hji
    · simpa [hermitianCoordinates_apply_of_le n _ hij.le, hij.ne] using (hoff i j hij).1
    · simpa [hermitianCoordinates_apply_self] using hdiag i
    · simpa [hermitianCoordinates_apply_of_gt n _ hji, hji.ne'] using (hoff j i hji).2

/-- **Invariant-density characterization of the GUE.** `H` has law `gueMeasure n` if and only if
`H` is `P`-almost-everywhere measurable and `P.map H` is `hermitianLebesgue n` weighted by
`guePDF n`. -/
theorem hasLaw_gueMeasure_iff_withDensity {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      AEMeasurable H P ∧ P.map H = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue n]
  exact ⟨fun h ↦ ⟨h.aemeasurable, h.map_eq⟩, fun ⟨hm, heq⟩ ↦ ⟨hm, heq⟩⟩

/-- **Equivalence of the entry and invariant-density characterizations of the GUE.** On a
probability space `(Ω, P)`, the independent-Gaussian real and imaginary coordinate conditions on a
complex Hermitian random matrix `H` hold if and only if `H` is `P`-almost-everywhere measurable with
law `(hermitianLebesgue n).withDensity (guePDF n)`. -/
theorem gue_iIndepFun_iff_withDensity [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    (iIndepFun (fun (ab : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ab) P ∧
      (∀ i : Fin n,
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P) ∧
      (∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
          (gaussianReal 0 (1 / (2 * n))) P ∧
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
          (gaussianReal 0 (1 / (2 * n))) P)) ↔
      (AEMeasurable H P ∧ P.map H = (hermitianLebesgue n).withDensity (guePDF n)) := by
  rw [← hasLaw_gueMeasure_iff_iIndepFun, hasLaw_gueMeasure_iff_withDensity]

end Characterizations

end TauCeti.Probability
