/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Determinant
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Determinant moments of the LKJ law

For an LKJ correlation matrix of positive shape `η`, a real determinant power `q` is
integrable in dimensions at least two exactly when `-η < q`. On this sharp domain its
expectation is the ratio of LKJ normalizing constants

`lkjNormalizer p (η + q) / lkjNormalizer p η`.

The value follows directly by multiplying the LKJ density by the determinant power, which shifts
its exponent from `η - 1` to `η + q - 1`. For sharpness, the determinant pushforward of the
LKJ law is identified with the determinant pushforward of the independent centered-Beta partial
correlation construction. This one-dimensional identification uses compact moment determinacy on
`[0, 1]`; it does not require identification of the full matrix laws. The construction's exact
integrability threshold then detects divergence at and below the endpoint.

In dimensions zero and one, the LKJ law is concentrated at the identity and every determinant
power is constantly one.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η q : ℝ}

private abbrev lkjCoordinateLaw (p : ℕ) (η : ℝ) (ij : strictLowerTriangle p) : Measure ℝ :=
  (betaMeasure (lkjPartialCorrelationShape p η ij)
    (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)

private abbrev lkjCoordinateProduct (p : ℕ) (η : ℝ) :
    Measure (strictLowerTriangle p → ℝ) :=
  Measure.pi (lkjCoordinateLaw p η)

private theorem prod_beta_lkjPartialCorrelationShape (p : ℕ) (η : ℝ) :
    (∏ ij : strictLowerTriangle p, beta (1 / 2) (lkjPartialCorrelationShape p η ij)) =
      lkjNormalizer p η := by
  simp_rw [lkjPartialCorrelationShape_def]
  rw [← Fintype.prod_fiberwise'
    (fun ij : strictLowerTriangle p ↦ ij.1.2)
    (fun j : Fin p ↦ beta (1 / 2)
      (η + (((p - 1 - j.val : ℕ) : ℝ) - 1) / 2))]
  simp_rw [Finset.prod_const, Finset.card_univ, card_strictLowerTriangle_column]
  calc
    _ = ∏ k ∈ Finset.range p,
        beta (1 / 2) (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^ (p - 1 - k) := by
      simpa only using Fin.prod_univ_eq_prod_range
        (fun k : ℕ ↦ beta (1 / 2)
          (η + (((p - 1 - k : ℕ) : ℝ) - 1) / 2) ^ (p - 1 - k)) p
    _ = lkjNormalizer p η := by
      rw [lkjNormalizer_eq_prod_columns]
      rcases p with _ | p
      · simp
      · rw [Finset.prod_range_succ]
        simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, zero_sub, pow_zero, mul_one]
        rw [Finset.prod_Ico_eq_prod_range]
        congr 1
        ext k
        have h : p + 1 - (1 + k) = p - k := by omega
        rw [h]

private theorem prod_beta_ratio_lkjPartialCorrelationShape (p : ℕ) (η q : ℝ) :
    (∏ ij : strictLowerTriangle p,
        beta (1 / 2) (lkjPartialCorrelationShape p η ij + q) /
          beta (1 / 2) (lkjPartialCorrelationShape p η ij)) =
      lkjNormalizer p (η + q) / lkjNormalizer p η := by
  rw [Finset.prod_div_distrib, prod_beta_lkjPartialCorrelationShape]
  have hshape (ij : strictLowerTriangle p) :
      lkjPartialCorrelationShape p η ij + q =
        lkjPartialCorrelationShape p (η + q) ij := by
    simp only [lkjPartialCorrelationShape_def]
    ring
  simp_rw [hshape, prod_beta_lkjPartialCorrelationShape]

private theorem det_mem_Ioc_of_posDef_of_diag_eq_one
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef)
    (hdiag : ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1) :
    (R : Matrix (Fin p) (Fin p) ℝ).det ∈ Set.Ioc 0 1 := by
  let x := correlationCoordinates p R
  have hx : x ∈ posDefCorrelationRegion p := by
    rw [mem_posDefCorrelationRegion, correlationMatrix_correlationCoordinates hdiag]
    exact hR
  let z := partialCorrelationOfCorrelationCoordinates x
  have hz : ∀ ij, |z ij| < 1 := mapsTo_partialCorrelationOfCorrelationCoordinates hx
  have hmatrix : (R : Matrix (Fin p) (Fin p) ℝ) = partialCorrelationGram z := by
    rw [← coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation
      (fun ij ↦ (hz ij).le),
      correlationCoordinatesOfPartialCorrelation_partialCorrelationOfCorrelationCoordinates hx,
      correlationMatrix_correlationCoordinates hdiag]
  rw [hmatrix, det_partialCorrelationGram (fun ij ↦ (hz ij).le)]
  constructor
  · exact Finset.prod_pos fun ij _ ↦ sub_pos.mpr
      ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  · exact Finset.prod_le_one₀
      (fun ij _ ↦ sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij).le))
      (fun ij _ ↦ by nlinarith [sq_nonneg (z ij)])

private theorem map_det_lkjMeasure_compl_Icc :
    (lkjMeasure p η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det) (Set.Icc 0 1)ᶜ = 0 := by
  rw [← mem_ae_iff, mem_ae_map_iff (by fun_prop) measurableSet_Icc]
  filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hdiag
  have hdet := det_mem_Ioc_of_posDef_of_diag_eq_one hR hdiag
  exact ⟨hdet.1.le, hdet.2⟩

private theorem map_det_partialCorrelationGram_compl_Icc (hη : 0 < η) :
    (lkjCoordinateProduct p η).map
        (fun z ↦ (partialCorrelationGram z).det) (Set.Icc 0 1)ᶜ = 0 := by
  rw [← mem_ae_iff, mem_ae_map_iff (by fun_prop) measurableSet_Icc]
  filter_upwards [ae_abs_le_one_pi_centered_betaMeasure
    (fun ij : strictLowerTriangle p ↦ lkjPartialCorrelationShape_pos hη ij)] with z hz
  change (partialCorrelationGram z).det ∈ Set.Icc 0 1
  rw [det_partialCorrelationGram hz]
  constructor
  · exact Finset.prod_nonneg fun ij _ ↦
      sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij))
  · exact Finset.prod_le_one₀
      (fun ij _ ↦ sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij)))
      (fun ij _ ↦ by nlinarith [sq_nonneg (z ij)])

/-- **Determinant moments of the LKJ law.** If `η > 0` and `q > -η`, then the expectation of
`det R ^ q` is the ratio of the LKJ normalizers at the shifted and original shapes. This includes
dimensions zero and one. -/
theorem integral_rpow_det_lkjMeasure (hη : 0 < η) (hq : -η < q) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ q ∂lkjMeasure p η =
      lkjNormalizer p (η + q) / lkjNormalizer p η := by
  rw [lkjMeasure_of_pos hη,
    show lkjPDF p η = fun R ↦ ENNReal.ofReal (lkjPDFReal p η R) by
      funext R
      rw [lkjPDF_def],
    TauCeti.Probability.integral_withDensity_ofReal
      (measurable_lkjPDFReal p η).aemeasurable (ae_of_all _ (lkjPDFReal_nonneg hη))]
  rw [lkjPDFReal_eq_indicator]
  simp only [smul_eq_mul]
  rw [show (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
          (fun A ↦ (A : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
            lkjNormalizer p η) R * (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
          (fun R ↦ ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) /
            lkjNormalizer p η) * (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) by
        funext R
        rw [Set.indicator_mul_left]]
  rw [integral_indicator (measurableSet_posDefMatrix p)]
  have hcombine : ∀ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef →
        ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η) *
            (R : Matrix (Fin p) (Fin p) ℝ).det ^ q =
          (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η + q - 1) /
            lkjNormalizer p η := by
    intro R hR
    rw [div_mul_eq_mul_div, ← Real.rpow_add hR.det_pos]
    congr 2
    ring
  rw [setIntegral_congr_fun (measurableSet_posDefMatrix p) hcombine, integral_div,
    setIntegral_rpow_det_correlationLebesgue p (by linarith),
    div_eq_mul_inv]

private theorem map_det_lkjMeasure_eq_map_det_partialCorrelationGram (hη : 0 < η) :
    (lkjMeasure p η).map
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det) =
      (lkjCoordinateProduct p η).map (fun z ↦ (partialCorrelationGram z).det) := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  let _ (ij : strictLowerTriangle p) :=
    isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
  apply Measure.ext_of_forall_integral_pow_eq_of_support isCompact_Icc
    map_det_lkjMeasure_compl_Icc (map_det_partialCorrelationGram_compl_Icc hη)
  intro n
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  have hlkj := integral_rpow_det_lkjMeasure (p := p) hη
    (q := (n : ℝ)) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hconstruction := integral_rpow_det_partialCorrelationGram_pi_betaMeasure
    (a := fun ij : strictLowerTriangle p ↦ lkjPartialCorrelationShape p η ij)
    (q := (n : ℝ)) (fun ij ↦ lkjPartialCorrelationShape_pos hη ij)
    (fun ij ↦ by have := lkjPartialCorrelationShape_pos hη ij; positivity)
  rw [prod_beta_ratio_lkjPartialCorrelationShape] at hconstruction
  simpa only [Function.comp_apply, Real.rpow_natCast, lkjCoordinateProduct,
    lkjCoordinateLaw] using hlkj.trans hconstruction.symm

/-- **Sharp determinant-power integrability for the LKJ law.** In dimension at least two and at
positive shape `η`, `det R ^ q` is integrable exactly for `q > -η`. Equality at the endpoint is
on the divergent side. -/
@[simp]
theorem integrable_rpow_det_lkjMeasure_iff (hp : 2 ≤ p) (hη : 0 < η) (q : ℝ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) (lkjMeasure p η) ↔ -η < q := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  let _ (ij : strictLowerTriangle p) :=
    isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
  change Integrable ((fun x : ℝ ↦ x ^ q) ∘
      fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ).det) (lkjMeasure p η) ↔ -η < q
  rw [← (integrable_map_measure (g := fun x : ℝ ↦ x ^ q) (by fun_prop)
      (by fun_prop : AEMeasurable
        (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (R : Matrix (Fin p) (Fin p) ℝ).det) (lkjMeasure p η))),
    map_det_lkjMeasure_eq_map_det_partialCorrelationGram hη,
    integrable_map_measure (g := fun x : ℝ ↦ x ^ q) (by fun_prop)
      (by fun_prop : AEMeasurable (fun z ↦ (partialCorrelationGram z).det)
        (lkjCoordinateProduct p η))]
  change Integrable (fun z ↦ (partialCorrelationGram z).det ^ q)
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) ↔ -η < q
  rw [integrable_rpow_det_partialCorrelationGram_pi_betaMeasure_iff
    (fun ij ↦ lkjPartialCorrelationShape_pos hη ij)]
  constructor
  · intro h
    let ij : strictLowerTriangle p :=
      ⟨(⟨p - 1, by omega⟩, ⟨p - 2, by omega⟩), by simp only [Fin.lt_def]; omega⟩
    have hlast := h ij
    have hsub : p - 1 - ij.1.2.val = 1 := by
      dsimp [ij]
      omega
    rw [lkjPartialCorrelationShape_def, hsub] at hlast
    norm_num at hlast
    linarith
  · intro hq ij
    have hcol : 1 ≤ p - 1 - ij.1.2.val := by
      have := ij.2
      have := ij.1.1.isLt
      omega
    rw [lkjPartialCorrelationShape_def]
    have hcol' : (1 : ℝ) ≤ (p - 1 - ij.1.2.val : ℕ) := by exact_mod_cast hcol
    linarith

/-- In dimensions zero and one, every determinant power under the positive-shape LKJ law is
integrable. -/
theorem integrable_rpow_det_lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) (q : ℝ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ q) (lkjMeasure p η) := by
  rw [lkjMeasure_of_le_one hp hη]
  exact integrable_dirac (by simp)

/-- In dimensions zero and one, every real determinant-power moment under a positive-shape LKJ
law equals one. -/
theorem integral_rpow_det_lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) (q : ℝ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ q ∂lkjMeasure p η = 1 := by
  rw [lkjMeasure_of_le_one hp hη, integral_dirac]
  simp

end TauCeti.Probability
