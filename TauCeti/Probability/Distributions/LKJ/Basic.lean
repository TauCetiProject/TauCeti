/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral
public import TauCeti.Probability.Density
import Mathlib.Algebra.Order.Star.Real

/-!
# The LKJ correlation-matrix family

The LKJ law of shape `η > 0` on `p × p` correlation matrices has density
`det R ^ (η - 1) / lkjNormalizer p η` with respect to
`TauCeti.correlationLebesgue p`.  The reference measure is Lebesgue measure on the affine space of
unit-diagonal symmetric matrices, rather than ambient Lebesgue measure on all symmetric matrices.
The density vanishes away from the positive-definite cone, and nonpositive shapes give the zero
measure.

This file defines the density and measure, proves their measurable and Radon--Nikodym interfaces,
and records that the law is concentrated on positive-definite unit-diagonal matrices.  At positive
shape the law is a probability measure, because the integral of the determinant power, computed in
partial-correlation coordinates, is `lkjNormalizer p η`.  At shape one the density is constant on
the positive-definite region, so the law is normalized correlation volume on that region.  In
dimensions zero and one the law is the Dirac mass at the identity.

## Main definitions

* `TauCeti.Probability.lkjPDFReal` and `TauCeti.Probability.lkjPDF` are the real- and
  `ℝ≥0∞`-valued densities with respect to `TauCeti.correlationLebesgue`.
* `TauCeti.Probability.lkjMeasure` is the LKJ measure, totalized to zero at nonpositive shape.

## Main results

* `TauCeti.Probability.lkjMeasure_of_pos` and
  `TauCeti.Probability.lkjMeasure_of_nonpos` describe the valid and invalid branches.
* `TauCeti.Probability.isProbabilityMeasure_lkjMeasure` proves normalization at positive shape.
* `TauCeti.Probability.lkjMeasure_shape_one` identifies the shape-one law with conditioned
  correlation volume.
* `TauCeti.Probability.ae_posDef_lkjMeasure` and
  `TauCeti.Probability.ae_diag_eq_one_lkjMeasure` give the almost-sure carrier properties.
* `TauCeti.Probability.hasPDF_of_hasLaw_lkjMeasure` and
  `TauCeti.Probability.rnDeriv_lkjMeasure` give the density interfaces.
* `TauCeti.Probability.measurable_lkjMeasure` proves parameter measurability.
* `TauCeti.Probability.lkjMeasure_of_le_one` identifies the zero- and one-dimensional laws.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-! ### The density -/

open Classical in
/-- The real-valued LKJ density of shape `η` on `p × p` symmetric matrices, with respect to
`TauCeti.correlationLebesgue p`.  On the positive-definite cone it is
`det R ^ (η - 1) / lkjNormalizer p η`, and it vanishes off that cone.

The formula is total in `η`, but it describes the LKJ law only when `0 < η`. -/
def lkjPDFReal (p : ℕ) (η : ℝ)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ :=
  if (R : Matrix (Fin p) (Fin p) ℝ).PosDef then
    (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η
  else 0

open Classical in
/-- The defining branch expression of the real-valued LKJ density. -/
theorem lkjPDFReal_def (p : ℕ) (η : ℝ)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDFReal p η R =
      if (R : Matrix (Fin p) (Fin p) ℝ).PosDef then
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η
      else 0 :=
  (rfl)

/-- On the positive-definite cone the real-valued LKJ density is its determinant-power formula. -/
@[simp]
theorem lkjPDFReal_of_posDef (p : ℕ) (η : ℝ)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDFReal p η R =
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η := by
  classical
  rw [lkjPDFReal, ite_eq_left hR]

/-- Off the positive-definite cone the real-valued LKJ density vanishes. -/
@[simp]
theorem lkjPDFReal_of_not_posDef (p : ℕ) (η : ℝ)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : ¬ (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDFReal p η R = 0 := by
  classical
  rw [lkjPDFReal, ite_eq_right hR]

/-- At positive shape the real-valued LKJ density is nonnegative. -/
theorem lkjPDFReal_nonneg (hη : 0 < η)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    0 ≤ lkjPDFReal p η R := by
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [lkjPDFReal_of_posDef p η hR]
    exact div_nonneg (Real.rpow_nonneg hR.det_pos.le _) (lkjNormalizer_pos hη).le
  · simp [hR]

/-- At positive shape the real-valued LKJ density is positive exactly on the positive-definite
cone. -/
@[simp]
theorem lkjPDFReal_pos_iff (hη : 0 < η)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < lkjPDFReal p η R ↔ (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  refine ⟨fun h ↦ ?_, fun hR ↦ ?_⟩
  · by_contra hR
    simp [hR] at h
  · rw [lkjPDFReal_of_posDef p η hR]
    exact div_pos (Real.rpow_pos_of_pos hR.det_pos _) (lkjNormalizer_pos hη)

/-- The `ℝ≥0∞`-valued LKJ density, used to define the measure. -/
def lkjPDF (p : ℕ) (η : ℝ)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (lkjPDFReal p η R)

/-- The `ℝ≥0∞`-valued LKJ density is `ENNReal.ofReal` of the real-valued density. -/
theorem lkjPDF_def (p : ℕ) (η : ℝ)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η R = ENNReal.ofReal (lkjPDFReal p η R) :=
  (rfl)

/-- On the positive-definite cone the `ℝ≥0∞`-valued LKJ density is its determinant-power
formula. -/
@[simp]
theorem lkjPDF_of_posDef (p : ℕ) (η : ℝ)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDF p η R = ENNReal.ofReal
      ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η) := by
  rw [lkjPDF_def, lkjPDFReal_of_posDef p η hR]

/-- Off the positive-definite cone the `ℝ≥0∞`-valued LKJ density vanishes. -/
@[simp]
theorem lkjPDF_of_not_posDef (p : ℕ) (η : ℝ)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : ¬ (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDF p η R = 0 := by
  simp [lkjPDF_def, hR]

/-- At positive shape the LKJ density is positive exactly on the positive-definite cone. -/
@[simp]
theorem lkjPDF_pos_iff (hη : 0 < η)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < lkjPDF p η R ↔ (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [lkjPDF_def, ENNReal.ofReal_pos, lkjPDFReal_pos_iff hη]

/-- The LKJ density is finite. -/
@[simp]
theorem lkjPDF_ne_top (p : ℕ) (η : ℝ)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η R ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- At positive shape the `ℝ≥0∞`-valued density recovers the real-valued one. -/
@[simp]
theorem toReal_lkjPDF (hη : 0 < η)
    (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (lkjPDF p η R).toReal = lkjPDFReal p η R :=
  ENNReal.toReal_ofReal (lkjPDFReal_nonneg hη R)

/-- The real-valued LKJ density is measurable along measurable families of shapes and symmetric
matrices. -/
private theorem measurable_lkjPDFReal_comp {γ : Type*} [MeasurableSpace γ]
    {f : γ → ℝ} {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun c ↦ lkjPDFReal p (f c) (g c) := by
  classical
  have hg' : Measurable fun c ↦ (g c : Matrix (Fin p) (Fin p) ℝ) :=
    measurable_subtype_coe.comp hg
  have hdet : Measurable fun c ↦ (g c : Matrix (Fin p) (Fin p) ℝ).det :=
    (Continuous.matrix_det continuous_id).measurable.comp hg'
  have hrpow : Measurable fun z : ℝ × ℝ ↦ z.1 ^ z.2 := by fun_prop
  simp only [lkjPDFReal]
  refine Measurable.ite (hg (measurableSet_posDefMatrix p)) ?_ measurable_const
  exact (hrpow.comp (hdet.prodMk (hf.sub measurable_const))).div
    ((measurable_lkjNormalizer p).comp hf)

/-- The `ℝ≥0∞`-valued LKJ density is measurable along measurable families of shapes and symmetric
matrices. -/
private theorem measurable_lkjPDF_comp {γ : Type*} [MeasurableSpace γ]
    {f : γ → ℝ} {g : γ → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun c ↦ lkjPDF p (f c) (g c) :=
  (measurable_lkjPDFReal_comp hf hg).ennreal_ofReal

/-- The real-valued LKJ density is measurable in the matrix. -/
@[fun_prop]
theorem measurable_lkjPDFReal (p : ℕ) (η : ℝ) : Measurable (lkjPDFReal p η) :=
  measurable_lkjPDFReal_comp measurable_const measurable_id

/-- The real-valued LKJ density is jointly measurable in the shape and matrix. -/
@[fun_prop]
theorem measurable_uncurry_lkjPDFReal (p : ℕ) :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      lkjPDFReal p q.1 q.2 :=
  measurable_lkjPDFReal_comp measurable_fst measurable_snd

/-- The `ℝ≥0∞`-valued LKJ density is measurable in the matrix. -/
@[fun_prop]
theorem measurable_lkjPDF (p : ℕ) (η : ℝ) : Measurable (lkjPDF p η) :=
  measurable_lkjPDF_comp measurable_const measurable_id

/-- The `ℝ≥0∞`-valued LKJ density is jointly measurable in the shape and matrix. -/
@[fun_prop]
theorem measurable_uncurry_lkjPDF (p : ℕ) :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      lkjPDF p q.1 q.2 :=
  measurable_lkjPDF_comp measurable_fst measurable_snd

/-! ### The measure -/

/-- The LKJ measure of shape `η` on `p × p` correlation matrices.  At positive shape it has
`TauCeti.Probability.lkjPDF p η` as its density against `TauCeti.correlationLebesgue p`;
nonpositive shapes give the zero measure. -/
def lkjMeasure (p : ℕ) (η : ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  if 0 < η then (correlationLebesgue p).withDensity (lkjPDF p η) else 0

/-- The defining branch expression of the LKJ measure. -/
theorem lkjMeasure_def (p : ℕ) (η : ℝ) :
    lkjMeasure p η =
      if 0 < η then (correlationLebesgue p).withDensity (lkjPDF p η) else 0 :=
  (rfl)

/-- At positive shape the LKJ measure is its density against correlation Lebesgue measure. -/
theorem lkjMeasure_of_pos (hη : 0 < η) :
    lkjMeasure p η = (correlationLebesgue p).withDensity (lkjPDF p η) := by
  rw [lkjMeasure, ite_eq_left hη]

/-- At nonpositive shape the LKJ measure is zero. -/
@[simp]
theorem lkjMeasure_of_nonpos (hη : η ≤ 0) : lkjMeasure p η = 0 := by
  rw [lkjMeasure, ite_eq_right (not_lt.mpr hη)]

/-- The LKJ measure gives no mass to the complement of the positive-definite cone. -/
@[simp]
theorem lkjMeasure_compl_posDef (p : ℕ) (η : ℝ) :
    lkjMeasure p η
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosDef}ᶜ = 0 := by
  by_cases hη : 0 < η
  · rw [lkjMeasure_of_pos hη,
      withDensity_apply _ (measurableSet_posDefMatrix p).compl]
    refine setLIntegral_eq_zero (measurableSet_posDefMatrix p).compl fun R hR ↦ ?_
    exact lkjPDF_of_not_posDef p η hR
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- A matrix sampled from an LKJ measure is almost surely positive definite. -/
theorem ae_posDef_lkjMeasure (p : ℕ) (η : ℝ) :
    ∀ᵐ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂lkjMeasure p η,
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [ae_iff]
  exact lkjMeasure_compl_posDef p η

/-- Including the positive-definite lift of an LKJ law returns the original law.
This also holds at nonpositive shape, when both measures vanish. -/
@[simp]
theorem map_subtype_val_comap_lkjMeasure (p : ℕ) (η : ℝ) :
    ((lkjMeasure p η).comap
        (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))).map
        Subtype.val = lkjMeasure p η :=
  (map_comap_subtype_coe (measurableSet_posDefMatrix p) _).trans
    (Measure.restrict_eq_self_of_ae_mem (ae_posDef_lkjMeasure p η))

/-- A matrix sampled from an LKJ measure has unit diagonal almost surely. -/
theorem ae_diag_eq_one_lkjMeasure (p : ℕ) (η : ℝ) :
    ∀ᵐ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂lkjMeasure p η,
      ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1 := by
  by_cases hη : 0 < η
  · rw [lkjMeasure_of_pos hη]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_correlationLebesgue_diag_eq_one p)
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-! ### Normalization -/

/-- The real-valued LKJ density is the indicator of the positive-definite cone times the
determinant-power formula. -/
theorem lkjPDFReal_eq_indicator (p : ℕ) (η : ℝ) :
    lkjPDFReal p η =
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
        fun R ↦ (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η := by
  funext R
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef <;> simp [hR]

/-- At positive shape the real-valued LKJ density is integrable against correlation Lebesgue
measure. -/
theorem integrable_lkjPDFReal (hη : 0 < η) :
    Integrable (lkjPDFReal p η) (correlationLebesgue p) := by
  rw [lkjPDFReal_eq_indicator, integrable_indicator_iff (measurableSet_posDefMatrix p)]
  exact (integrableOn_rpow_det_correlationLebesgue p hη).div_const _

/-- At positive shape the real-valued LKJ density integrates to one. -/
theorem integral_lkjPDFReal_eq_one (hη : 0 < η) :
    ∫ R, lkjPDFReal p η R ∂correlationLebesgue p = 1 := by
  rw [lkjPDFReal_eq_indicator, integral_indicator (measurableSet_posDefMatrix p), integral_div,
    setIntegral_rpow_det_correlationLebesgue p hη, div_self (lkjNormalizer_ne_zero hη)]

/-- At positive shape the `ℝ≥0∞`-valued LKJ density integrates to one. -/
theorem lintegral_lkjPDF_eq_one (hη : 0 < η) :
    ∫⁻ R, lkjPDF p η R ∂correlationLebesgue p = 1 := by
  simp_rw [lkjPDF_def]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_lkjPDFReal hη)
    (ae_of_all _ (lkjPDFReal_nonneg hη)), integral_lkjPDFReal_eq_one hη, ENNReal.ofReal_one]

/-- The LKJ law of positive shape is a probability measure. -/
theorem isProbabilityMeasure_lkjMeasure (hη : 0 < η) : IsProbabilityMeasure (lkjMeasure p η) :=
  ⟨by rw [lkjMeasure_of_pos hη, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_lkjPDF_eq_one hη]⟩

/-- At positive shape the LKJ law lifted to the positive-definite cone is a probability law. -/
theorem isProbabilityMeasure_comap_lkjMeasure (hη : 0 < η) :
    IsProbabilityMeasure ((lkjMeasure p η).comap
      (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) := by
  apply (Measure.isProbabilityMeasure_map_iff
    (f := (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)))
    measurable_subtype_coe.aemeasurable).mp
  rw [map_subtype_val_comap_lkjMeasure]
  exact isProbabilityMeasure_lkjMeasure hη

variable (p) in
/-- The positive-definite correlation matrices have correlation Lebesgue measure
`lkjNormalizer p 1`, the LKJ normalizer at shape one. -/
theorem correlationLebesgue_setOf_posDef_eq_lkjNormalizer :
    correlationLebesgue p {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosDef} =
      ENNReal.ofReal (lkjNormalizer p 1) := by
  have h := setIntegral_rpow_det_correlationLebesgue p one_pos
  simp only [sub_self, Real.rpow_zero, setIntegral_const, smul_eq_mul, mul_one] at h
  have hfin := volume_posDefCorrelationRegion_lt_top p
  rw [← correlationLebesgue_setOf_posDef] at hfin
  rw [← h, measureReal_def, ENNReal.ofReal_toReal hfin.ne]

variable (p) in
/-- At shape one the LKJ law is uniform on the positive-definite correlation matrices: it is
correlation Lebesgue measure conditioned on the positive-definite cone. -/
theorem lkjMeasure_shape_one :
    lkjMeasure p 1 = ProbabilityTheory.cond (correlationLebesgue p)
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have hZ := lkjNormalizer_pos (p := p) one_pos
  have hpdf : lkjPDF p 1 =
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
        fun _ ↦ (correlationLebesgue p {R | (R : Matrix (Fin p) (Fin p) ℝ).PosDef})⁻¹ := by
    funext R
    by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
    · simp [hR, correlationLebesgue_setOf_posDef_eq_lkjNormalizer, ENNReal.ofReal_inv_of_pos hZ]
    · simp [hR]
  rw [lkjMeasure_of_pos one_pos, hpdf, withDensity_indicator (measurableSet_posDefMatrix p),
    withDensity_const, ProbabilityTheory.cond]

/-! ### Density interfaces -/

section Density

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- A random symmetric matrix with an LKJ law has a density against
`TauCeti.correlationLebesgue`; at invalid shape the zero law trivially has one. -/
theorem hasPDF_of_hasLaw_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P) :
    HasPDF X P (correlationLebesgue p) := by
  by_cases hη : 0 < η
  · exact Probability.hasPDF_of_hasLaw_withDensity
      (measurable_lkjPDF p η).aemeasurable (by rwa [← lkjMeasure_of_pos hη])
  · refine Probability.hasPDF_of_hasLaw_withDensity (f := 0) aemeasurable_const ?_
    rwa [withDensity_zero, ← lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- At positive shape, the density of a random symmetric matrix with an LKJ law is
`TauCeti.Probability.lkjPDF`. -/
theorem pdf_eq_lkjPDF_of_hasLaw_lkjMeasure (hη : 0 < η)
    (hX : HasLaw X (lkjMeasure p η) P) :
    pdf X P (correlationLebesgue p) =ᵐ[correlationLebesgue p] lkjPDF p η :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_lkjPDF p η).aemeasurable
    (by rwa [← lkjMeasure_of_pos hη])

/-- The Radon--Nikodym derivative of a positive-shape LKJ law against correlation Lebesgue
measure is its LKJ density. -/
theorem rnDeriv_lkjMeasure (hη : 0 < η) :
    (lkjMeasure p η).rnDeriv (correlationLebesgue p) =ᵐ[correlationLebesgue p] lkjPDF p η := by
  rw [lkjMeasure_of_pos hη]
  exact Measure.rnDeriv_withDensity _ (measurable_lkjPDF p η)

end Density

/-! ### Low dimensions and parameter measurability -/

/-- In dimensions zero and one the LKJ density at the identity matrix is one. -/
theorem lkjPDF_identity_of_le_one (hp : p ≤ 1) (η : ℝ) :
    lkjPDF p η
      (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) = 1 := by
  rw [lkjPDF_of_posDef p η Matrix.PosDef.one, Matrix.det_one]
  have hn : lkjNormalizer p η = 1 := by
    have hp_cases : p = 0 ∨ p = 1 := by omega
    rcases hp_cases with rfl | rfl <;> simp
  rw [hn]
  simp

/-- At positive shape, the zero- and one-dimensional LKJ laws are the Dirac mass at the identity
matrix. -/
theorem lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) :
    lkjMeasure p η =
      Measure.dirac
        (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  rw [lkjMeasure_of_pos hη, correlationLebesgue_of_le_one hp,
    dirac_withDensity' (measurable_lkjPDF p η), lkjPDF_identity_of_le_one hp η, one_smul]

/-- In dimension zero a positive-shape LKJ law is the Dirac mass at the unique symmetric matrix. -/
theorem lkjMeasure_zero (hη : 0 < η) :
    lkjMeasure 0 η = Measure.dirac 0 := by
  rw [lkjMeasure_of_le_one (p := 0) (by omega) hη]
  exact congrArg Measure.dirac (Subsingleton.elim _ _)

/-- In dimension one a positive-shape LKJ law is the Dirac mass at the identity matrix. -/
theorem lkjMeasure_one (hη : 0 < η) :
    lkjMeasure 1 η = Measure.dirac
      (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ)) :=
  lkjMeasure_of_le_one le_rfl hη

/-- The LKJ family is measurable in its totalized real shape parameter. -/
@[fun_prop]
theorem measurable_lkjMeasure (p : ℕ) : Measurable (lkjMeasure p) := by
  have hvalid : MeasurableSet {η : ℝ | 0 < η} := measurableSet_lt measurable_const measurable_id
  unfold lkjMeasure
  exact Measurable.ite hvalid
    (measurable_withDensity (measurable_uncurry_lkjPDF p)) measurable_const

end TauCeti.Probability
