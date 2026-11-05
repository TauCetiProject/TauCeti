/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Parameter measurability of truncated normal distributions

The truncated normal law depends measurably on its mean and variance for every fixed measurable
truncation set. It also depends measurably on moving interval endpoints. All statements use the
totalized definition of `truncatedNormalMeasure`: an interval of zero Gaussian mass gives the zero
measure, including at zero variance and for reversed or coincident endpoints.

Both real endpoints and extended-real endpoints are covered. The latter are expressed through
`Real.toEReal` so that infinite one-sided truncations belong to the same measurable family.

Truncation events may also vary through any measurable incidence set. The named real and
extended densities are jointly measurable in these events, the Gaussian parameters and the
evaluation point. At zero variance the densities vanish, as in their definitions; they do not
represent a surviving Dirac mass.

## Main results

* `Measurable.truncatedNormalMeasure` — arbitrary measurable incidence sets;
* `TauCeti.Probability.measurable_uncurry_truncatedNormalPDFReal`,
  `TauCeti.Probability.measurable_uncurry_truncatedNormalPDF` — joint density measurability;
* `TauCeti.Probability.measurable_truncatedNormalMeasure` — measurability in the Gaussian
  parameters for a fixed measurable truncation set;
* `TauCeti.Probability.measurable_truncatedNormalMeasure_Ioc` and its other endpoint conventions
  — joint measurability in the Gaussian parameters and real endpoints;
* `TauCeti.Probability.measurable_truncatedNormalMeasure_preimage_Ioc` and its other endpoint
  conventions — the corresponding result for extended-real endpoints.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

section VaryingEvents

variable {α : Type*} [MeasurableSpace α] {m : α → ℝ} {v : α → ℝ≥0} {s : α → Set ℝ}

/-- Truncated Gaussian measures are measurable in the Gaussian parameters and the truncation
event, provided the event has a measurable incidence set. This includes zero variance and
conditioning events of zero mass. -/
@[fun_prop]
theorem _root_.Measurable.truncatedNormalMeasure (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun a => truncatedNormalMeasure (m a) (v a) (s a) := by
  have hμ : Measurable fun a : α => gaussianReal (m a) (v a) :=
    measurable_gaussianReal.comp (hm.prodMk hv)
  have hsection (a : α) : Prod.mk a ⁻¹' {p : α × ℝ | p.2 ∈ s p.1} = s a := by
    ext x
    rfl
  simpa only [truncatedNormalMeasure_def, hsection] using
    hμ.cond (fun _ => inferInstance) hs

/-- The real truncated normal density is jointly measurable in its Gaussian parameters, its
truncation event and its evaluation point, for a measurable incidence set. -/
@[fun_prop]
theorem measurable_uncurry_truncatedNormalPDFReal (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun p : α × ℝ => truncatedNormalPDFReal (m p.1) (v p.1) (s p.1) p.2 := by
  let κ : Kernel α ℝ := ⟨fun a => gaussianReal (m a) (v a),
    measurable_gaussianReal.comp (hm.prodMk hv)⟩
  have hmass : Measurable fun a => gaussianReal (m a) (v a) (s a) :=
    Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hs
      (fun a => inferInstanceAs (IsFiniteMeasure (gaussianReal (m a) (v a))))
  have hpdf : Measurable fun p : α × ℝ => gaussianPDFReal (m p.1) (v p.1) p.2 := by
    fun_prop
  convert (hpdf.indicator hs).div ((hmass.comp measurable_fst).ennreal_toReal) using 1
  ext p
  simp [truncatedNormalPDFReal_def, measureReal_def, Set.indicator]

/-- The extended truncated normal density is jointly measurable in its Gaussian parameters,
truncation event and evaluation point, for a measurable incidence set. -/
@[fun_prop]
theorem measurable_uncurry_truncatedNormalPDF (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun p : α × ℝ => truncatedNormalPDF (m p.1) (v p.1) (s p.1) p.2 := by
  simpa only [truncatedNormalPDF_eq_ofReal] using
    (measurable_uncurry_truncatedNormalPDFReal hm hv hs).ennreal_ofReal

end VaryingEvents

/-- For a fixed measurable truncation set, the truncated normal law is measurable in its mean and
variance, including the zero-variance boundary and zero-mass truncations. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable fun p : ℝ × ℝ≥0 ↦ truncatedNormalMeasure p.1 p.2 s := by
  have hμ : Measurable fun p : ℝ × ℝ≥0 ↦ gaussianReal p.1 p.2 :=
    ProbabilityTheory.measurable_gaussianReal
  simpa only [truncatedNormalMeasure_def] using
    hμ.cond_const hs

/-! ### Real endpoints -/

/-- Truncation to `(l, r]` is jointly measurable in the Gaussian parameters and real endpoints. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ioc :
    Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Ioc p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def, Set.preimage_id] using
    hμ.cond_preimage_Ioc (fun _ ↦ inferInstance) measurable_id (by fun_prop) (by fun_prop)

/-- Truncation to `[l, r]` is jointly measurable in the Gaussian parameters and real endpoints. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Icc :
    Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Icc p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def, Set.preimage_id] using
    hμ.cond_preimage_Icc (fun _ ↦ inferInstance) measurable_id (by fun_prop) (by fun_prop)

/-- Truncation to `(l, r)` is jointly measurable in the Gaussian parameters and real endpoints. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ioo :
    Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Ioo p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def, Set.preimage_id] using
    hμ.cond_preimage_Ioo (fun _ ↦ inferInstance) measurable_id (by fun_prop) (by fun_prop)

/-- Truncation to `[l, r)` is jointly measurable in the Gaussian parameters and real endpoints. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ico :
    Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Ico p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (ℝ × ℝ) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def, Set.preimage_id] using
    hμ.cond_preimage_Ico (fun _ ↦ inferInstance) measurable_id (by fun_prop) (by fun_prop)

/-! ### Extended-real endpoints -/

/-- Truncation to the real preimage of an extended interval `(l, r]` is jointly measurable in the
Gaussian parameters and endpoints. Infinite endpoints give one-sided or untruncated laws. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_preimage_Ioc :
    Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Real.toEReal ⁻¹' Ioc p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def] using
    hμ.cond_preimage_Ioc (fun _ ↦ inferInstance) EReal.measurableEmbedding_coe.measurable
      (by fun_prop) (by fun_prop)

/-- Truncation to the real preimage of an extended interval `[l, r]` is jointly measurable in the
Gaussian parameters and endpoints. Infinite endpoints give one-sided or untruncated laws. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_preimage_Icc :
    Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Real.toEReal ⁻¹' Icc p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def] using
    hμ.cond_preimage_Icc (fun _ ↦ inferInstance) EReal.measurableEmbedding_coe.measurable
      (by fun_prop) (by fun_prop)

/-- Truncation to the real preimage of an extended interval `(l, r)` is jointly measurable in the
Gaussian parameters and endpoints. Infinite endpoints give one-sided or untruncated laws. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_preimage_Ioo :
    Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Real.toEReal ⁻¹' Ioo p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def] using
    hμ.cond_preimage_Ioo (fun _ ↦ inferInstance) EReal.measurableEmbedding_coe.measurable
      (by fun_prop) (by fun_prop)

/-- Truncation to the real preimage of an extended interval `[l, r)` is jointly measurable in the
Gaussian parameters and endpoints. Infinite endpoints give one-sided or untruncated laws. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_preimage_Ico :
    Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      truncatedNormalMeasure p.1.1 p.1.2 (Real.toEReal ⁻¹' Ico p.2.1 p.2.2) := by
  have hμ : Measurable fun p : (ℝ × ℝ≥0) × (EReal × EReal) ↦
      gaussianReal p.1.1 p.1.2 := ProbabilityTheory.measurable_gaussianReal.comp (by fun_prop)
  simpa only [truncatedNormalMeasure_def] using
    hμ.cond_preimage_Ico (fun _ ↦ inferInstance) EReal.measurableEmbedding_coe.measurable
      (by fun_prop) (by fun_prop)

end TauCeti.Probability
