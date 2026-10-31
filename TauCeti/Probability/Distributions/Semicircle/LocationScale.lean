/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.PDF
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Semicircle laws with prescribed centre and variance

`semicircleReal a v` is the affine image of the unit-radius law `semicircleMeasure` under
`x ↦ a + 2 * √v * x`. The factor two makes `v` the variance, rather than the squared radius.
The construction includes the point mass at `a` when `v = 0`.

We give normalization, measurability in the parameters, support, integrability, mean and
variance, and transport under every real affine map. For positive variance its density is
obtained from the existing unit-radius density by `affineDensity`; no new density is defined.
These laws provide the centre/variance normalization used for limiting spectral distributions.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- The semicircle law with centre `a` and variance `v`, including the Dirac law at `v = 0`. -/
def semicircleReal (a : ℝ) (v : ℝ≥0) : Measure ℝ :=
  semicircleMeasure.map fun x ↦ a + 2 * Real.sqrt v * x

/-- The centre/variance semicircle is the affine image of the unit-radius semicircle. -/
theorem semicircleReal_def (a : ℝ) (v : ℝ≥0) :
    semicircleReal a v = semicircleMeasure.map fun x ↦ a + 2 * Real.sqrt v * x :=
  (rfl)

/-- Every centre/variance semicircle is a probability law. -/
instance isProbabilityMeasure_semicircleReal (a : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (semicircleReal a v) := by
  rw [semicircleReal_def]
  infer_instance

/-- At zero variance the semicircle law is a point mass. -/
@[simp]
theorem semicircleReal_zero_var (a : ℝ) : semicircleReal a 0 = Measure.dirac a := by
  simp [semicircleReal_def]

/-- The unit-radius law has centre zero and variance one quarter. -/
@[simp]
theorem semicircleReal_zero_inv_four : semicircleReal 0 4⁻¹ = semicircleMeasure := by
  norm_num [semicircleReal_def, Real.sqrt_inv]
  have h : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [h]
  norm_num

/-- The law depends measurably on its centre and variance. -/
@[fun_prop]
theorem measurable_semicircleReal :
    Measurable fun p : ℝ × ℝ≥0 ↦ semicircleReal p.1 p.2 := by
  have h : Measurable fun p : ℝ × ℝ≥0 ↦
      ((⟨semicircleMeasure, inferInstance⟩ : ProbabilityMeasure ℝ),
        p.1, 2 * Real.sqrt p.2) := by fun_prop
  simp only [semicircleReal_def]
  rw [← ProbabilityMeasure.coe_mk semicircleMeasure inferInstance]
  exact measurable_map_affine.comp h

/-- A semicircle variable lies almost surely between its two support edges. -/
theorem ae_mem_Icc_semicircleReal (a : ℝ) (v : ℝ≥0) :
    ∀ᵐ x ∂semicircleReal a v, x ∈ Icc (a - 2 * Real.sqrt v) (a + 2 * Real.sqrt v) := by
  rw [semicircleReal_def]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).2
  filter_upwards [ae_mem_Ioo_semicircleMeasure] with x hx
  constructor <;> nlinarith [Real.sqrt_nonneg (v : ℝ), hx.1, hx.2]

/-- The exact support is the closed interval between the semicircle edges, also at variance zero.
-/
@[simp]
theorem support_semicircleReal (a : ℝ) (v : ℝ≥0) :
    (semicircleReal a v).support = Icc (a - 2 * Real.sqrt v) (a + 2 * Real.sqrt v) := by
  by_cases hv : v = 0
  · subst v
    simp [Measure.support_dirac]
  · have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast pos_iff_ne_zero.2 hv)
    rw [semicircleReal_def, support_map_affine (by positivity), support_semicircleMeasure]
    simpa [add_comm, sub_eq_add_neg] using
      (image_affine_Icc' (a := 2 * Real.sqrt (v : ℝ)) (by positivity) a (-1) 1)

/-- All exponential moments of a centre/variance semicircle exist. -/
@[simp]
theorem integrableExpSet_id_semicircleReal (a : ℝ) (v : ℝ≥0) :
    integrableExpSet id (semicircleReal a v) = univ := by
  rw [semicircleReal_def, integrableExpSet_id_map_affine,
    integrableExpSet_id_semicircleMeasure]
  simp

/-- Every natural power is integrable, including for the degenerate law. -/
theorem integrable_pow_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (semicircleReal a v) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp

/-- The mean of the centre/variance semicircle is its centre. -/
@[simp]
theorem integral_id_semicircleReal (a : ℝ) (v : ℝ≥0) :
    ∫ x, x ∂semicircleReal a v = a := by
  have hi : Integrable id semicircleMeasure :=
    integrable_of_mem_interior_integrableExpSet (by simp)
  rw [semicircleReal_def, integral_id_map_affine hi, integral_id_semicircleMeasure]
  ring

/-- The variance parameter is the actual variance, not the squared radius. -/
@[simp]
theorem variance_id_semicircleReal (a : ℝ) (v : ℝ≥0) :
    variance id (semicircleReal a v) = v := by
  rw [semicircleReal_def, variance_id_map_affine, variance_id_semicircleMeasure]
  nlinarith [Real.sq_sqrt v.coe_nonneg]

/-- An affine image of a semicircle has the transported centre and the squared-slope variance.
Negative slopes are allowed, as are zero slope and zero variance. -/
theorem map_affine_semicircleReal (a b c : ℝ) (v : ℝ≥0) :
    (semicircleReal a v).map (fun x ↦ b + c * x) =
      semicircleReal (b + c * a) (Real.toNNReal (c ^ 2) * v) := by
  rw [semicircleReal_def, map_affine_map_affine, semicircleReal_def]
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg c),
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  by_cases hc : 0 ≤ c
  · congr 1
    ext x
    rw [abs_of_nonneg hc]
    ring
  · calc
      _ = (semicircleMeasure.map Neg.neg).map
          (fun x ↦ b + c * a + 2 * (|c| * Real.sqrt v) * x) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        ext x
        simp only [Function.comp_apply]
        rw [abs_of_neg (lt_of_not_ge hc)]
        ring
      _ = _ := by rw [map_neg_semicircleMeasure]

/-- At positive variance the semicircle has density `(2πv)⁻¹ √(4v - (x - a)²)`.
The real square root makes the density zero outside the support interval. -/
theorem semicircleReal_eq_withDensity (a : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    semicircleReal a v = volume.withDensity
      (fun x ↦ ENNReal.ofReal ((2 * Real.pi * v)⁻¹ * Real.sqrt (4 * v - (x - a) ^ 2))) := by
  have hv' : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hv'
  have hs2 := Real.sq_sqrt v.coe_nonneg
  rw [semicircleReal_def, semicircleMeasure_eq_withDensity,
    map_affine_withDensity_volume _ (by positivity)]
  congr 1
  ext x
  simp only [affineDensity_apply, semicirclePDF_apply, semicirclePDFReal_apply,
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (v : ℝ))]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hrad : 1 - ((x - a) / (2 * Real.sqrt v)) ^ 2 =
      (4 * v - (x - a) ^ 2) / (2 * Real.sqrt v) ^ 2 := by
    field_simp
    nlinarith
  rw [hrad, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp
  rw [hs2]

end TauCeti.Probability
