/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.Triangular.Basic

/-!
# Affine transport of triangular laws

For a triangular variable with endpoints `a`, `b` and mode `c`, a positive affine map
`x ↦ d + s * x` transforms all three parameters by the same map. A negative slope reverses
the endpoints and transforms the mode. These identities include endpoint modes and invalid
parameters, where both measures are zero.

The real density identities give the corresponding change of variables pointwise, including
at the mode. The measure identities and their `HasLaw` corollaries let callers transport the
whole law and then use the generic affine formulas for moments, transforms and quantiles.
For valid parameters, slope zero is covered by `MeasureTheory.Measure.map_const`, giving
the Dirac mass at the intercept.

The proof follows the density-transport pattern of
`TauCeti.Probability.Distributions.AsymmetricLaplace.Affine`, using
`TauCeti.Probability.map_affine_withDensity_volume`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), Chapter 26, Section 9.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A positive affine map transforms the endpoints and mode of the real triangular density.
The identity includes invalid parameters and endpoint modes. -/
theorem triangularPDFReal_affine_pos (a b c d x : ℝ) {s : ℝ} (hs : 0 < s) :
    triangularPDFReal (d + s * a) (d + s * b) (d + s * c) x =
      s⁻¹ * triangularPDFReal a b c ((x - d) / s) := by
  have hguard :
      (d + s * a ≤ d + s * c ∧ d + s * c ≤ d + s * b ∧
        x ∈ Ioo (d + s * a) (d + s * b)) ↔
      (a ≤ c ∧ c ≤ b ∧ (x - d) / s ∈ Ioo a b) := by
    simp only [mem_Ioo, lt_div_iff₀ hs, div_lt_iff₀ hs]
    constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
      (refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith)
  have hbranch : x < d + s * c ↔ (x - d) / s < c := by
    rw [div_lt_iff₀ hs]
    constructor <;> intro h <;> linarith
  simp only [triangularPDFReal_def, hguard, hbranch]
  split_ifs with h hxc
  · have hsa : d + s * b - (d + s * a) = s * (b - a) := by ring
    have hsc : d + s * c - (d + s * a) = s * (c - a) := by ring
    have hnum : x - (d + s * a) = s * ((x - d) / s - a) := by
      field_simp
      ring
    rw [hsa, hsc, hnum]
    field_simp
  · have hsa : d + s * b - (d + s * a) = s * (b - a) := by ring
    have hsc : d + s * b - (d + s * c) = s * (b - c) := by ring
    have hnum : d + s * b - x = s * (b - (x - d) / s) := by
      field_simp
      ring
    rw [hsa, hsc, hnum]
    field_simp
  · simp

/-- Negation reverses the endpoints and negates the mode of the real triangular density.
This holds pointwise, including at the mode and at the endpoints. -/
theorem triangularPDFReal_neg (a b c x : ℝ) :
    triangularPDFReal (-b) (-a) (-c) x = triangularPDFReal a b c (-x) := by
  have hguard : (-b ≤ -c ∧ -c ≤ -a ∧ x ∈ Ioo (-b) (-a)) ↔
      (a ≤ c ∧ c ≤ b ∧ -x ∈ Ioo a b) := by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
      (refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  rw [triangularPDFReal_def, triangularPDFReal_def]
  by_cases h : a ≤ c ∧ c ≤ b ∧ -x ∈ Ioo a b
  · rw [ite_eq_left (hguard.mpr h), ite_eq_left h]
    rcases lt_trichotomy (-x) c with hxc | hxc | hcx
    · rw [ite_eq_right (by linarith : ¬ x < -c), ite_eq_left hxc]
      congr 1 <;> ring
    · have hca : c - a ≠ 0 := by linarith [h.2.2.1]
      have hbc : b - c ≠ 0 := by linarith [h.2.2.2]
      have hba : b - a ≠ 0 := by linarith [h.2.2.1, h.2.2.2]
      rw [ite_eq_right (by linarith : ¬ x < -c),
        ite_eq_right (by linarith : ¬ -x < c)]
      simp only [sub_neg_eq_add, neg_add_eq_sub] at *
      field_simp [hba]
      nlinarith
    · rw [ite_eq_left (by linarith : x < -c), ite_eq_right hcx.not_gt]
      congr 1 <;> ring
  · rw [ite_eq_right (mt hguard.mp h), ite_eq_right h]

/-- A negative affine map reverses the endpoints and transforms the mode of a triangular
density, with the usual inverse-absolute-slope factor. -/
theorem triangularPDFReal_affine_neg (a b c d x : ℝ) {s : ℝ} (hs : s < 0) :
    triangularPDFReal (d + s * b) (d + s * a) (d + s * c) x =
      |s|⁻¹ * triangularPDFReal a b c ((x - d) / s) := by
  have h := triangularPDFReal_affine_pos (-b) (-a) (-c) d x (neg_pos.mpr hs)
  rw [triangularPDFReal_neg] at h
  simpa [abs_of_neg hs, div_neg] using h

/-- The affine density of a triangular law at a positive slope is the named density with
transformed endpoints and mode. -/
-- Prefer the family density to the generic expansion by affineDensity_apply.
@[simp 1100]
theorem affineDensity_triangularPDF_pos (a b c d x : ℝ) {s : ℝ} (hs : 0 < s) :
    affineDensity d s (triangularPDF a b c) x =
      triangularPDF (d + s * a) (d + s * b) (d + s * c) x := by
  rw [affineDensity_apply, abs_of_pos hs, triangularPDF_eq_ofReal,
    triangularPDF_eq_ofReal, triangularPDFReal_affine_pos a b c d x hs,
    ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]

/-- The affine density of a triangular law at a negative slope is the named density with
reversed transformed endpoints and transformed mode. -/
-- Prefer the family density to the generic expansion by affineDensity_apply.
@[simp 1100]
theorem affineDensity_triangularPDF_neg (a b c d x : ℝ) {s : ℝ} (hs : s < 0) :
    affineDensity d s (triangularPDF a b c) x =
      triangularPDF (d + s * b) (d + s * a) (d + s * c) x := by
  rw [affineDensity_apply, triangularPDF_eq_ofReal, triangularPDF_eq_ofReal,
    triangularPDFReal_affine_neg a b c d x hs,
    ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg s))]

/-- A positive affine image of a triangular law transforms both endpoints and the mode.
This includes the zero laws at invalid parameters. -/
@[simp]
theorem triangularMeasure_map_affine_pos (a b c d : ℝ) {s : ℝ} (hs : 0 < s) :
    (triangularMeasure a b c).map (fun x ↦ d + s * x) =
      triangularMeasure (d + s * a) (d + s * b) (d + s * c) := by
  rw [triangularMeasure_eq_withDensity, map_affine_withDensity_volume _ hs.ne',
    triangularMeasure_eq_withDensity]
  congr 1
  ext x
  exact affineDensity_triangularPDF_pos a b c d x hs

/-- A negative affine image of a triangular law reverses the transformed endpoints and
transforms the mode. This includes the zero laws at invalid parameters. -/
@[simp]
theorem triangularMeasure_map_affine_neg (a b c d : ℝ) {s : ℝ} (hs : s < 0) :
    (triangularMeasure a b c).map (fun x ↦ d + s * x) =
      triangularMeasure (d + s * b) (d + s * a) (d + s * c) := by
  rw [triangularMeasure_eq_withDensity, map_affine_withDensity_volume _ hs.ne,
    triangularMeasure_eq_withDensity]
  congr 1
  ext x
  exact affineDensity_triangularPDF_neg a b c d x hs

/-- A positive affine image of a triangular random variable has transformed endpoints and
mode, without assumptions on the source measure. -/
theorem hasLaw_affine_pos_triangularMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {a b c d s : ℝ} (hs : 0 < s)
    (hX : HasLaw X (triangularMeasure a b c) P) :
    HasLaw (fun ω ↦ d + s * X ω)
      (triangularMeasure (d + s * a) (d + s * b) (d + s * c)) P :=
  (HasLaw.mk (by fun_prop) (triangularMeasure_map_affine_pos a b c d hs)).fun_comp hX

/-- A negative affine image of a triangular random variable has reversed transformed
endpoints and transformed mode, without assumptions on the source measure. -/
theorem hasLaw_affine_neg_triangularMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {a b c d s : ℝ} (hs : s < 0)
    (hX : HasLaw X (triangularMeasure a b c) P) :
    HasLaw (fun ω ↦ d + s * X ω)
      (triangularMeasure (d + s * b) (d + s * a) (d + s * c)) P :=
  (HasLaw.mk (by fun_prop) (triangularMeasure_map_affine_neg a b c d hs)).fun_comp hX

end TauCeti.Probability
