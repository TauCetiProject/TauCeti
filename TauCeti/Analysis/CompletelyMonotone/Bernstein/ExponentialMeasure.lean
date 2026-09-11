/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.Probability.Distributions.Exponential

/-!
# Exponential measures as Bernstein representing measures

The exponential probability measure with rate `r > 0`, transported from `ℝ` to `ℝ≥0`, has
Laplace transform

`t ↦ r / (r + t)`.

This gives the non-atomic acceptance example for Bernstein's theorem: at unit rate the function
`t ↦ 1 / (1 + t)` is represented by the measure with density `e⁻ˣ` on `[0, ∞)`.  Unlike the
Dirac examples, this exercises a genuinely continuous representing measure.

The measure is defined by pushing Mathlib's `ProbabilityTheory.expMeasure` forward along
`Real.toNNReal`.  A positive-rate exponential random variable is nonnegative almost surely, so
this transport retains the law and turns its moment-generating-function formula into the required
Laplace-transform formula.

## Main declarations

* `TauCeti.nnrealExpMeasure`: the exponential measure on `ℝ≥0`.
* `TauCeti.nnrealExpMeasure_one_eq_map_withDensity`: at unit rate, this is the pushforward of
  the measure with density `e⁻ˣ` on the nonnegative real half-line.
* `TauCeti.isProbabilityMeasure_nnrealExpMeasure`: it is a probability measure at positive rate.
* `TauCeti.laplaceTransform_nnrealExpMeasure`: its Laplace transform is `r / (r + t)`.
* `TauCeti.representsLaplace_nnrealExpMeasure`: the resulting Bernstein representation.
* `TauCeti.bernsteinMeasure_one_div_one_add`: the canonical Bernstein measure of
  `t ↦ 1 / (1 + t)` is the unit-rate exponential measure.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Example 1.4 and Theorem 1.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TauCeti

/-- The exponential measure of rate `r` on `ℝ≥0`, obtained by transporting the usual exponential
law on `ℝ` along `Real.toNNReal`.

For `r > 0` this transport loses no information because the exponential law is supported on the
nonnegative half-line. -/
noncomputable def nnrealExpMeasure (r : ℝ) : Measure ℝ≥0 :=
  (expMeasure r).map Real.toNNReal

/-- At unit rate, `nnrealExpMeasure` is the measure with density `e⁻ˣ` on the nonnegative real
half-line, transported to `ℝ≥0`.  The displayed `if` makes the zero density on negative reals
explicit before the transport. -/
theorem nnrealExpMeasure_one_eq_map_withDensity :
    nnrealExpMeasure 1 =
      (volume.withDensity fun x : ℝ =>
        ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0)).map Real.toNNReal := by
  rw [nnrealExpMeasure]
  apply congrArg (Measure.map Real.toNNReal)
  change volume.withDensity (exponentialPDF 1) = _
  apply congrArg volume.withDensity
  funext x
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x <;> simp [hx]

/-- The positive-rate exponential measure on `ℝ≥0` is a probability measure. -/
theorem isProbabilityMeasure_nnrealExpMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (nnrealExpMeasure r) := by
  let _ := isProbabilityMeasure_expMeasure hr
  rw [nnrealExpMeasure]
  infer_instance

/-- A positive-rate exponential law on `ℝ` is nonnegative almost surely. -/
private theorem ae_nonneg_expMeasure {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  let _ := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic (0 : ℝ)) = 0 := by
    rw [← ProbabilityTheory.ofReal_cdf]
    simp [cdf_expMeasure_eq hr]
  have hIio : expMeasure r (Iio (0 : ℝ)) = 0 :=
    measure_mono_null Iio_subset_Iic_self hIic
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hIio] with x hx
  exact not_lt.mp hx

/-- The Laplace transform of the exponential measure of rate `r > 0` is `r / (r + t)` throughout
its maximal finiteness domain `-r < t`. -/
theorem laplaceTransform_nnrealExpMeasure {r t : ℝ} (hr : 0 < r) (ht : -r < t) :
    laplaceTransform (nnrealExpMeasure r) t = r / (r + t) := by
  rw [laplaceTransform_apply, nnrealExpMeasure,
    integral_map_of_stronglyMeasurable measurable_real_toNNReal (by fun_prop)]
  calc
    ∫ x : ℝ, exp (-(t * ((Real.toNNReal x : ℝ≥0) : ℝ))) ∂expMeasure r =
        ∫ x : ℝ, exp (-(t * x)) ∂expMeasure r := by
      apply integral_congr_ae
      filter_upwards [ae_nonneg_expMeasure hr] with x hx
      rw [Real.coe_toNNReal x hx]
    _ = mgf (fun x : ℝ => x) (expMeasure r) (-t) := by
      simp only [mgf, neg_mul]
    _ = r / (r - -t) := Probability.mgf_fun_id_expMeasure hr (by linarith)
    _ = r / (r + t) := by ring

/-- The positive-rate exponential measure represents `t ↦ r / (r + t)` in Bernstein's theorem. -/
theorem representsLaplace_nnrealExpMeasure {r : ℝ} (hr : 0 < r) :
    RepresentsLaplace (nnrealExpMeasure r) (fun t => r / (r + t)) := by
  let _ := isProbabilityMeasure_nnrealExpMeasure hr
  rw [representsLaplace_iff]
  exact ⟨inferInstance, fun _ ht => (laplaceTransform_nnrealExpMeasure hr (by linarith)).symm⟩

/-- The canonical Bernstein representing measure of `t ↦ r / (r + t)`, for positive `r`, is the
exponential measure of rate `r` on `ℝ≥0`. -/
theorem bernsteinMeasure_div_add {r : ℝ} (hr : 0 < r) :
    bernsteinMeasure (fun t => r / (r + t)) = nnrealExpMeasure r :=
  (eq_bernsteinMeasure _ (representsLaplace_nnrealExpMeasure hr)).symm

/-- At unit rate, the exponential measure on `ℝ≥0` represents `t ↦ 1 / (1 + t)`. -/
theorem representsLaplace_nnrealExpMeasure_one :
    RepresentsLaplace (nnrealExpMeasure 1) (fun t => 1 / (1 + t)) :=
  representsLaplace_nnrealExpMeasure one_pos

/-- The canonical Bernstein representing measure of `t ↦ 1 / (1 + t)` is the unit-rate
exponential measure on `ℝ≥0`. -/
theorem bernsteinMeasure_one_div_one_add :
    bernsteinMeasure (fun t => 1 / (1 + t)) = nnrealExpMeasure 1 :=
  bernsteinMeasure_div_add one_pos

end TauCeti

end

end
