/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Complex
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Basic

/-!
# The Haar character of units of a finite-dimensional real algebra

Let `A` be a finite-dimensional real normed algebra. A unit `x` of `A` acts on the additive group
of `A` by left multiplication, and `μ (x • s) = distribHaarChar A x * μ s` for every regular
additive Haar measure `μ` on `A` and every set `s`. Multiplication by `x` is an `ℝ`-linear map of
determinant `Algebra.norm ℝ x`, so Mathlib's image formula
`MeasureTheory.Measure.addHaar_image_linearMap` scales `μ` by `|Algebra.norm ℝ x|`, and the
character is read off one positive compact set through Mathlib's criterion
`MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul`. In particular the character is `|x|`
on `ℝ` and `|z|²` on `ℂ`.

## Main results

* `MeasureTheory.distribHaarChar_eq_nnnorm_algebraNorm`, `MeasureTheory.distribHaarChar_real`,
  `MeasureTheory.distribHaarChar_complex`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism).
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) proves the formulas on `ℝ` and `ℂ` as
  `MeasureTheory.ringHaarChar_real` and `MeasureTheory.ringHaarChar_complex` in
  `FLT/HaarMeasure/HaarChar/RealComplex.lean` (by Yaël Dillies and Javier López-Contreras), and
  the determinant formula for algebras as `algebra_ringHaarChar_eq_ringHaarChar_det` in
  `FLT/HaarMeasure/HaarChar/FiniteDimensional.lean` (by Kevin Buzzard and Norbert Voelker).
-/

public section

open MeasureTheory Measure Set TopologicalSpace
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-- **The Haar character of a finite-dimensional real algebra.** Multiplication by a unit `x` is
an `ℝ`-linear map of determinant `Algebra.norm ℝ x`, so it scales Haar measure by
`|Algebra.norm ℝ x|`. -/
theorem distribHaarChar_eq_nnnorm_algebraNorm (x : Aˣ) :
    distribHaarChar A x = ‖Algebra.norm ℝ (x : A)‖₊ := by
  borelize A
  let μ : Measure A := addHaar
  let K : PositiveCompacts A := Classical.arbitrary _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := K) (K.measure_ne_zero μ)
    (K.measure_ne_top μ) ?_
  have hsmul : x • (K : Set A) = Algebra.lmul ℝ A (x : A) '' K := by
    ext b
    simp [Set.mem_smul_set, Units.smul_def]
  rw [hsmul, addHaar_image_linearMap, ← Algebra.norm_apply, ← Real.eNorm_eq_ofReal_abs,
    eNorm_eq_nnNorm]

/-- The Haar character of `ℝ` is the absolute value. -/
@[simp]
theorem distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  rw [distribHaarChar_eq_nnnorm_algebraNorm, Algebra.norm_self, MonoidHom.id_apply]

/-- The Haar character of `ℂ` is the square of the absolute value. -/
@[simp]
theorem distribHaarChar_complex (z : ℂˣ) : distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  rw [distribHaarChar_eq_nnnorm_algebraNorm, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
  ext
  simp

end MeasureTheory
