/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order

/-!
# A finite measure's characteristic function is positive definite

This file proves the "easy" (necessary) direction of Bochner's theorem: the characteristic
function `charFun μ` of a finite measure `μ` on a real inner product space `E` is a
*positive-definite function*. Concretely, for every finite family `(cᵢ, tᵢ)` the Hermitian
form

`∑ᵢ ∑ⱼ cᵢ · conj cⱼ · charFun μ (tᵢ - tⱼ)`

is a nonnegative real number (`charFun_sum_mul_conj_nonneg`), equivalently the kernel
`(x, y) ↦ charFun μ (x - y)` on `E` is positive semidefinite (`posSemidef_charFun`). The proof
is the classical computation: the Hermitian form equals the honest integral

`∫ y, ‖∑ᵢ cᵢ · exp (⟪y, tᵢ⟫ * I)‖ ^ 2 ∂μ`

of a nonnegative integrand (`charFun_sum_mul_conj_eq_integral`), because
`exp (⟪y, tᵢ⟫ * I) · conj (exp (⟪y, tⱼ⟫ * I)) = exp (⟪y, tᵢ - tⱼ⟫ * I)` makes the double sum
factor through a squared modulus.

The results are stated directly on Mathlib's `MeasureTheory.charFun`, so they need no
positive-definiteness *predicate*; this is the half of Bochner's theorem that is provable without
the harder measure-extraction (Riesz–Markov / Lévy–Prokhorov) machinery.

`charFun` and `innerProbChar` are from
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`; positive semidefiniteness
of complex matrices is Mathlib's `Matrix.PosSemidef`.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Complex ComplexConjugate

open scoped ComplexOrder

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

private theorem integrable_exp_inner_mul_I (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ :=
  ((innerProbChar a).integrable μ).congr (.of_forall (innerProbChar_apply a))

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem exp_mul_conj_exp_inner (y a b : E) :
    exp (⟪y, a⟫ * I) * conj (exp (⟪y, b⟫ * I)) = exp (⟪y, a - b⟫ * I) := by
  rw [← exp_conj, ← exp_add, inner_sub_right]
  simp [sub_mul, ← sub_eq_add_neg]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem sq_norm_sum_mul_exp_inner {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E)
    (y : E) : ((‖∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) := by
  rw [ofReal_pow, ← mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← exp_mul_conj_exp_inner]
  ring

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` equals the integral of the
squared modulus `‖∑ᵢ cᵢ · exp (⟪y, tᵢ⟫ * I)‖ ^ 2`, a manifestly nonnegative function. -/
theorem charFun_sum_mul_conj_eq_integral {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j) =
      ((∫ y, ‖∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hint (i j : ι) : Integrable (fun y => c i * conj (c j) * exp (⟪y, t i - t j⟫ * I)) μ :=
    (integrable_exp_inner_mul_I _).const_mul _
  simp_rw [← integral_complex_ofReal, sq_norm_sum_mul_exp_inner,
    integral_finsetSum s fun i _ => integrable_finsetSum s fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum s fun j _ => hint i j]
  simp_rw [integral_const_mul, charFun_apply]

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` is a nonnegative real:
`charFun μ` is a positive-definite function. -/
theorem charFun_sum_mul_conj_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j) := by
  rw [charFun_sum_mul_conj_eq_integral, zero_le_real]
  exact integral_nonneg fun _ => by positivity

/-- The subtraction kernel `(x, y) ↦ charFun μ (x - y)` of a finite measure is positive
semidefinite: the matrix reformulation of the positive-definiteness of `charFun μ`. -/
theorem posSemidef_charFun : Matrix.PosSemidef fun x y : E => charFun μ (x - y) := by
  refine ⟨.ext fun x y => ?_, fun x => ?_⟩
  · rw [← neg_sub y x, charFun_neg, ← starRingEnd_apply]
  · simpa [Finsupp.sum, mul_right_comm] using
      charFun_sum_mul_conj_nonneg (μ := μ) x.support (fun i => conj (x i)) id

end TauCeti
