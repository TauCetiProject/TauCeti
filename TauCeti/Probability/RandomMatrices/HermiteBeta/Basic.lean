/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Hermite (Gaussian) beta ensembles: densities, measures, and symmetries

For any inverse temperature `β > 0`, quadratic confinement `c > 0`, and particle count `n : ℕ`,
the Gaussian beta (Hermite beta) ensemble is the probability law on `ℝⁿ` with Lebesgue density
proportional to

`exp (-(c / 2) * ∑ i, x i ^ 2) * (∏ i < j, |x i - x j|) ^ β`,

whose normalization constant is the Mehta–Selberg constant

`Z_{n, β, c} = c ^ (-(n / 2 + β * n * (n - 1) / 4)) * (2 * π) ^ (n / 2) *
  ∏ j ∈ Icc 1 n, (Γ(1 + j * β / 2) / Γ(1 + β / 2))`.

This file defines the absolute Vandermonde product, the Mehta–Selberg normalization constant, and
both the unordered Gaussian beta measure on `ℝⁿ` and the ordered Gaussian beta measure on the
strictly decreasing Weyl chamber `{x : Fin n → ℝ | StrictAnti x}`. It establishes positivity,
measurability, permutation invariance, scaling covariance (`x ↦ s • x` maps confinement `c` to
`c / s ^ 2`), and concrete low-dimensional evaluations of the normalization constant (`n = 0, 1`,
GUE `n = 2, β = 2`, GOE `n = 2, β = 1`).

The Dumitriu–Edelman tridiagonal matrix model, the exact total-mass proof (`IsProbabilityMeasure`),
and the Mehta–Selberg Bochner integral identity are proved in
`TauCeti.Probability.RandomMatrices.HermiteBeta.DumitriuEdelman`.

## Main definitions

* `TauCeti.Probability.vandermondeProd`: `∏ i < j, |x i - x j|`.
* `TauCeti.Probability.gaussianBetaNormConst`: the Mehta–Selberg constant `Z_{n, β, c}`.
* `TauCeti.Probability.gaussianBetaPDFReal`, `TauCeti.Probability.gaussianBetaPDF`, and
  `TauCeti.Probability.gaussianBetaMeasure`: the unordered Gaussian beta density and measure.
* `TauCeti.Probability.gaussianBetaOrderedPDFReal`, `TauCeti.Probability.gaussianBetaOrderedPDF`,
  and `TauCeti.Probability.gaussianBetaOrderedMeasure`: the ordered Gaussian beta density and
  measure on the strictly decreasing Weyl chamber.

## Main results

* `TauCeti.Probability.vandermondeProd_eq_abs_det_vandermonde`,
  `TauCeti.Probability.vandermondeProd_smul`, and `TauCeti.Probability.vandermondeProd_comp_perm`:
  identification with `|(Matrix.vandermonde x).det|`, scaling homogeneity, and permutation
  invariance of the Vandermonde product.
* `TauCeti.Probability.map_comp_perm_gaussianBetaMeasure`: permutation invariance of the unordered
  Gaussian beta measure.
* `TauCeti.Probability.map_smul_gaussianBetaMeasure` and
  `TauCeti.Probability.map_smul_gaussianBetaOrderedMeasure`: scaling covariance of the unordered
  and ordered Gaussian beta measures.
* `TauCeti.Probability.gaussianBetaNormConst_one`,
  `TauCeti.Probability.gaussianBetaNormConst_two_two`, and
  `TauCeti.Probability.gaussianBetaNormConst_two_one`: concrete low-dimensional checks.

## References

* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.5.1.
* P. J. Forrester, *Log-Gases and Random Matrices*, Princeton University Press, 2010, §1.9 and §4.7.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

/-! ### The Vandermonde product -/

/-- The absolute Vandermonde product `∏ i < j, |x i - x j|` of a tuple `x : Fin n → ℝ`. -/
def vandermondeProd {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, |x i - x j|

/-- The absolute Vandermonde product is nonnegative. -/
theorem vandermondeProd_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vandermondeProd x :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- The Vandermonde product is strictly positive whenever `x` has distinct coordinates. -/
theorem vandermondeProd_pos_of_injective {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    0 < vandermondeProd x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hj =>
    abs_pos.mpr (sub_ne_zero.mpr (hx.ne (Finset.mem_Ioi.mp hj).ne))

/-- On strictly decreasing tuples, the absolute values in `vandermondeProd` drop. -/
theorem vandermondeProd_of_strictAnti {n : ℕ} {x : Fin n → ℝ} (hx : StrictAnti x) :
    vandermondeProd x = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x i - x j) :=
  Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ hj =>
    abs_of_pos (sub_pos.mpr (hx (Finset.mem_Ioi.mp hj)))

/-- The Vandermonde product of a `0`-tuple is `1`. -/
@[simp]
theorem vandermondeProd_zero (x : Fin 0 → ℝ) : vandermondeProd x = 1 := by
  simp [vandermondeProd]

/-- The Vandermonde product of a `1`-tuple is `1`. -/
@[simp]
theorem vandermondeProd_one (x : Fin 1 → ℝ) : vandermondeProd x = 1 := by
  simp [vandermondeProd]

/-- The Vandermonde product depends continuously on the coordinates. -/
@[fun_prop]
theorem continuous_vandermondeProd (n : ℕ) : Continuous (vandermondeProd (n := n)) := by
  unfold vandermondeProd
  fun_prop

/-- The Vandermonde product is measurable. -/
@[fun_prop]
theorem measurable_vandermondeProd (n : ℕ) : Measurable (vandermondeProd (n := n)) :=
  (continuous_vandermondeProd n).measurable

/-- The absolute Vandermonde product equals the absolute value of the Vandermonde determinant. -/
theorem vandermondeProd_eq_abs_det_vandermonde {n : ℕ} (x : Fin n → ℝ) :
    vandermondeProd x = |(Matrix.vandermonde x).det| := by
  rw [vandermondeProd, Matrix.det_vandermonde, Finset.abs_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.abs_prod]
  exact Finset.prod_congr rfl fun j _ => abs_sub_comm (x i) (x j)

/-- Scaling coordinates by `s` multiplies `vandermondeProd` by `|s| ^ (n * (n - 1) / 2)`. -/
theorem vandermondeProd_smul {n : ℕ} (s : ℝ) (x : Fin n → ℝ) :
    vandermondeProd (s • x) = |s| ^ (n * (n - 1) / 2) * vandermondeProd x := by
  have hmat : Matrix.vandermonde (s • x) =
      Matrix.vandermonde x * Matrix.diagonal (fun j : Fin n => s ^ j.val) := by
    ext i j
    simp [Matrix.vandermonde, Matrix.mul_diagonal, mul_pow, mul_comm]
  rw [vandermondeProd_eq_abs_det_vandermonde, vandermondeProd_eq_abs_det_vandermonde, hmat,
    Matrix.det_mul, Matrix.det_diagonal, abs_mul, Finset.abs_prod, mul_comm]
  congr 1
  simp_rw [abs_pow, Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun k => k) n,
    Finset.sum_range_id]

/-- `vandermondeProd` is invariant under coordinate permutations. -/
theorem vandermondeProd_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    vandermondeProd (x ∘ σ) = vandermondeProd x := by
  have hmat : Matrix.vandermonde (x ∘ σ) = (Matrix.vandermonde x).submatrix σ id := by
    ext i j; rfl
  rw [vandermondeProd_eq_abs_det_vandermonde, vandermondeProd_eq_abs_det_vandermonde, hmat,
    Matrix.det_permute, abs_mul, abs_unit_intCast, one_mul]

/-! ### The Mehta–Selberg normalization constant and Gaussian beta densities -/

/-- The Mehta–Selberg normalization constant for the `n`-particle Gaussian beta ensemble with Dyson
index `β` and quadratic confinement `c`:
`c ^ (-(n / 2 + β * n * (n - 1) / 4)) * (2 * π) ^ (n / 2) *
  ∏ j ∈ Finset.Icc 1 n, (Real.Gamma (1 + j * β / 2) / Real.Gamma (1 + β / 2))`. -/
def gaussianBetaNormConst (β c : ℝ) (n : ℕ) : ℝ :=
  c ^ (-((n : ℝ) / 2 + β * n * ((n : ℝ) - 1) / 4)) * (2 * Real.pi) ^ ((n : ℝ) / 2) *
    ∏ j ∈ Finset.Icc 1 n, (Real.Gamma (1 + (j : ℝ) * β / 2) / Real.Gamma (1 + β / 2))

/-- Explicit formula for `gaussianBetaNormConst`. -/
theorem gaussianBetaNormConst_def (β c : ℝ) (n : ℕ) :
    gaussianBetaNormConst β c n =
      c ^ (-((n : ℝ) / 2 + β * n * ((n : ℝ) - 1) / 4)) * (2 * Real.pi) ^ ((n : ℝ) / 2) *
        ∏ j ∈ Finset.Icc 1 n, (Real.Gamma (1 + (j : ℝ) * β / 2) / Real.Gamma (1 + β / 2)) := by
  rfl

/-- The Mehta–Selberg normalization constant is strictly positive for `β > 0` and `c > 0`. -/
theorem gaussianBetaNormConst_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (n : ℕ) :
    0 < gaussianBetaNormConst β c n := by
  unfold gaussianBetaNormConst
  refine mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos (by positivity) _))
    (Finset.prod_pos fun j _ => div_pos (Real.Gamma_pos_of_pos (by positivity))
      (Real.Gamma_pos_of_pos (by positivity)))

/-- At `n = 0`, the Mehta–Selberg normalization constant is `1`. -/
@[simp]
theorem gaussianBetaNormConst_zero (β c : ℝ) : gaussianBetaNormConst β c 0 = 1 := by
  simp [gaussianBetaNormConst]

/-- At `n = 1`, the Mehta–Selberg constant is `√(2 * π / c)`, matching `N(0, c⁻¹)`. -/
theorem gaussianBetaNormConst_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    gaussianBetaNormConst β c 1 = Real.sqrt (2 * Real.pi / c) := by
  have hG : Real.Gamma (1 + β / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  unfold gaussianBetaNormConst
  simp only [Nat.cast_one, sub_self, mul_zero, zero_div, add_zero, Finset.Icc_self,
    Finset.prod_singleton, one_mul, div_self hG, mul_one]
  rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow, Real.div_rpow (by positivity) hc.le, one_div]
  ring

/-- Concrete GUE check (`n = 2, β = 2, c = 2`): `Z_{2, 2, 2} = π`. -/
theorem gaussianBetaNormConst_two_two : gaussianBetaNormConst 2 2 2 = Real.pi := by
  unfold gaussianBetaNormConst
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.prod_pair (by decide : (1 : ℕ) ≠ 2)]
  have hG2 : Real.Gamma (1 + (2 : ℝ) / 2) = 1 := by
    have : (1 : ℝ) + 2 / 2 = (1 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]; simp
  have hG3 : Real.Gamma (1 + 2 * (2 : ℝ) / 2) = 2 := by
    have : (1 : ℝ) + 2 * 2 / 2 = (2 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]; norm_num
  have hpow : (2 : ℝ) ^ (-((2 : ℝ) / 2 + 2 * 2 * (2 - 1) / 4)) = (4 : ℝ)⁻¹ := by
    have hexp : -((2 : ℝ) / 2 + 2 * 2 * (2 - 1) / 4) = ((-2 : ℤ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_intCast]; norm_num
  have hpi : (2 * Real.pi) ^ ((2 : ℝ) / 2) = 2 * Real.pi := by norm_num
  push_cast
  rw [hpow, hpi, one_mul, hG2, hG3]
  ring

/-- Concrete GOE check (`n = 2, β = 1, c = 1`): `Z_{2, 1, 1} = 4 * √π`. -/
theorem gaussianBetaNormConst_two_one : gaussianBetaNormConst 1 1 2 = 4 * Real.sqrt Real.pi := by
  unfold gaussianBetaNormConst
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.prod_pair (by decide : (1 : ℕ) ≠ 2)]
  have hG32 : Real.Gamma (1 + (1 : ℝ) / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [add_comm, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hG2 : Real.Gamma (1 + 2 * (1 : ℝ) / 2) = 1 := by
    have : (1 : ℝ) + 2 * 1 / 2 = (1 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]; simp
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  push_cast
  rw [Real.one_rpow, one_mul, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, one_mul,
    hG32, hG2]
  field_simp [hsqrt_ne]
  nlinarith [hsq]

/-- The real-valued Gaussian beta (Hermite beta) probability density on `ℝⁿ` with Dyson index `β`
and quadratic confinement `c`. Totalized to `0` when `β ≤ 0` or `c ≤ 0`. -/
def gaussianBetaPDFReal (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if 0 < β ∧ 0 < c then
    (gaussianBetaNormConst β c n)⁻¹ *
      Real.exp (-(c / 2) * ∑ i : Fin n, x i ^ 2) *
      vandermondeProd x ^ β
  else 0

/-- The `ℝ≥0∞`-valued Gaussian beta probability density on `ℝⁿ`. -/
def gaussianBetaPDF (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianBetaPDFReal β c x)

/-- The unordered Gaussian beta (Hermite beta) measure on `ℝⁿ`. For `β > 0` and `c > 0` it is a
probability measure; otherwise it is the zero measure. -/
def gaussianBetaMeasure (β c : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity (gaussianBetaPDF β c (n := n))

/-- The real-valued ordered Gaussian beta density on the strictly decreasing Weyl chamber
`{x : Fin n → ℝ | StrictAnti x}`, multiplied by `n!` so that it integrates to `1`. -/
def gaussianBetaOrderedPDFReal (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if StrictAnti x then (n.factorial : ℝ) * gaussianBetaPDFReal β c x else 0

/-- The `ℝ≥0∞`-valued ordered Gaussian beta density on `ℝⁿ`. -/
def gaussianBetaOrderedPDF (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianBetaOrderedPDFReal β c x)

/-- The ordered Gaussian beta measure on `ℝⁿ`, supported on `{x : Fin n → ℝ | StrictAnti x}`. -/
def gaussianBetaOrderedMeasure (β c : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity (gaussianBetaOrderedPDF β c (n := n))

/-- The extended Gaussian beta density is `ENNReal.ofReal` of the real density. -/
theorem gaussianBetaPDF_eq_ofReal (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    gaussianBetaPDF β c x = ENNReal.ofReal (gaussianBetaPDFReal β c x) := by rfl

/-- The extended ordered Gaussian beta density is `ENNReal.ofReal` of the real ordered density. -/
theorem gaussianBetaOrderedPDF_eq_ofReal (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    gaussianBetaOrderedPDF β c x = ENNReal.ofReal (gaussianBetaOrderedPDFReal β c x) := by rfl

/-- Unfolding `gaussianBetaMeasure` as a weighted Lebesgue measure. -/
theorem gaussianBetaMeasure_eq_withDensity (β c : ℝ) (n : ℕ) :
    gaussianBetaMeasure β c n = volume.withDensity (gaussianBetaPDF β c (n := n)) := by rfl

/-- Unfolding `gaussianBetaOrderedMeasure` as a weighted Lebesgue measure. -/
theorem gaussianBetaOrderedMeasure_eq_withDensity (β c : ℝ) (n : ℕ) :
    gaussianBetaOrderedMeasure β c n =
      volume.withDensity (gaussianBetaOrderedPDF β c (n := n)) := by rfl

/-- Formula for `gaussianBetaPDFReal` at positive parameters. -/
@[simp]
theorem gaussianBetaPDFReal_of_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {n : ℕ} (x : Fin n → ℝ) :
    gaussianBetaPDFReal β c x =
      (gaussianBetaNormConst β c n)⁻¹ *
        Real.exp (-(c / 2) * ∑ i : Fin n, x i ^ 2) *
        vandermondeProd x ^ β := by
  simp [gaussianBetaPDFReal, hβ, hc]

/-- `gaussianBetaPDFReal` vanishes when parameters are not both positive. -/
theorem gaussianBetaPDFReal_of_not_pos {β c : ℝ} (h : ¬(0 < β ∧ 0 < c)) {n : ℕ} (x : Fin n → ℝ) :
    gaussianBetaPDFReal β c x = 0 := by
  simp [gaussianBetaPDFReal, h]

/-- `gaussianBetaPDFReal` is nonnegative everywhere. -/
theorem gaussianBetaPDFReal_nonneg (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ gaussianBetaPDFReal β c x := by
  by_cases h : 0 < β ∧ 0 < c
  · rw [gaussianBetaPDFReal_of_pos h.1 h.2]
    have hZ := gaussianBetaNormConst_pos h.1 h.2 n
    have hv := vandermondeProd_nonneg x
    positivity
  · simp [gaussianBetaPDFReal_of_not_pos h]

/-- Formula for `gaussianBetaOrderedPDFReal` on strictly decreasing tuples. -/
@[simp]
theorem gaussianBetaOrderedPDFReal_of_strictAnti (β c : ℝ) {n : ℕ} {x : Fin n → ℝ}
    (hx : StrictAnti x) :
    gaussianBetaOrderedPDFReal β c x = (n.factorial : ℝ) * gaussianBetaPDFReal β c x := by
  simp [gaussianBetaOrderedPDFReal, hx]

/-- `gaussianBetaOrderedPDFReal` vanishes off the strictly decreasing Weyl chamber. -/
@[simp]
theorem gaussianBetaOrderedPDFReal_of_not_strictAnti (β c : ℝ) {n : ℕ} {x : Fin n → ℝ}
    (hx : ¬StrictAnti x) :
    gaussianBetaOrderedPDFReal β c x = 0 := by
  simp [gaussianBetaOrderedPDFReal, hx]

/-- `gaussianBetaOrderedPDF` vanishes off the strictly decreasing Weyl chamber. -/
@[simp]
theorem gaussianBetaOrderedPDF_of_not_strictAnti (β c : ℝ) {n : ℕ} {x : Fin n → ℝ}
    (hx : ¬StrictAnti x) :
    gaussianBetaOrderedPDF β c x = 0 := by
  rw [gaussianBetaOrderedPDF_eq_ofReal, gaussianBetaOrderedPDFReal_of_not_strictAnti β c hx,
    ENNReal.ofReal_zero]

/-- `gaussianBetaOrderedPDFReal` is nonnegative everywhere. -/
theorem gaussianBetaOrderedPDFReal_nonneg (β c : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ gaussianBetaOrderedPDFReal β c x := by
  by_cases hx : StrictAnti x
  · rw [gaussianBetaOrderedPDFReal_of_strictAnti β c hx]
    exact mul_nonneg (Nat.cast_nonneg _) (gaussianBetaPDFReal_nonneg β c x)
  · simp [hx]

/-- The strictly decreasing Weyl chamber `{x : Fin n → ℝ | StrictAnti x}` is open. -/
theorem isOpen_strictAnti_fin (n : ℕ) : IsOpen {x : Fin n → ℝ | StrictAnti x} := by
  cases n with
  | zero =>
      have heq : {x : Fin 0 → ℝ | StrictAnti x} = Set.univ := by
        ext x; simp [StrictAnti]
      rw [heq]
      exact isOpen_univ
  | succ m =>
      have heq : {x : Fin (m + 1) → ℝ | StrictAnti x} =
          ⋂ k : Fin m, {x | x k.succ < x k.castSucc} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Fin.strictAnti_iff_succ_lt]
      rw [heq]
      exact isOpen_iInter_of_finite fun k =>
        isOpen_lt (continuous_apply k.succ) (continuous_apply k.castSucc)

/-- `gaussianBetaPDFReal` is measurable. -/
@[fun_prop]
theorem measurable_gaussianBetaPDFReal (β c : ℝ) (n : ℕ) :
    Measurable (gaussianBetaPDFReal β c (n := n)) := by
  unfold gaussianBetaPDFReal
  by_cases h : 0 < β ∧ 0 < c
  · simp only [ite_eq_left h]
    fun_prop
  · simp only [ite_eq_right h]
    exact measurable_const

/-- `gaussianBetaPDF` is measurable. -/
@[fun_prop]
theorem measurable_gaussianBetaPDF (β c : ℝ) (n : ℕ) :
    Measurable (gaussianBetaPDF β c (n := n)) :=
  (measurable_gaussianBetaPDFReal β c n).ennreal_ofReal

/-- `gaussianBetaOrderedPDFReal` is measurable. -/
@[fun_prop]
theorem measurable_gaussianBetaOrderedPDFReal (β c : ℝ) (n : ℕ) :
    Measurable (gaussianBetaOrderedPDFReal β c (n := n)) := by
  have heq : gaussianBetaOrderedPDFReal β c (n := n) =
      {x : Fin n → ℝ | StrictAnti x}.indicator
        (fun x => (n.factorial : ℝ) * gaussianBetaPDFReal β c x) := by
    funext x
    by_cases hx : StrictAnti x <;> simp [gaussianBetaOrderedPDFReal, hx]
  rw [heq]
  exact ((measurable_gaussianBetaPDFReal β c n).const_mul _).indicator
    (isOpen_strictAnti_fin n).measurableSet

/-- `gaussianBetaOrderedPDF` is measurable. -/
@[fun_prop]
theorem measurable_gaussianBetaOrderedPDF (β c : ℝ) (n : ℕ) :
    Measurable (gaussianBetaOrderedPDF β c (n := n)) :=
  (measurable_gaussianBetaOrderedPDFReal β c n).ennreal_ofReal

/-- `gaussianBetaPDFReal` is invariant under coordinate permutations. -/
theorem gaussianBetaPDFReal_comp_perm (β c : ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    gaussianBetaPDFReal β c (x ∘ σ) = gaussianBetaPDFReal β c x := by
  by_cases h : 0 < β ∧ 0 < c
  · rw [gaussianBetaPDFReal_of_pos h.1 h.2, gaussianBetaPDFReal_of_pos h.1 h.2,
      vandermondeProd_comp_perm]
    have hsum : ∑ i : Fin n, (x ∘ σ) i ^ 2 = ∑ i : Fin n, x i ^ 2 :=
      Equiv.sum_comp σ (fun i => x i ^ 2)
    rw [hsum]
  · rw [gaussianBetaPDFReal_of_not_pos h, gaussianBetaPDFReal_of_not_pos h]

/-- `gaussianBetaPDF` is invariant under coordinate permutations. -/
theorem gaussianBetaPDF_comp_perm (β c : ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    gaussianBetaPDF β c (x ∘ σ) = gaussianBetaPDF β c x := by
  rw [gaussianBetaPDF_eq_ofReal, gaussianBetaPDF_eq_ofReal, gaussianBetaPDFReal_comp_perm]

/-- The unordered Gaussian beta measure is invariant under coordinate permutations. -/
theorem map_comp_perm_gaussianBetaMeasure (β c : ℝ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (gaussianBetaMeasure β c n).map (fun x => x ∘ σ) = gaussianBetaMeasure β c n := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ.symm
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => x ∘ σ := by
    funext x i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hmp : (volume : Measure (Fin n → ℝ)).map e = volume :=
    (measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ.symm).map_eq
  rw [gaussianBetaMeasure, ← he, MeasurableEquiv.map_withDensity, hmp]
  congr 1
  funext y
  have hsymm : e.symm y = y ∘ σ.symm := by
    funext i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [hsymm, gaussianBetaPDF_comp_perm]

/-! ### Scaling covariance of the Gaussian beta laws -/

/-- Pushing `volume.withDensity g` forward under `x ↦ s • x` (`s > 0`) rescales by `s ^ (-n)`. -/
private theorem map_smul_volume_withDensity {n : ℕ} {s : ℝ} (hs : 0 < s)
    (g : (Fin n → ℝ) → ℝ≥0∞) :
    (volume.withDensity g).map (fun x : Fin n → ℝ => s • x) =
      volume.withDensity fun y => ENNReal.ofReal ((s ^ n)⁻¹) * g (s⁻¹ • y) := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 hs.ne').unit).toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => s • x := rfl
  have hsymm : ∀ y, e.symm y = s⁻¹ • y := fun y => by
    simp [e, Units.smul_def]
  rw [← he, MeasurableEquiv.map_withDensity, he, Measure.map_addHaar_smul volume hs.ne',
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos hs n))]
  exact congrArg volume.withDensity (funext fun y => by
    simp only [hsymm, Pi.smul_apply, smul_eq_mul])

/-- Pointwise scaling identity for `gaussianBetaPDFReal`. -/
private theorem gaussianBetaPDFReal_smul_inv {β c s : ℝ} (hβ : 0 < β) (hc : 0 < c) (hs : 0 < s)
    {n : ℕ} (y : Fin n → ℝ) :
    (s ^ n)⁻¹ * gaussianBetaPDFReal β c (s⁻¹ • y) = gaussianBetaPDFReal β (c / s ^ 2) y := by
  have hc' : 0 < c / s ^ 2 := div_pos hc (pow_pos hs 2)
  rw [gaussianBetaPDFReal_of_pos hβ hc, gaussianBetaPDFReal_of_pos hβ hc',
    vandermondeProd_smul, abs_of_pos (inv_pos.mpr hs),
    Real.mul_rpow (by positivity) (vandermondeProd_nonneg y)]
  have hexp :
      -(c / 2) * ∑ i : Fin n, (s⁻¹ • y) i ^ 2 = -(c / s ^ 2 / 2) * ∑ i : Fin n, y i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    ring
  have hcard : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have hmul : (n * (n - 1) / 2) * 2 = n * (n - 1) := by
      rw [← Finset.sum_range_id, Finset.sum_range_id_mul_two]
    cases n with
    | zero => simp
    | succ m =>
        have h := congrArg (Nat.cast (R := ℝ)) hmul
        simp only [Nat.cast_mul, Nat.add_sub_cancel, Nat.cast_ofNat] at h
        push_cast at h ⊢
        linarith
  have hZ : gaussianBetaNormConst β (c / s ^ 2) n =
      s ^ ((n : ℝ) + β * n * ((n : ℝ) - 1) / 2) * gaussianBetaNormConst β c n := by
    unfold gaussianBetaNormConst
    rw [Real.div_rpow hc.le (pow_nonneg hs.le 2), div_eq_inv_mul,
      ← Real.rpow_neg (pow_nonneg hs.le 2), neg_neg, ← Real.rpow_natCast s 2,
      ← Real.rpow_mul hs.le]
    have hpow : (2 : ℝ) * ((n : ℝ) / 2 + β * n * ((n : ℝ) - 1) / 4) =
        (n : ℝ) + β * n * ((n : ℝ) - 1) / 2 := by ring
    rw [Nat.cast_ofNat, hpow]
    ring
  have hspow : (s ^ n)⁻¹ * ((s⁻¹) ^ (n * (n - 1) / 2)) ^ β =
      (s ^ ((n : ℝ) + β * n * ((n : ℝ) - 1) / 2))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast s n, ← Real.rpow_natCast s (n * (n - 1) / 2),
      Real.inv_rpow (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le, hcard, ← mul_inv,
      ← Real.rpow_add hs]
    congr 2; ring
  rw [hexp, hZ, mul_inv]
  calc (s ^ n)⁻¹ * ((gaussianBetaNormConst β c n)⁻¹ *
        Real.exp (-(c / s ^ 2 / 2) * ∑ i : Fin n, y i ^ 2) *
        (((s⁻¹) ^ (n * (n - 1) / 2)) ^ β * vandermondeProd y ^ β))
      = ((s ^ n)⁻¹ * ((s⁻¹) ^ (n * (n - 1) / 2)) ^ β) * (gaussianBetaNormConst β c n)⁻¹ *
          Real.exp (-(c / s ^ 2 / 2) * ∑ i : Fin n, y i ^ 2) * vandermondeProd y ^ β := by ring
    _ = (s ^ ((n : ℝ) + β * n * ((n : ℝ) - 1) / 2))⁻¹ * (gaussianBetaNormConst β c n)⁻¹ *
          Real.exp (-(c / s ^ 2 / 2) * ∑ i : Fin n, y i ^ 2) * vandermondeProd y ^ β := by
        rw [hspow]
    _ = _ := by ring

/-- Scaling a Gaussian beta law by `s > 0` divides its confinement parameter `c` by `s ^ 2`. -/
theorem map_smul_gaussianBetaMeasure {β c s : ℝ} (hβ : 0 < β) (hc : 0 < c) (hs : 0 < s) (n : ℕ) :
    (gaussianBetaMeasure β c n).map (fun x => s • x) = gaussianBetaMeasure β (c / s ^ 2) n := by
  rw [gaussianBetaMeasure, gaussianBetaMeasure, map_smul_volume_withDensity hs]
  congr 1
  funext y
  rw [gaussianBetaPDF_eq_ofReal, gaussianBetaPDF_eq_ofReal,
    ← ENNReal.ofReal_mul (by positivity), gaussianBetaPDFReal_smul_inv hβ hc hs]

/-- Scaling an ordered Gaussian beta law by `s > 0` divides its confinement `c` by `s ^ 2`. -/
theorem map_smul_gaussianBetaOrderedMeasure {β c s : ℝ} (hβ : 0 < β) (hc : 0 < c) (hs : 0 < s)
    (n : ℕ) :
    (gaussianBetaOrderedMeasure β c n).map (fun x => s • x) =
      gaussianBetaOrderedMeasure β (c / s ^ 2) n := by
  rw [gaussianBetaOrderedMeasure, gaussianBetaOrderedMeasure, map_smul_volume_withDensity hs]
  congr 1
  funext y
  have hiff : StrictAnti (s⁻¹ • y) ↔ StrictAnti y := by
    constructor
    · intro h i j hij
      have := h hij
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact (mul_lt_mul_iff_right₀ (inv_pos.mpr hs)).mp this
    · intro h i j hij
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_lt_mul_of_pos_left (h hij) (inv_pos.mpr hs)
  rw [gaussianBetaOrderedPDF_eq_ofReal, gaussianBetaOrderedPDF_eq_ofReal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  by_cases hy : StrictAnti y
  · rw [gaussianBetaOrderedPDFReal_of_strictAnti _ _ (hiff.mpr hy),
      gaussianBetaOrderedPDFReal_of_strictAnti _ _ hy]
    calc (s ^ n)⁻¹ * ((n.factorial : ℝ) * gaussianBetaPDFReal β c (s⁻¹ • y))
        = (n.factorial : ℝ) * ((s ^ n)⁻¹ * gaussianBetaPDFReal β c (s⁻¹ • y)) := by ring
      _ = (n.factorial : ℝ) * gaussianBetaPDFReal β (c / s ^ 2) y := by
          rw [gaussianBetaPDFReal_smul_inv hβ hc hs]
  · rw [gaussianBetaOrderedPDFReal_of_not_strictAnti _ _ (mt hiff.mp hy),
      gaussianBetaOrderedPDFReal_of_not_strictAnti _ _ hy, mul_zero]

end Probability

end TauCeti
