/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Complex.NormSq
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Gaussian orthogonal and unitary ensembles

The matrix `gaussianEnsemble β n g` built from an array `g` of reals: for `β = 1` the real
symmetric matrix with entries `g (i, j)` above the diagonal and `√2 * g (i, i)` on it, and
otherwise the Hermitian matrix with entries `(g (i, j) + I * g (j, i)) / √2` above the diagonal
and `g (i, i)` on it, all divided by `√n`. With independent standard Gaussian entries this is the
GOE (`β = 1`) or the GUE (`β = 2`). Realizations are Wigner matrices
(`TauCeti.wignerMatrix`), which gives the Hermitian property and the second-moment computation.

## Main definitions

* `TauCeti.Probability.gaussianEnsemble`: the matrix built from the array `g`.
* `TauCeti.Probability.gaussianEnsembleSelfAdjointCLM`: continuous `ℝ`-linear map bundling
  `gaussianEnsemble β n` into `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`.

## Main results

* `TauCeti.Probability.isHermitian_gaussianEnsemble` and
  `TauCeti.Probability.isSymm_gaussianEnsemble_of_eq_one`: Hermitian and (`β = 1`) symmetric
  structure.
* `TauCeti.Probability.im_gaussianEnsemble_one`,
  `TauCeti.Probability.im_gaussianEnsemble_of_lt_of_ne_one`, and
  `TauCeti.Probability.gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one`: imaginary-part and
  `β ≠ 1` entry properties.
* `TauCeti.Probability.gaussianEnsemble_add` and `TauCeti.Probability.gaussianEnsemble_smul`: the
  matrix is real-linear in the array.
* `TauCeti.Probability.continuous_gaussianEnsemble`: it depends continuously on the array.
* `TauCeti.Probability.sum_gaussianEnsemble_single_mul_mul_self_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_single_mul_mul_self_of_eq_one`: quadratic Casimir
  identities over the standard coordinate basis `Pi.single p 1`.
* `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_single_mul_of_ne_one`,
  `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_single_mul_of_eq_one`,
  `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_mul_of_ne_one`, and
  `TauCeti.Probability.sum_re_trace_mul_gaussianEnsemble_single_mul_of_eq_one`: trace inner-product
  identities over the coordinate basis.
* `TauCeti.Probability.hasLaw_gaussianEnsemble`: with independent `N(0, v)` coordinates the
  ensemble has the law of `√v` times the ensemble of standard Gaussian coordinates.
* `TauCeti.Probability.gaussianEnsemble_one_zero_zero_hasLaw` and
  `TauCeti.Probability.gaussianEnsemble_two_zero_zero_hasLaw`: the laws of the `1 × 1` ensembles,
  `N(0, 2)` and `N(0, 1)`.
* `TauCeti.Probability.integral_re_trace_gaussianEnsemble_one_sq_div` and
  `TauCeti.Probability.integral_re_trace_gaussianEnsemble_two_sq_div`: the normalized trace of
  the square has expectation `1 + 1 / n` for the GOE and `1` for the GUE.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5 and §4.3.1.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.6 and §3.1.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory

namespace TauCeti

namespace Probability

/-- The array `g`, extended to `ℕ × ℕ` by its `(0, 0)` entry outside its `n × n` corner when
`n > 0`, and by `1` when `n = 0`. -/
private def extendArray {Ω : Type*} (n : ℕ) (g : Fin n × Fin n → Ω → ℝ) (p : ℕ × ℕ)
    (ω : Ω) : ℝ :=
  if h : p.1 < n ∧ p.2 < n then g (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) ω
  else if hn : 0 < n then g (⟨0, hn⟩, ⟨0, hn⟩) ω else 1

private theorem extendArray_apply {Ω : Type*} {n : ℕ} (g : Fin n × Fin n → Ω → ℝ) (i j : Fin n)
    (ω : Ω) : extendArray n g (i.val, j.val) ω = g (i, j) ω := by
  simp [extendArray, i.isLt, j.isLt]

/-- The above-diagonal entries of the Wigner matrix equal to `gaussianEnsemble β n`. -/
private def ensembleUpper {Ω : Type*} (β n : ℕ) (g : Fin n × Fin n → Ω → ℝ) :
    StrictUpper → Ω → ℂ := fun ij ω ↦
  if β = 1 then (extendArray n g ij.val ω : ℂ)
  else ((extendArray n g ij.val ω : ℂ) + Complex.I * extendArray n g (ij.val.2, ij.val.1) ω) /
    (Real.sqrt 2 : ℝ)

/-- The diagonal entries of the Wigner matrix equal to `gaussianEnsemble β n`. -/
private def ensembleDiag {Ω : Type*} (β n : ℕ) (g : Fin n × Fin n → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun i ω ↦ if β = 1 then Real.sqrt 2 * extendArray n g (i, i) ω else extendArray n g (i, i) ω

/-- The Gaussian ensemble built from the array `g`: for `β = 1` the real symmetric matrix with
entries `g (i, j)` for `i < j` and `√2 * g (i, i)` on the diagonal, and otherwise the Hermitian
matrix with entries `(g (i, j) + I * g (j, i)) / √2` for `i < j` and `g (i, i)` on the diagonal,
all divided by `√n`. With independent standard Gaussian entries this is the GOE (`β = 1`) or the
GUE (`β = 2`). -/
def gaussianEnsemble (β n : ℕ) (g : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  wignerMatrix (ensembleUpper β n (fun p _ ↦ g p))
    (ensembleDiag β n (fun p _ ↦ g p)) n ()

section Entries

variable {β n : ℕ} (g : Fin n × Fin n → ℝ)

/-- Entry formula for `gaussianEnsemble`, with the common factor `1 / √n` outside the cases.
For `β = 1`, diagonal entries use `√2 * g (i, i)` and off-diagonal entries use the corresponding
upper-triangular sample symmetrically. For `β ≠ 1`, the diagonal is `g (i, i)`, the upper entries
are `(g (i, j) + I * g (j, i)) / √2`, and the lower entries are their complex conjugates. -/
theorem gaussianEnsemble_apply (i j : Fin n) :
    gaussianEnsemble β n g i j = ((Real.sqrt n)⁻¹ : ℂ) *
      if β = 1 then
        if i = j then ((Real.sqrt 2 * g (i, i) : ℝ) : ℂ)
        else if i < j then (g (i, j) : ℂ) else (g (j, i) : ℂ)
      else
        if i = j then (g (i, i) : ℂ)
        else if i < j then ((g (i, j) : ℂ) + Complex.I * g (j, i)) / (Real.sqrt 2 : ℝ)
        else ((g (j, i) : ℂ) - Complex.I * g (i, j)) /         (Real.sqrt 2 : ℝ) := by
  rw [gaussianEnsemble]
  rcases lt_trichotomy i j with h | h | h
  · rw [wignerMatrix_apply_of_lt _ _ _ h]
    by_cases hβ : β = 1 <;>
      simp [ensembleUpper, extendArray_apply, h, h.ne, hβ]
  · subst j
    rw [wignerMatrix_apply_self]
    by_cases hβ : β = 1 <;> simp [ensembleDiag, extendArray_apply, hβ]
  · rw [wignerMatrix_apply_of_gt _ _ _ h]
    by_cases hβ : β = 1 <;>
      simp [ensembleUpper, extendArray_apply, h.not_gt, h.ne', sub_eq_add_neg, hβ,
        Complex.conj_ofReal]

/-- The diagonal entries of the `β = 1` ensemble are `√2 * g (i, i) / √n`. -/
@[simp]
theorem gaussianEnsemble_apply_self_of_eq_one (hβ : β = 1) (i : Fin n) :
    gaussianEnsemble β n g i i = ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt 2 * g (i, i) : ℝ) : ℂ) := by
  simp [gaussianEnsemble_apply, hβ]

/-- Above the diagonal the `β = 1` ensemble has entries `g (i, j) / √n`. -/
@[simp]
theorem gaussianEnsemble_apply_of_lt_of_eq_one (hβ : β = 1) {i j : Fin n} (h : i < j) :
    gaussianEnsemble β n g i j = ((Real.sqrt n)⁻¹ : ℂ) * (g (i, j) : ℂ) := by
  simp [gaussianEnsemble_apply, hβ, h, h.ne]

/-- Below the diagonal the `β = 1` ensemble has entries `g (j, i) / √n`. -/
@[simp]
theorem gaussianEnsemble_apply_of_gt_of_eq_one (hβ : β = 1) {i j : Fin n} (h : j < i) :
    gaussianEnsemble β n g i j = ((Real.sqrt n)⁻¹ : ℂ) * (g (j, i) : ℂ) := by
  simp [gaussianEnsemble_apply, hβ, h.not_gt, h.ne']

/-- The diagonal entries of the `β ≠ 1` ensemble are `g (i, i) / √n`. -/
@[simp]
theorem gaussianEnsemble_apply_self_of_ne_one (hβ : β ≠ 1) (i : Fin n) :
    gaussianEnsemble β n g i i = ((Real.sqrt n)⁻¹ : ℂ) * (g (i, i) : ℂ) := by
  simp [gaussianEnsemble_apply, hβ]

/-- Above the diagonal the `β ≠ 1` ensemble has entries `(g (i, j) + I * g (j, i)) / √(2n)`. -/
@[simp]
theorem gaussianEnsemble_apply_of_lt_of_ne_one (hβ : β ≠ 1) {i j : Fin n} (h : i < j) :
    gaussianEnsemble β n g i j = ((Real.sqrt n)⁻¹ : ℂ) *
      (((g (i, j) : ℂ) + Complex.I * g (j, i)) / (Real.sqrt 2 : ℝ)) := by
  simp [gaussianEnsemble_apply, hβ, h, h.ne]

/-- Below the diagonal the `β ≠ 1` ensemble has entries `(g (j, i) - I * g (i, j)) / √(2n)`. -/
@[simp]
theorem gaussianEnsemble_apply_of_gt_of_ne_one (hβ : β ≠ 1) {i j : Fin n} (h : j < i) :
    gaussianEnsemble β n g i j = ((Real.sqrt n)⁻¹ : ℂ) *
      (((g (j, i) : ℂ) - Complex.I * g (i, j)) / (Real.sqrt 2 : ℝ)) := by
  simp [gaussianEnsemble_apply, hβ, h.not_gt, h.ne']

end Entries

section Linear

variable {β n : ℕ}

/-- The Gaussian ensemble is additive in the array. -/
@[simp]
theorem gaussianEnsemble_add (g h : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (g + h) = gaussianEnsemble β n g + gaussianEnsemble β n h := by
  ext i j
  simp only [gaussianEnsemble_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring

/-- The Gaussian ensemble is homogeneous in the array for real scalars. -/
@[simp]
theorem gaussianEnsemble_smul (c : ℝ) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (c • g) = c • gaussianEnsemble β n g := by
  ext i j
  simp only [gaussianEnsemble_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
    Complex.real_smul]
  split_ifs <;> push_cast <;> ring

/-- The Gaussian ensemble of the zero array is zero. -/
@[simp]
theorem gaussianEnsemble_zero : gaussianEnsemble β n 0 = 0 := by
  simpa using gaussianEnsemble_smul (β := β) 0 (0 : Fin n × Fin n → ℝ)

/-- The Gaussian ensemble commutes with negation in the array. -/
@[simp]
theorem gaussianEnsemble_neg (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (-g) = -gaussianEnsemble β n g := by
  simpa using gaussianEnsemble_smul (β := β) (-1 : ℝ) g

/-- The Gaussian ensemble is subtractive in the array. -/
@[simp]
theorem gaussianEnsemble_sub (g h : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n (g - h) = gaussianEnsemble β n g - gaussianEnsemble β n h := by
  ext i j
  simp only [gaussianEnsemble_apply, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> push_cast <;> ring

/-- The Gaussian ensemble depends continuously on the array. -/
@[fun_prop]
theorem continuous_gaussianEnsemble : Continuous (gaussianEnsemble β n) := by
  refine continuous_matrix fun i j ↦ ?_
  simp only [gaussianEnsemble_apply]
  split_ifs <;> fun_prop

/-- The Gaussian ensemble is a measurable function of the array. -/
@[fun_prop]
theorem measurable_gaussianEnsemble : Measurable (gaussianEnsemble β n) :=
  continuous_gaussianEnsemble.measurable

end Linear

/-- **The law of a Gaussian ensemble with independent `N(0, v)` coordinates.** If the coordinates
`g (i, j)` are independent with law `N(0, v)`, the ensemble has the law of `√v` times the ensemble
of independent standard Gaussian coordinates: `√v` times the GOE (`β = 1`) or GUE (`β = 2`). -/
theorem hasLaw_gaussianEnsemble {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (β : ℕ) {n : ℕ} {g : Fin n × Fin n → Ω → ℝ} {v : NNReal}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P) :
    HasLaw (fun ω ↦ gaussianEnsemble β n (fun ij ↦ g ij ω))
      ((Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map
        fun x ↦ Real.sqrt v • gaussianEnsemble β n x) P := by
  have hv : gaussianReal 0 v = (gaussianReal 0 1).map (Real.sqrt v * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr
    exact NNReal.eq (Real.sq_sqrt v.property).symm
  have hpi : Measure.pi (fun _ : Fin n × Fin n ↦ gaussianReal 0 v) =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (Real.sqrt v • ·) := by
    rw [hv, ← Measure.pi_map_pi fun _ ↦ by fun_prop]
    -- scalar multiplication on arrays is coordinatewise multiplication
    rfl
  have hlaw := (⟨by fun_prop, rfl⟩ : HasLaw (gaussianEnsemble β n) _ _).comp (hindep.hasLaw_pi hg)
  rw [hpi, Measure.map_map (by fun_prop) (by fun_prop)] at hlaw
  simpa [Function.comp_def, gaussianEnsemble_smul] using hlaw

/-- A sampled Gaussian ensemble is the corresponding Wigner matrix with its entry functions. -/
private theorem gaussianEnsemble_eq_wignerMatrix {Ω : Type*} (β n : ℕ)
    (g : Fin n × Fin n → Ω → ℝ) (ω : Ω) :
    gaussianEnsemble β n (fun p ↦ g p ω) =
      wignerMatrix (ensembleUpper β n g) (ensembleDiag β n g) n ω := by
  rw [gaussianEnsemble]
  apply wignerMatrix_congr
  · intro ij hij
    simp [ensembleUpper, extendArray, hij]
  · intro i hi
    simp [ensembleDiag, extendArray, hi]

/-- The Gaussian ensemble is Hermitian for every array. -/
theorem isHermitian_gaussianEnsemble (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsemble β n g).IsHermitian := by
  have := gaussianEnsemble_eq_wignerMatrix β n (fun p (_ : Unit) ↦ g p) ()
  rw [this]
  exact wignerMatrix_isHermitian _ _ _ n

/-- Every entry of the `β = 1` Gaussian ensemble has zero imaginary part. -/
@[simp] theorem im_gaussianEnsemble_one {n : ℕ} (g : Fin n × Fin n → ℝ) (i j : Fin n) :
    (gaussianEnsemble 1 n g i j).im = 0 := by
  rcases lt_trichotomy i j with h | rfl | h <;>
    simp [*, ← Complex.ofReal_inv, ← Complex.ofReal_mul]

/-- Above the diagonal, the `β ≠ 1` Gaussian ensemble has imaginary part `g (j, i) / √(2n)`. -/
theorem im_gaussianEnsemble_of_lt_of_ne_one {β n : ℕ} (g : Fin n × Fin n → ℝ) (hβ : β ≠ 1)
    {i j : Fin n} (h : i < j) :
    (gaussianEnsemble β n g i j).im = (Real.sqrt n)⁻¹ * ((Real.sqrt 2)⁻¹ * g (j, i)) := by
  rw [gaussianEnsemble_apply_of_lt_of_ne_one g hβ h, ← Complex.ofReal_inv, div_eq_mul_inv,
    ← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]; ring

/-- For `β = 2` and `n = 2`, the imaginary part of the `(0, 1)` entry is `g (1, 0) / 2`. -/
theorem im_gaussianEnsemble_two_zero_one (g : Fin 2 × Fin 2 → ℝ) :
    (gaussianEnsemble 2 2 g 0 1).im = g (1, 0) / 2 := by
  rw [im_gaussianEnsemble_of_lt_of_ne_one g (by decide) (by decide : (0 : Fin 2) < 1),
    Nat.cast_ofNat, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), div_eq_inv_mul]

/-- All `β ≠ 1` branches of `TauCeti.Probability.gaussianEnsemble` coincide with `β = 2`. -/
theorem gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (g : Fin n × Fin n → ℝ) : gaussianEnsemble β n g = gaussianEnsemble 2 n g := by
  ext i j; rw [gaussianEnsemble_apply, gaussianEnsemble_apply, ite_eq_right hβ,
    ite_eq_right (by decide : (2 : ℕ) ≠ 1)]

/-- For `n = 1` and `β = 1`, the single entry `√2 * g (0, 0)` of the ensemble is `N(0, 2)` when
`g (0, 0)` is a standard Gaussian. -/
theorem gaussianEnsemble_one_zero_zero_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (g : Fin 1 × Fin 1 → Ω → ℝ) (hg : HasLaw (g (0, 0)) (gaussianReal 0 1) μ) :
    HasLaw (fun ω ↦ (gaussianEnsemble 1 1 (fun p ↦ g p ω) 0 0).re)
      (gaussianReal 0 2) μ := by
  have e : (fun ω ↦ (gaussianEnsemble 1 1 (fun p ↦ g p ω) 0 0).re) =
      fun ω ↦ Real.sqrt 2 * g (0, 0) ω := by
    funext ω
    simp [Real.sqrt_one]
  have h : HasLaw (fun ω ↦ Real.sqrt 2 * g (0, 0) ω) (gaussianReal (Real.sqrt 2 * 0)
      (NNReal.mk (Real.sqrt 2 ^ 2) (sq_nonneg _) * 1)) μ := gaussianReal_const_mul hg (Real.sqrt 2)
  rw [e]
  convert h using 2
  · simp
  · rw [mul_one]
    exact NNReal.eq (Real.sq_sqrt (by norm_num)).symm

/-- For `n = 1` and `β = 2`, the single entry `g (0, 0)` of the ensemble is `N(0, 1)` when
`g (0, 0)` is a standard Gaussian. -/
theorem gaussianEnsemble_two_zero_zero_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (g : Fin 1 × Fin 1 → Ω → ℝ) (hg : HasLaw (g (0, 0)) (gaussianReal 0 1) μ) :
    HasLaw (fun ω ↦ (gaussianEnsemble 2 1 (fun p ↦ g p ω) 0 0).re)
      (gaussianReal 0 1) μ := by
  have e : (fun ω ↦ (gaussianEnsemble 2 1 (fun p ↦ g p ω) 0 0).re) = g (0, 0) := by
    funext ω
    simp [Real.sqrt_one]
  rwa [e]

private theorem integral_re_trace_gaussianEnsemble_sq_div_of_wigner {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {σ2 s : ℝ} (β n : ℕ) (g : Fin n × Fin n → Ω → ℝ)
    (hξi : ∀ ij, Integrable (fun ω ↦ ‖ensembleUpper β n g ij ω‖ ^ 2) μ)
    (hξ : ∀ ij, ∫ ω, ‖ensembleUpper β n g ij ω‖ ^ 2 ∂μ = s)
    (hηi : ∀ i, Integrable (fun ω ↦ ensembleDiag β n g i ω ^ 2) μ)
    (hη : ∀ i, ∫ ω, ensembleDiag β n g i ω ^ 2 ∂μ = σ2) :
    ∫ ω, (gaussianEnsemble β n (fun p ↦ g p ω) ^ 2).trace.re / n ∂μ =
      (σ2 + (n - 1) * s) / n := by
  rw [← integral_re_trace_wignerMatrix_mul_self hξi hξ hηi hη n]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [gaussianEnsemble_eq_wignerMatrix, sq]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]

/-- The moments of the extended array, given those of the entries `g p` with `R p`. -/
private theorem extendArray_sq_moments {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} (hn : 0 < n) (g : Fin n × Fin n → Ω → ℝ) (R : Fin n × Fin n → Prop)
    (hint : ∀ p, R p → Integrable (fun ω ↦ g p ω ^ 2) μ)
    (hvar : ∀ p, R p → ∫ ω, g p ω ^ 2 ∂μ = 1)
    (hint00 : Integrable (fun ω ↦ g ((⟨0, hn⟩ : Fin n), ⟨0, hn⟩) ω ^ 2) μ)
    (hvar00 : ∫ ω, g ((⟨0, hn⟩ : Fin n), ⟨0, hn⟩) ω ^ 2 ∂μ = 1) (p : ℕ × ℕ)
    (hp : ∀ h : p.1 < n ∧ p.2 < n, R (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)) :
    Integrable (fun ω ↦ extendArray n g p ω ^ 2) μ ∧ ∫ ω, extendArray n g p ω ^ 2 ∂μ = 1 := by
  by_cases h : p.1 < n ∧ p.2 < n
  · simp only [extendArray, h, and_self, ↓reduceDIte]
    exact ⟨hint _ (hp h), hvar _ (hp h)⟩
  · simp [extendArray, h, hn, hint00, hvar00]

/-- The GOE has `E trₙ H² = 1 + 1 / n`, where `trₙ = n⁻¹ tr`: it suffices that the entries
`g (i, j)` with `i ≤ j` have second moment `1`. The diagonal entries of the ensemble have second
moment `2 / n` and the off-diagonal ones `1 / n`. -/
theorem integral_re_trace_gaussianEnsemble_one_sq_div {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {n : ℕ} (hn : 0 < n) (g : Fin n × Fin n → Ω → ℝ)
    (hint : ∀ i j, i ≤ j → Integrable (fun ω ↦ g (i, j) ω ^ 2) μ)
    (hvar : ∀ i j, i ≤ j → ∫ ω, g (i, j) ω ^ 2 ∂μ = 1) :
    ∫ ω, (gaussianEnsemble 1 n (fun p ↦ g p ω) ^ 2).trace.re / n ∂μ = 1 + 1 / n := by
  have hm := extendArray_sq_moments hn g (fun p ↦ p.1 ≤ p.2)
    (fun p hp ↦ hint p.1 p.2 hp) (fun p hp ↦ hvar p.1 p.2 hp)
    (hint ⟨0, hn⟩ ⟨0, hn⟩ le_rfl) (hvar ⟨0, hn⟩ ⟨0, hn⟩ le_rfl)
  have hξ (ij : StrictUpper) :
      ∀ ω, ‖ensembleUpper 1 n g ij ω‖ ^ 2 = extendArray n g ij.val ω ^ 2 := by
    intro ω
    simp [ensembleUpper]
  have hη (i : ℕ) : ∀ ω, ensembleDiag 1 n g i ω ^ 2 = 2 * extendArray n g (i, i) ω ^ 2 := by
    intro ω
    simp [ensembleDiag, mul_pow]
  have hd (i : ℕ) := hm (i, i) fun _ ↦ le_rfl
  have hu (ij : StrictUpper) := hm ij.val fun h ↦ (Fin.mk_le_mk.2 ij.property.le)
  rw [integral_re_trace_gaussianEnsemble_sq_div_of_wigner (σ2 := 2) (s := 1) 1 n g
    (fun ij ↦ by simp only [hξ]; exact (hu ij).1)
    (fun ij ↦ by simp only [hξ]; exact (hu ij).2)
    (fun i ↦ by simp only [hη]; exact (hd i).1.const_mul 2)
    (fun i ↦ by simp only [hη, integral_const_mul, (hd i).2]; norm_num)]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The GUE has `E trₙ H² = 1`, where `trₙ = n⁻¹ tr`: it suffices that the entries of `g` have
second moment `1`. -/
theorem integral_re_trace_gaussianEnsemble_two_sq_div {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {n : ℕ} (hn : 0 < n) (g : Fin n × Fin n → Ω → ℝ)
    (hint : ∀ p, Integrable (fun ω ↦ g p ω ^ 2) μ) (hvar : ∀ p, ∫ ω, g p ω ^ 2 ∂μ = 1) :
    ∫ ω, (gaussianEnsemble 2 n (fun p ↦ g p ω) ^ 2).trace.re / n ∂μ = 1 := by
  have hm := extendArray_sq_moments hn g (fun _ ↦ True) (fun p _ ↦ hint p)
    (fun p _ ↦ hvar p) (hint (⟨0, hn⟩, ⟨0, hn⟩)) (hvar (⟨0, hn⟩, ⟨0, hn⟩))
  have hξ (ij : StrictUpper) : ∀ ω, ‖ensembleUpper 2 n g ij ω‖ ^ 2 =
      (extendArray n g ij.val ω ^ 2 + extendArray n g (ij.val.2, ij.val.1) ω ^ 2) / 2 := by
    intro ω
    simpa [ensembleUpper] using Complex.norm_sq_add_I_mul_div_sqrt_two _ _
  have hη (i : ℕ) : ∀ ω, ensembleDiag 2 n g i ω ^ 2 = extendArray n g (i, i) ω ^ 2 := by
    intro ω
    simp [ensembleDiag]
  have hd (i : ℕ) := hm (i, i) fun _ ↦ trivial
  have hu (ij : StrictUpper) := hm ij.val fun _ ↦ trivial
  have hu' (ij : StrictUpper) := hm (ij.val.2, ij.val.1) fun _ ↦ trivial
  rw [integral_re_trace_gaussianEnsemble_sq_div_of_wigner (σ2 := 1) (s := 1) 2 n g
    (fun ij ↦ by simp only [hξ]; exact ((hu ij).1.add (hu' ij).1).div_const 2)
    (fun ij ↦ by
      simp only [hξ]
      rw [integral_div, integral_add (hu ij).1 (hu' ij).1, (hu ij).2, (hu' ij).2]
      norm_num)
    (fun i ↦ by simp only [hη]; exact (hd i).1)
    (fun i ↦ by simp only [hη]; exact (hd i).2)]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

section CasimirAndTrace

/-- For `β = 1` (the GOE parameterization), `gaussianEnsemble β n g` is a symmetric matrix. -/
theorem isSymm_gaussianEnsemble_of_eq_one {β n : ℕ} (hβ : β = 1) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsemble β n g).IsSymm := by
  ext i j; rw [transpose_apply, gaussianEnsemble_apply, gaussianEnsemble_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hβ, hij, hij.ne, hij.not_gt, hij.ne']
  · simp [hβ]
  · simp [hβ, hji, hji.ne, hji.not_gt, hji.ne']

/-- For `β = 1`, swapping matrix indices preserves `gaussianEnsemble β n g`. -/
theorem gaussianEnsemble_apply_comm_of_eq_one {β n : ℕ} (hβ : β = 1) (g : Fin n × Fin n → ℝ)
    (i j : Fin n) : gaussianEnsemble β n g i j = gaussianEnsemble β n g j i :=
  (isSymm_gaussianEnsemble_of_eq_one hβ g).apply j i

/-- Continuous `ℝ`-linear map bundling `gaussianEnsemble β n` into the real topological submodule
`selfAdjoint (Matrix (Fin n) (Fin n) ℂ)`. -/
def gaussianEnsembleSelfAdjointCLM (β n : ℕ) :
    (Fin n × Fin n → ℝ) →L[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℂ) where
  toFun g := ⟨gaussianEnsemble β n g, (isHermitian_gaussianEnsemble β n g).isSelfAdjoint⟩
  map_add' g h := Subtype.ext (gaussianEnsemble_add g h)
  map_smul' c g := Subtype.ext (gaussianEnsemble_smul c g)
  cont := continuous_gaussianEnsemble.subtype_mk _

/-- Coercing `gaussianEnsembleSelfAdjointCLM β n g` to a matrix recovers
`gaussianEnsemble β n g`. -/
@[simp] theorem coe_gaussianEnsembleSelfAdjointCLM_apply (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleSelfAdjointCLM β n g : Matrix (Fin n) (Fin n) ℂ) =
      gaussianEnsemble β n g := (rfl)

private abbrev ensSingle (β n : ℕ) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  gaussianEnsemble β n (Pi.single p 1)

private theorem inv_sqrt_nat_sq (n : ℕ) :
    (Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_natCast]

private theorem inv_sqrt_two_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]

private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_ofNat]

private theorem gaussianEnsemble_single_apply_eq_zero {β n : ℕ} {p : Fin n × Fin n}
    {i j : Fin n} (h1 : p ≠ (i, j)) (h2 : p ≠ (j, i)) : ensSingle β n p i j = 0 := by
  rcases eq_or_ne i j with rfl | hij <;>
    simp [ensSingle, gaussianEnsemble_apply, h1.symm, h2.symm, *]

private theorem sum_gaussianEnsemble_single_apply_mul_eq_pair (β n : ℕ) (i j k l : Fin n) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l =
      ∑ p ∈ ({(i, j), (j, i)} : Finset (Fin n × Fin n)),
        ensSingle β n p i j * ensSingle β n p k l := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun p _ hp ↦ ?_).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  rw [gaussianEnsemble_single_apply_eq_zero hp.left hp.right, zero_mul]

private theorem sum_gaussianEnsemble_single_apply_mul_eq_zero_of_not {β n : ℕ}
    {i j k l : Fin n} (h1 : ¬ (i = l ∧ j = k)) (h2 : ¬ (i = k ∧ j = l)) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l = 0 :=
  Finset.sum_eq_zero fun p _ ↦ by
    by_cases hp : p = (i, j) ∨ p = (j, i)
    · rw [gaussianEnsemble_single_apply_eq_zero (i := k) (j := l) (by grind) (by grind), mul_zero]
    · rw [gaussianEnsemble_single_apply_eq_zero (i := i) (j := j) (by grind) (by grind), zero_mul]

private theorem sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {i j : Fin n} (hij : i < j) (k l : Fin n) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l =
      if i = l ∧ j = k then (n : ℂ)⁻¹ else 0 := by
  by_cases h1 : i = l ∧ j = k
  · rcases h1 with ⟨rfl, rfl⟩
    rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
      Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).left)]
    simp only [ensSingle, gaussianEnsemble_apply_of_lt_of_ne_one _ hβ hij,
      gaussianEnsemble_apply_of_gt_of_ne_one _ hβ hij, Pi.single_apply, Prod.mk.injEq, hij.ne,
      hij.ne', and_self, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero, mul_one,
      mul_zero, add_zero, zero_add, sub_zero, zero_sub, div_eq_mul_inv]
    linear_combination (1 - Complex.I * Complex.I) *
        ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) * inv_sqrt_two_sq + inv_sqrt_nat_sq n -
      ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) * (2 : ℂ)⁻¹ * Complex.I_mul_I
  · by_cases h2 : i = k ∧ j = l
    · rcases h2 with ⟨rfl, rfl⟩
      rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
        Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).left)]
      simp only [ensSingle, gaussianEnsemble_apply_of_lt_of_ne_one _ hβ hij, Pi.single_apply,
        Prod.mk.injEq, hij.ne, hij.ne', and_self, ↓reduceIte, Complex.ofReal_one,
        Complex.ofReal_zero, mul_one, mul_zero, add_zero, zero_add, div_eq_mul_inv]
      linear_combination ((Real.sqrt ↑n : ℂ)⁻¹ * (Real.sqrt ↑n : ℂ)⁻¹) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * Complex.I_mul_I
    · simp [h1, sum_gaussianEnsemble_single_apply_mul_eq_zero_of_not h1 h2]

private theorem star_sum_gaussianEnsemble_single_apply_mul (β n : ℕ) (i j k l : Fin n) :
    star (∑ p : Fin n × Fin n, ensSingle β n p j i * ensSingle β n p l k) =
      ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l := by
  have hstar (p : Fin n × Fin n) (a b : Fin n) :
      star (ensSingle β n p b a) = ensSingle β n p a b := by
    simpa [conjTranspose_apply] using congr_fun₂ (isHermitian_gaussianEnsemble β n _).eq a b
  rw [star_sum]; exact Finset.sum_congr rfl fun p _ ↦ by rw [star_mul', hstar, hstar, mul_comm]

private theorem sum_gaussianEnsemble_single_apply_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (i j k l : Fin n) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l =
      if i = l ∧ j = k then (n : ℂ)⁻¹ else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one hβ hij k l
  · by_cases hkl : i = l ∧ i = k
    · rcases hkl with ⟨rfl, rfl⟩
      rw [sum_gaussianEnsemble_single_apply_mul_eq_pair, Finset.pair_eq_singleton,
        Finset.sum_singleton]
      simp [ensSingle, hβ, inv_sqrt_nat_sq]
    · simp [hkl, sum_gaussianEnsemble_single_apply_mul_eq_zero_of_not hkl (by grind)]
  · have h := congrArg star (sum_gaussianEnsemble_single_apply_mul_of_lt_of_ne_one hβ hji l k)
    rw [star_sum_gaussianEnsemble_single_apply_mul] at h
    refine h.trans ?_
    by_cases hc : i = l ∧ j = k
    · rcases hc with ⟨rfl, rfl⟩; simp [RCLike.star_def, ← Complex.ofReal_natCast]
    · have hc' : ¬ (j = k ∧ i = l) := by grind
      simp [hc, hc']

private theorem sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one {β n : ℕ} (hβ : β = 1)
    {i j : Fin n} (hij : i < j) (k l : Fin n) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l =
      (n : ℂ)⁻¹ * ((if i = l ∧ j = k then 1 else 0) + (if i = k ∧ j = l then 1 else 0)) := by
  by_cases h1 : i = l ∧ j = k
  · rcases h1 with ⟨rfl, rfl⟩
    rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
      Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).left)]
    simp [ensSingle, gaussianEnsemble_apply_of_lt_of_eq_one _ hβ hij,
      gaussianEnsemble_apply_of_gt_of_eq_one _ hβ hij, hij.ne, inv_sqrt_nat_sq]
  · by_cases h2 : i = k ∧ j = l
    · rcases h2 with ⟨rfl, rfl⟩
      rw [sum_gaussianEnsemble_single_apply_mul_eq_pair,
        Finset.sum_pair (fun h ↦ hij.ne (Prod.mk.inj h).left)]
      simp [ensSingle, gaussianEnsemble_apply_of_lt_of_eq_one _ hβ hij, hij.ne, inv_sqrt_nat_sq]
    · simp [h1, h2, sum_gaussianEnsemble_single_apply_mul_eq_zero_of_not h1 h2]

private theorem sum_gaussianEnsemble_single_apply_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    (i j k l : Fin n) :
    ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l =
      (n : ℂ)⁻¹ * ((if i = l ∧ j = k then 1 else 0) + (if i = k ∧ j = l then 1 else 0)) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one hβ hij k l
  · by_cases hkl : i = l ∧ i = k
    · rcases hkl with ⟨rfl, rfl⟩
      rw [sum_gaussianEnsemble_single_apply_mul_eq_pair, Finset.pair_eq_singleton,
        Finset.sum_singleton]
      simp only [ensSingle, gaussianEnsemble_apply_self_of_eq_one _ hβ, Pi.single_eq_same, mul_one,
        and_self, ↓reduceIte]
      linear_combination (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) * inv_sqrt_nat_sq n +
        (n : ℂ)⁻¹ * sqrt_two_sq
    · have hkl' : ¬ (i = k ∧ i = l) := by grind
      simp [hkl, hkl', sum_gaussianEnsemble_single_apply_mul_eq_zero_of_not hkl hkl']
  · simp_rw [ensSingle, gaussianEnsemble_apply_comm_of_eq_one hβ _ i j]
    rw [sum_gaussianEnsemble_single_apply_mul_of_lt_of_eq_one hβ hji k l, add_comm]
    congr 2 <;> exact if_congr and_comm rfl rfl

private theorem sum_single_mul_mul_self_apply (β n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i l : Fin n) :
    (∑ p : Fin n × Fin n, ensSingle β n p * M * ensSingle β n p) i l =
      ∑ j : Fin n, ∑ k : Fin n, M j k *
        ∑ p : Fin n × Fin n, ensSingle β n p i j * ensSingle β n p k l := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm.trans <| Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun p _ ↦ by ring).trans Finset.sum_comm

/-- **GUE Casimir identity**: for `β ≠ 1` and any `M`,
`∑ p, Eₚ * M * Eₚ = (n⁻¹ * M.trace) • 1`, where `Eₚ = gaussianEnsemble β n (Pi.single p 1)`. -/
theorem sum_gaussianEnsemble_single_mul_mul_self_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      ((n : ℂ)⁻¹ * M.trace) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i l; rw [sum_single_mul_mul_self_apply]
  simp_rw [sum_gaussianEnsemble_single_apply_mul_of_ne_one hβ]
  by_cases hil : i = l <;> simp [hil, Matrix.trace, Finset.mul_sum, mul_comm]

/-- **GOE Casimir identity**: for `β = 1` and any `M`,
`∑ p, Eₚ * M * Eₚ = n⁻¹ • (M.trace • 1 + Mᵀ)`, where
`Eₚ = gaussianEnsemble β n (Pi.single p 1)`. -/
theorem sum_gaussianEnsemble_single_mul_mul_self_of_eq_one {β n : ℕ} (hβ : β = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * M * gaussianEnsemble β n (Pi.single p 1) =
      (n : ℂ)⁻¹ • (M.trace • (1 : Matrix (Fin n) (Fin n) ℂ) + Mᵀ) := by
  ext i l; rw [sum_single_mul_mul_self_apply]
  simp_rw [sum_gaussianEnsemble_single_apply_mul_of_eq_one hβ, ← mul_assoc,
    mul_comm (M _ _) (n : ℂ)⁻¹, mul_assoc, ← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ j : Fin n, ∑ k : Fin n, M j k * if i = l ∧ j = k then (1 : ℂ) else 0) =
      if i = l then M.trace else 0 := by by_cases hil : i = l <;> simp [hil, Matrix.trace]
  have h2 : (∑ j : Fin n, ∑ k : Fin n, M j k * if i = k ∧ j = l then (1 : ℂ) else 0) = M l i := by
    simp [ite_and]
  rw [h1, h2]; simp [Matrix.one_apply]

private theorem sum_trace_mul_eq_sum_cov (β n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n, (X * ensSingle β n p).trace * (Y * ensSingle β n p).trace =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, (X i j * Y k l) *
        ∑ p : Fin n × Fin n, ensSingle β n p j i * ensSingle β n p l k := by
  have hexp (p : Fin n × Fin n) :
      (X * ensSingle β n p).trace * (Y * ensSingle β n p).trace =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          (X i j * Y k l) * (ensSingle β n p j i * ensSingle β n p l k) := by
    rw [Matrix.trace_mul_eq_sum X, Matrix.trace_mul_eq_sum Y, Finset.sum_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  simp_rw [hexp, Finset.mul_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm.trans <| Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm

/-- **GUE trace inner-product identity** for `β ≠ 1`. -/
theorem sum_trace_mul_gaussianEnsemble_single_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * (X * Y).trace := by
  rw [sum_trace_mul_eq_sum_cov]
  have hinner (i j : Fin n) : (∑ k : Fin n, ∑ l : Fin n, (X i j * Y k l) *
      ∑ p : Fin n × Fin n, ensSingle β n p j i * ensSingle β n p l k) =
      (n : ℂ)⁻¹ * (X i j * Y j i) := by
    simp only [sum_gaussianEnsemble_single_apply_mul_of_ne_one hβ, ite_and, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [hinner, ← Finset.mul_sum, ← Matrix.trace_mul_eq_sum]

/-- **GOE trace inner-product identity** for `β = 1`. -/
theorem sum_trace_mul_gaussianEnsemble_single_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace =
      (n : ℂ)⁻¹ * ((X * Y).trace + (X * Yᵀ).trace) := by
  rw [sum_trace_mul_eq_sum_cov]
  have hinner (i j : Fin n) : (∑ k : Fin n, ∑ l : Fin n, (X i j * Y k l) *
      ∑ p : Fin n × Fin n, ensSingle β n p j i * ensSingle β n p l k) =
      (n : ℂ)⁻¹ * (X i j * Y j i + X i j * Y i j) := by
    simp only [sum_gaussianEnsemble_single_apply_mul_of_eq_one hβ, mul_add, mul_ite, mul_one,
      mul_zero, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [hinner, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp [Matrix.trace_mul_eq_sum, transpose_apply]

private theorem re_sum_trace_mul_gaussianEnsemble_single_mul (β n : ℕ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (∑ p : Fin n × Fin n, (X * ensSingle β n p).trace * (Y * ensSingle β n p).trace).re =
      ∑ p : Fin n × Fin n,
        (X * ensSingle β n p).trace.re * (Y * ensSingle β n p).trace.re := by
  have hreal {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
      (((A * B).trace).re : ℂ) = (A * B).trace :=
    RCLike.conj_eq_iff_re.mp (by
      rw [← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq,
        trace_mul_comm])
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hE := isHermitian_gaussianEnsemble β n (Pi.single p 1)
  conv_lhs => rw [← hreal hX hE, ← hreal hY hE]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Real-part GUE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * (X * Y).trace.re := by
  rw [← re_sum_trace_mul_gaussianEnsemble_single_mul β n hX hY,
    sum_trace_mul_gaussianEnsemble_single_mul_of_ne_one hβ, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]

/-- Real-part GOE trace inner-product identity for Hermitian matrices `X, Y`. -/
theorem sum_re_trace_mul_gaussianEnsemble_single_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (n : ℝ)⁻¹ * ((X * Y).trace.re + (X * Yᵀ).trace.re) := by
  rw [← re_sum_trace_mul_gaussianEnsemble_single_mul β n hX hY,
    sum_trace_mul_gaussianEnsemble_single_mul_of_eq_one hβ, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.add_re]

end CasimirAndTrace

end Probability

end TauCeti
