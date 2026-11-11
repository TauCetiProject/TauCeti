/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Analysis.Complex.NormSq

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

## Main results

* `TauCeti.Probability.isHermitian_gaussianEnsemble`: the matrix is Hermitian.
* `TauCeti.Probability.gaussianEnsemble_one_zero_zero_hasLaw` and
  `TauCeti.Probability.gaussianEnsemble_two_zero_zero_hasLaw`: the laws of the `1 × 1` ensembles,
  `N(0, 2)` and `N(0, 1)`.
* `TauCeti.Probability.integral_re_trace_gaussianEnsemble_one_sq_div` and
  `TauCeti.Probability.integral_re_trace_gaussianEnsemble_two_sq_div`: the normalized trace of
  the square has expectation `1 + 1 / n` for the GOE and `1` for the GUE.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.6.
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
  simp [extendArray, i.2, j.2]

/-- The above-diagonal entries of the Wigner matrix equal to `gaussianEnsemble β n`. -/
private def ensembleUpper {Ω : Type*} (β n : ℕ) (g : Fin n × Fin n → Ω → ℝ) :
    StrictUpper → Ω → ℂ := fun ij ω ↦
  if β = 1 then (extendArray n g ij.1 ω : ℂ)
  else ((extendArray n g ij.1 ω : ℂ) + Complex.I * extendArray n g (ij.1.2, ij.1.1) ω) /
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
      ∀ ω, ‖ensembleUpper 1 n g ij ω‖ ^ 2 = extendArray n g ij.1 ω ^ 2 := by
    intro ω
    simp [ensembleUpper]
  have hη (i : ℕ) : ∀ ω, ensembleDiag 1 n g i ω ^ 2 = 2 * extendArray n g (i, i) ω ^ 2 := by
    intro ω
    simp [ensembleDiag, mul_pow]
  have hd (i : ℕ) := hm (i, i) fun _ ↦ le_rfl
  have hu (ij : StrictUpper) := hm ij.1 fun h ↦ (Fin.mk_le_mk.2 ij.2.le)
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
      (extendArray n g ij.1 ω ^ 2 + extendArray n g (ij.1.2, ij.1.1) ω ^ 2) / 2 := by
    intro ω
    simpa [ensembleUpper] using Complex.norm_sq_add_I_mul_div_sqrt_two _ _
  have hη (i : ℕ) : ∀ ω, ensembleDiag 2 n g i ω ^ 2 = extendArray n g (i, i) ω ^ 2 := by
    intro ω
    simp [ensembleDiag]
  have hd (i : ℕ) := hm (i, i) fun _ ↦ trivial
  have hu (ij : StrictUpper) := hm ij.1 fun _ ↦ trivial
  have hu' (ij : StrictUpper) := hm (ij.1.2, ij.1.1) fun _ ↦ trivial
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

end Probability

end TauCeti
