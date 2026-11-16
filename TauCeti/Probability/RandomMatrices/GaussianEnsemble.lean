/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.Complex.NormSq
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.RandomMatrix.Wigner
import TauCeti.MeasureTheory.Measure.Smul
import TauCeti.Probability.Independence.Pi

/-!
# Gaussian orthogonal and unitary ensembles

The matrix `gaussianEnsemble β n g` built from an array `g` of reals: for `β = 1` the real
symmetric matrix with entries `g (i, j)` above the diagonal and `√2 * g (i, i)` on it, and
otherwise the Hermitian matrix with entries `(g (i, j) + I * g (j, i)) / √2` above the diagonal
and `g (i, i)` on it, all divided by `√n`. With independent standard Gaussian entries this is the
GOE (`β = 1`) or the GUE (`β = 2`). Realizations are Wigner matrices
(`TauCeti.wignerMatrix`), which gives the Hermitian property and the second-moment computation.

Viewed directly on the real self-adjoint subspaces
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` and
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`, the realizations are `goeMatrix` and
`gueMatrix`, and their laws under independent standard Gaussian coordinates are `goeMeasure n` and
`gueMeasure n`. In the Frobenius inner product, `goeMeasure n` is the pushforward of `stdGaussian`
by `√(2 / n)` and `gueMeasure n` is the pushforward of `stdGaussian` by `(√n)⁻¹`. This yields
orthogonal and unitary conjugation invariance immediately via `stdGaussian_map`, the explicit
densities against Frobenius volume and coordinate Lebesgue measures `TauCeti.symmetricLebesgue` and
`TauCeti.hermitianLebesgue`, and the equivalence between the independent-entry and
invariant-density characterizations of GOE and GUE.

## Main definitions

* `TauCeti.Probability.gaussianEnsemble` — the ambient complex matrix built from the array `g`.
* `TauCeti.Probability.goeMatrix` and `TauCeti.Probability.gueMatrix` — the GOE and GUE
  constructions valued in the real symmetric and complex Hermitian subspaces.
* `TauCeti.Probability.goeMeasure` and `TauCeti.Probability.gueMeasure` — the canonical GOE and
  GUE probability laws on the real symmetric and complex Hermitian subspaces.
* `TauCeti.Probability.goePDFReal`, `TauCeti.Probability.goePDF`,
  `TauCeti.Probability.guePDFReal`, and `TauCeti.Probability.guePDF` — the GOE and GUE densities
  against `TauCeti.symmetricLebesgue` and `TauCeti.hermitianLebesgue`.

## Main results

* `TauCeti.Probability.isHermitian_gaussianEnsemble` — the matrix is Hermitian.
* `TauCeti.Probability.gaussianEnsemble_add` and `TauCeti.Probability.gaussianEnsemble_smul` — the
  matrix is real-linear in the array.
* `TauCeti.Probability.continuous_gaussianEnsemble` — it depends continuously on the array.
* `TauCeti.Probability.hasLaw_gaussianEnsemble` — with independent `N(0, v)` coordinates the
  ensemble has the law of `√v` times the ensemble of standard Gaussian coordinates.
* `TauCeti.Probability.goeMeasure_eq_map_stdGaussian` and
  `TauCeti.Probability.gueMeasure_eq_map_stdGaussian` — `goeMeasure n` and `gueMeasure n` are
  scalar multiples of `stdGaussian` for the Frobenius inner product.
* `Matrix.unitaryGroup.map_symmetricConj_goeMeasure`,
  `Matrix.unitaryGroup.map_hermitianConj_gueMeasure`,
  `TauCeti.Probability.identDistrib_conj_gaussianEnsemble_one`, and
  `TauCeti.Probability.identDistrib_conj_gaussianEnsemble_of_ne_one` — orthogonal and unitary
  conjugation invariance.
* `TauCeti.Probability.goeMeasure_eq_withDensity_volume`,
  `TauCeti.Probability.goeMeasure_eq_withDensity_symmetricLebesgue`,
  `TauCeti.Probability.gueMeasure_eq_withDensity_volume`, and
  `TauCeti.Probability.gueMeasure_eq_withDensity_hermitianLebesgue` — the invariant trace-square
  densities against Frobenius volume and coordinate Lebesgue measures, together with `HasPDF`,
  `pdf`, and `rnDeriv` identifications.
* `TauCeti.Probability.hasLaw_goeMeasure_iff_entries`,
  `TauCeti.Probability.hasLaw_goe_withDensity_iff_entries`,
  `TauCeti.Probability.hasLaw_gueMeasure_iff_entries`, and
  `TauCeti.Probability.hasLaw_gue_withDensity_iff_entries` — equivalence of the independent-entry
  and invariant-density characterizations.
* `TauCeti.Probability.gaussianEnsemble_one_zero_zero_hasLaw` and
  `TauCeti.Probability.gaussianEnsemble_two_zero_zero_hasLaw` — the laws of the `1 × 1` ensembles,
  `N(0, 2)` and `N(0, 1)`.
* `TauCeti.Probability.integral_re_trace_gaussianEnsemble_one_sq_div` and
  `TauCeti.Probability.integral_re_trace_gaussianEnsemble_two_sq_div` — the normalized trace of
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
open scoped ENNReal NNReal Real RealInnerProductSpace Matrix

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
  have hlaw := (⟨by fun_prop, rfl⟩ : HasLaw (gaussianEnsemble β n) _ _).comp (hindep.hasLaw_pi hg)
  rw [pi_gaussianReal_eq_map_sqrt_smul, Measure.map_map (by fun_prop) (by fun_prop)] at hlaw
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

/-! ### Self-adjoint realizations and canonical GOE/GUE measures -/

section SelfAdjoint

variable {n : ℕ}

/-- The GOE realization valued directly in the real symmetric subspace
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`: entries `(√n)⁻¹ * g (i, j)` for `i < j`
and `(√n)⁻¹ * √2 * g (i, i)` on the diagonal. Complexifying its entries gives
`gaussianEnsemble 1 n g`. -/
def goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (symmetricCoordinates n).symm fun ij ↦
    (Real.sqrt n)⁻¹ * if ij.1.1 = ij.1.2 then Real.sqrt 2 * g ij.1 else g ij.1

@[simp]
theorem coe_goeMatrix_apply_self (g : Fin n × Fin n → ℝ) (i : Fin n) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i i =
      (Real.sqrt n)⁻¹ * (Real.sqrt 2 * g (i, i)) := by
  simp [goeMatrix]

@[simp]
theorem coe_goeMatrix_apply_of_lt (g : Fin n × Fin n → ℝ) {i j : Fin n} (h : i < j) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (i, j) := by
  rw [goeMatrix, coe_symmetricCoordinates_symm_apply_of_le n _ h.le, ite_eq_right h.ne]

@[simp]
theorem coe_goeMatrix_apply_of_gt (g : Fin n × Fin n → ℝ) {i j : Fin n} (h : j < i) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (j, i) := by
  rw [goeMatrix, coe_symmetricCoordinates_symm_apply_of_ge n _ h.le, ite_eq_right h.ne]

/-- Complexifying the entries of `goeMatrix n g` yields `gaussianEnsemble 1 n g`. -/
theorem coe_goeMatrix_map_ofReal (g : Fin n × Fin n → ℝ) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal = gaussianEnsemble 1 n g := by
  ext i j
  simp only [Matrix.map_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h]
  · simp
  · simp [h]

@[simp]
theorem goeMatrix_add (g h : Fin n × Fin n → ℝ) :
    goeMatrix n (g + h) = goeMatrix n g + goeMatrix n h := by
  apply (symmetricCoordinates n).injective
  funext ij
  simp only [goeMatrix, map_add, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply]
  split_ifs <;> ring

@[simp]
theorem goeMatrix_smul (c : ℝ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n (c • g) = c • goeMatrix n g := by
  apply (symmetricCoordinates n).injective
  funext ij
  simp only [goeMatrix, map_smul, ContinuousLinearEquiv.apply_symm_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> ring

@[simp]
theorem goeMatrix_zero : goeMatrix n 0 = 0 := by
  simpa using goeMatrix_smul (n := n) 0 0

@[fun_prop]
theorem continuous_goeMatrix : Continuous (goeMatrix n) := by
  refine (symmetricCoordinates n).symm.continuous.comp (continuous_pi fun ij ↦ ?_)
  split_ifs <;> fun_prop

@[fun_prop]
theorem measurable_goeMatrix : Measurable (goeMatrix n) :=
  continuous_goeMatrix.measurable

/-- The GUE realization valued directly in the complex Hermitian subspace
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`: diagonal entries `(√n)⁻¹ * g (i, i)` and
strictly upper-triangular entries `(√n)⁻¹ * (g (i, j) + I * g (j, i)) / √2`. Its coercion to
`Matrix (Fin n) (Fin n) ℂ` is `gaussianEnsemble β n g` for every `β ≠ 1` (in particular `β = 2`). -/
def gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (hermitianCoordinates n).symm fun p ↦
    (Real.sqrt n)⁻¹ * if p.1 = p.2 then g p else (Real.sqrt 2)⁻¹ * g p

/-- Coercing `gueMatrix n g` to `Matrix (Fin n) (Fin n) ℂ` gives `gaussianEnsemble β n g` for every
`β ≠ 1`. -/
theorem coe_gueMatrix_eq_gaussianEnsemble {β : ℕ} (hβ : β ≠ 1) (g : Fin n × Fin n → ℝ) :
    (gueMatrix n g : Matrix (Fin n) (Fin n) ℂ) = gaussianEnsemble β n g := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [gueMatrix, coe_hermitianCoordinates_symm_apply_of_lt n _ h,
      gaussianEnsemble_apply_of_lt_of_ne_one _ hβ h, ite_eq_right h.ne, ite_eq_right h.ne']
    push_cast
    ring
  · rw [gueMatrix, coe_hermitianCoordinates_symm_apply_self,
      gaussianEnsemble_apply_self_of_ne_one _ hβ]
    simp
  · rw [gueMatrix, coe_hermitianCoordinates_symm_apply_of_gt n _ h,
      gaussianEnsemble_apply_of_gt_of_ne_one _ hβ h, ite_eq_right h.ne, ite_eq_right h.ne']
    push_cast
    ring

/-- Coercing `gueMatrix n g` to `Matrix (Fin n) (Fin n) ℂ` gives `gaussianEnsemble 2 n g`. -/
theorem coe_gueMatrix (g : Fin n × Fin n → ℝ) :
    (gueMatrix n g : Matrix (Fin n) (Fin n) ℂ) = gaussianEnsemble 2 n g :=
  coe_gueMatrix_eq_gaussianEnsemble (by decide) g

@[simp]
theorem gueMatrix_add (g h : Fin n × Fin n → ℝ) :
    gueMatrix n (g + h) = gueMatrix n g + gueMatrix n h := by
  apply (hermitianCoordinates n).injective
  funext p
  simp only [gueMatrix, map_add, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply]
  split_ifs <;> ring

@[simp]
theorem gueMatrix_smul (c : ℝ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n (c • g) = c • gueMatrix n g := by
  apply (hermitianCoordinates n).injective
  funext p
  simp only [gueMatrix, map_smul, ContinuousLinearEquiv.apply_symm_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> ring

@[simp]
theorem gueMatrix_zero : gueMatrix n 0 = 0 := by
  simpa using gueMatrix_smul (n := n) 0 0

@[fun_prop]
theorem continuous_gueMatrix : Continuous (gueMatrix n) := by
  refine (hermitianCoordinates n).symm.continuous.comp (continuous_pi fun p ↦ ?_)
  split_ifs <;> fun_prop

@[fun_prop]
theorem measurable_gueMatrix : Measurable (gueMatrix n) :=
  continuous_gueMatrix.measurable

end SelfAdjoint

section Measures

variable {n : ℕ}

/-- **The GOE probability measure** on the real symmetric subspace
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`: the pushforward of independent standard
real Gaussian coordinates under `goeMatrix n`. -/
def goeMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n)

/-- **The GUE probability measure** on the complex Hermitian subspace
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`: the pushforward of independent standard
real Gaussian coordinates under `gueMatrix n`. -/
def gueMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n)

instance isProbabilityMeasure_goeMeasure (n : ℕ) : IsProbabilityMeasure (goeMeasure n) := by
  unfold goeMeasure
  infer_instance

instance isProbabilityMeasure_gueMeasure (n : ℕ) : IsProbabilityMeasure (gueMeasure n) := by
  unfold gueMeasure
  infer_instance

/-- In dimension zero, `goeMeasure 0` is the Dirac measure at `0`. -/
@[simp]
theorem goeMeasure_zero : goeMeasure 0 = Measure.dirac 0 := by
  have : IsEmpty (Fin 0 × Fin 0) := ⟨fun p ↦ p.1.elim0⟩
  rw [goeMeasure, Measure.pi_of_empty _ 0, Measure.map_dirac, goeMatrix_zero]

/-- In dimension zero, `gueMeasure 0` is the Dirac measure at `0`. -/
@[simp]
theorem gueMeasure_zero : gueMeasure 0 = Measure.dirac 0 := by
  have : IsEmpty (Fin 0 × Fin 0) := ⟨fun p ↦ p.1.elim0⟩
  rw [gueMeasure, Measure.pi_of_empty _ 0, Measure.map_dirac, gueMatrix_zero]

private theorem measurable_ofReal_symmetric (n : ℕ) :
    Measurable (fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      (H : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal) := by
  refine Continuous.measurable (continuous_matrix fun i j ↦ ?_)
  exact Complex.continuous_ofReal.comp
    ((continuous_apply_apply i j).comp continuous_subtype_val)

/-- Pushing `goeMeasure n` forward by real-to-complex entrywise coercion gives the law of
`gaussianEnsemble 1 n` under independent standard Gaussian coordinates. -/
theorem map_ofReal_goeMeasure (n : ℕ) :
    (goeMeasure n).map
        (fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (H : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal) =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble 1 n) := by
  rw [goeMeasure, Measure.map_map (measurable_ofReal_symmetric n) measurable_goeMatrix]
  congr 1
  funext g
  exact coe_goeMatrix_map_ofReal g

/-- Pushing `gueMeasure n` forward by subtype coercion gives the law of `gaussianEnsemble β n`
for every `β ≠ 1` under independent standard Gaussian coordinates. -/
theorem map_coe_gueMeasure {β : ℕ} (hβ : β ≠ 1) (n : ℕ) :
    (gueMeasure n).map
        (fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
          (H : Matrix (Fin n) (Fin n) ℂ)) =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n) := by
  rw [gueMeasure, Measure.map_map continuous_subtype_val.measurable measurable_gueMatrix]
  congr 1
  funext g
  exact coe_gueMatrix_eq_gaussianEnsemble hβ g

/-- With independent `N(0, v)` coordinates, `goeMatrix n` has the law of `√v` times `goeMeasure n`.
-/
theorem hasLaw_goeMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P) :
    HasLaw (fun ω ↦ goeMatrix n (fun ij ↦ g ij ω))
      ((goeMeasure n).map (Real.sqrt v • ·)) P := by
  have hlaw := (⟨measurable_goeMatrix.aemeasurable, rfl⟩ :
      HasLaw (goeMatrix n) _ _).comp (hindep.hasLaw_pi hg)
  rw [pi_gaussianReal_eq_map_sqrt_smul,
    Measure.map_map_const_smul _ measurable_goeMatrix _ (goeMatrix_smul _)] at hlaw
  exact hlaw

/-- With independent `N(0, v)` coordinates, `gueMatrix n` has the law of `√v` times `gueMeasure n`.
-/
theorem hasLaw_gueMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P) :
    HasLaw (fun ω ↦ gueMatrix n (fun ij ↦ g ij ω))
      ((gueMeasure n).map (Real.sqrt v • ·)) P := by
  have hlaw := (⟨measurable_gueMatrix.aemeasurable, rfl⟩ :
      HasLaw (gueMatrix n) _ _).comp (hindep.hasLaw_pi hg)
  rw [pi_gaussianReal_eq_map_sqrt_smul,
    Measure.map_map_const_smul _ measurable_gueMatrix _ (gueMatrix_smul _)] at hlaw
  exact hlaw

private theorem goeMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n g =
      Real.sqrt (2 / n) • ∑ ij : upperTriangle n, g ij.1 • symmetricOrthonormalBasis n ij := by
  apply (symmetricCoordinates n).injective
  funext kl
  rcases eq_or_ne n 0 with rfl | hn
  · exact kl.1.1.elim0
  simp only [goeMatrix, ContinuousLinearEquiv.apply_symm_apply, map_smul, map_sum,
    symmetricOrthonormalBasis_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hterm : ∀ ij : upperTriangle n,
      g ij.1 * symmetricCoordinates n
          (if ij.1.1 = ij.1.2 then symmetricBasis n ij
            else (Real.sqrt 2)⁻¹ • symmetricBasis n ij) kl =
        if ij = kl then (if kl.1.1 = kl.1.2 then g kl.1 else (Real.sqrt 2)⁻¹ * g kl.1) else 0 := by
    intro ij
    have hcoord : symmetricCoordinates n (symmetricBasis n ij) kl = if ij = kl then 1 else 0 := by
      rw [symmetricBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    by_cases heq : ij = kl
    · subst heq
      by_cases hd : ij.1.1 = ij.1.2 <;>
        simp only [hd, ↓reduceIte, map_smul, Pi.smul_apply, smul_eq_mul, hcoord, mul_one, one_mul,
          mul_comm]
    · by_cases hd : ij.1.1 = ij.1.2 <;>
        simp only [hd, heq, ↓reduceIte, map_smul, Pi.smul_apply, smul_eq_mul, hcoord, mul_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Real.sqrt_div (by norm_num)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  by_cases hd : kl.1.1 = kl.1.2
  · simp [hd, div_eq_mul_inv, mul_comm, mul_left_comm]
  · simp only [hd, ↓reduceIte]
    field_simp

private theorem gueMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n g =
      (Real.sqrt n)⁻¹ • ∑ p : Fin n × Fin n, g p • hermitianOrthonormalBasis n p := by
  apply (hermitianCoordinates n).injective
  funext q
  simp only [gueMatrix, ContinuousLinearEquiv.apply_symm_apply, map_smul, map_sum,
    hermitianOrthonormalBasis_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hterm : ∀ p : Fin n × Fin n,
      g p * hermitianCoordinates n
          (if p.1 = p.2 then hermitianBasis n p
            else (Real.sqrt 2)⁻¹ • hermitianBasis n p) q =
        if p = q then (if q.1 = q.2 then g q else (Real.sqrt 2)⁻¹ * g q) else 0 := by
    intro p
    have hcoord : hermitianCoordinates n (hermitianBasis n p) q = if p = q then 1 else 0 := by
      rw [hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    by_cases heq : p = q
    · subst heq
      by_cases hd : p.1 = p.2 <;> simp [hd, hcoord, mul_comm]
    · by_cases hd : p.1 = p.2 <;> simp [hd, heq, hcoord]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem map_restrict_upperTriangle_pi_gaussianReal (n : ℕ) :
    (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map
        (fun g (ij : upperTriangle n) ↦ g ij.1) =
      Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1 := by
  let μ := Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1
  have hind : iIndepFun (fun ij : upperTriangle n ↦ fun g : Fin n × Fin n → ℝ ↦ g ij.1) μ :=
    (iIndepFun_pi (μ := fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
      (X := fun _ x ↦ x) fun _ ↦ measurable_id.aemeasurable).precomp Subtype.val_injective
  have hlaw : ∀ ij : upperTriangle n,
      HasLaw (fun g : Fin n × Fin n → ℝ ↦ g ij.1) (gaussianReal 0 1) μ := fun ij ↦
    ⟨(measurable_pi_apply ij.1).aemeasurable, (measurePreserving_eval _ ij.1).map_eq⟩
  exact (hind.hasLaw_pi hlaw).map_eq

/-- **Standard Gaussian representation of the GOE.** For the Frobenius inner product on the real
symmetric subspace, `goeMeasure n` is the pushforward of `stdGaussian` by `√(2 / n)`. -/
theorem goeMeasure_eq_map_stdGaussian (n : ℕ) :
    goeMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).map
        (fun H ↦ Real.sqrt (2 / n) • H) := by
  have hcomp : goeMatrix n =
      (fun H ↦ Real.sqrt (2 / n) • H) ∘
        (fun x : upperTriangle n → ℝ ↦ ∑ ij, x ij • symmetricOrthonormalBasis n ij) ∘
        (fun g (ij : upperTriangle n) ↦ g ij.1) := by
    funext g
    exact goeMatrix_eq_smul_sum_orthonormalBasis n g
  rw [goeMeasure, hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_restrict_upperTriangle_pi_gaussianReal,
    ← stdGaussian_eq_map_pi_orthonormalBasis (symmetricOrthonormalBasis n)]

/-- **Standard Gaussian representation of the GUE.** For the real Frobenius inner product on the
complex Hermitian subspace, `gueMeasure n` is the pushforward of `stdGaussian` by `(√n)⁻¹`. -/
theorem gueMeasure_eq_map_stdGaussian (n : ℕ) :
    gueMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).map
        (fun H ↦ (Real.sqrt n)⁻¹ • H) := by
  have hcomp : gueMatrix n =
      (fun H ↦ (Real.sqrt n)⁻¹ • H) ∘
        (fun g : Fin n × Fin n → ℝ ↦ ∑ p, g p • hermitianOrthonormalBasis n p) := by
    funext g
    exact gueMatrix_eq_smul_sum_orthonormalBasis n g
  rw [gueMeasure, hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← stdGaussian_eq_map_pi_orthonormalBasis (hermitianOrthonormalBasis n)]

/-- In dimension one, the single entry of the GOE law is `N(0, 2)`. -/
theorem map_symmetricFinOneEquiv_goeMeasure :
    (goeMeasure 1).map symmetricFinOneEquiv = gaussianReal 0 2 := by
  have hcomp : symmetricFinOneEquiv ∘ goeMatrix 1 =
      (fun x : ℝ ↦ Real.sqrt 2 * x) ∘ fun g : Fin 1 × Fin 1 → ℝ ↦ g (0, 0) := by
    funext g
    simp [Function.comp_apply, Real.sqrt_one]
  rw [goeMeasure, Measure.map_map symmetricFinOneEquiv.continuous.measurable measurable_goeMatrix,
    hcomp, ← Measure.map_map (by fun_prop : Measurable (fun x : ℝ ↦ Real.sqrt 2 * x))
      (measurable_pi_apply (0, 0)),
    (measurePreserving_eval _ (0, 0)).map_eq, gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  apply NNReal.eq
  simp

/-- In dimension one, the single real diagonal entry of the GUE law is `N(0, 1)`. -/
theorem map_hermitianFinOneEquiv_gueMeasure :
    (gueMeasure 1).map hermitianFinOneEquiv = gaussianReal 0 1 := by
  have hcomp : hermitianFinOneEquiv ∘ gueMatrix 1 = fun g : Fin 1 × Fin 1 → ℝ ↦ g (0, 0) := by
    funext g
    simp [Function.comp_apply, gueMatrix, Real.sqrt_one]
  rw [gueMeasure, Measure.map_map hermitianFinOneEquiv.continuous.measurable measurable_gueMatrix,
    hcomp, (measurePreserving_eval _ (0, 0)).map_eq]

end Measures

/-! ### Orthogonal and unitary conjugation invariance -/

section ConjugationInvariance

variable {n : ℕ}

/-- **Orthogonal conjugation invariance of the GOE.** For every `O ∈ O(n)`, conjugating a GOE
matrix by `O` leaves `goeMeasure n` invariant. -/
theorem _root_.Matrix.unitaryGroup.map_symmetricConj_goeMeasure
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (goeMeasure n).map (Matrix.unitaryGroup.symmetricConj O) = goeMeasure n := by
  rw [goeMeasure_eq_map_stdGaussian,
    Measure.map_map_const_smul _ (by fun_prop) _ (map_smul _ _),
    stdGaussian_map]

/-- **Unitary conjugation invariance of the GUE.** For every `U ∈ U(n)`, conjugating a GUE matrix
by `U` leaves `gueMeasure n` invariant. -/
theorem _root_.Matrix.unitaryGroup.map_hermitianConj_gueMeasure
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gueMeasure n).map (Matrix.unitaryGroup.hermitianConj U) = gueMeasure n := by
  rw [gueMeasure_eq_map_stdGaussian,
    Measure.map_map_const_smul _ (by fun_prop) _ (map_smul _ _),
    stdGaussian_map]

/-- **Orthogonal conjugation invariance of `gaussianEnsemble 1 n`.** With independent `N(0, v)`
coordinates, conjugating `gaussianEnsemble 1 n` by a real orthogonal matrix lifted to `ℂ` preserves
its distribution. -/
theorem identDistrib_conj_gaussianEnsemble_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P)
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    IdentDistrib
      (fun ω ↦
        (O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal *
          gaussianEnsemble 1 n (fun ij ↦ g ij ω) *
          ((O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᵀ)
      (fun ω ↦ gaussianEnsemble 1 n (fun ij ↦ g ij ω)) P P := by
  let lift : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun H ↦ (H : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal
  have hlift : Measurable lift := measurable_ofReal_symmetric n
  have hG : HasLaw (fun ω ↦ goeMatrix n (fun ij ↦ g ij ω))
      ((goeMeasure n).map (Real.sqrt v • ·)) P := hasLaw_goeMatrix hg hindep
  have hR : HasLaw (fun ω ↦ gaussianEnsemble 1 n (fun ij ↦ g ij ω))
      (((goeMeasure n).map (Real.sqrt v • ·)).map lift) P := by
    simpa only [Function.comp_def, lift, coe_goeMatrix_map_ofReal] using
      (⟨hlift.aemeasurable, rfl⟩ : HasLaw lift _ _).comp hG
  have hL : HasLaw
      (fun ω ↦
        (O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal *
          gaussianEnsemble 1 n (fun ij ↦ g ij ω) *
          ((O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᵀ)
      (((goeMeasure n).map (Real.sqrt v • ·)).map lift) P := by
    have hmap : ((goeMeasure n).map (Real.sqrt v • ·)).map (Matrix.unitaryGroup.symmetricConj O) =
        (goeMeasure n).map (Real.sqrt v • ·) := by
      rw [Measure.map_map_const_smul _ (by fun_prop) _ (map_smul _ _),
        Matrix.unitaryGroup.map_symmetricConj_goeMeasure O]
    have hconjG := (⟨by fun_prop, hmap⟩ :
      HasLaw (Matrix.unitaryGroup.symmetricConj O) _ _).fun_comp hG
    have hcomp := (⟨hlift.aemeasurable, rfl⟩ : HasLaw lift _ _).fun_comp hconjG
    convert hcomp using 1
    funext ω
    ext i j
    simp [lift, Matrix.mul_apply, Matrix.transpose_apply, ← coe_goeMatrix_map_ofReal]
  exact ⟨hL.aemeasurable, hR.aemeasurable, hL.map_eq.trans hR.map_eq.symm⟩

/-- **Unitary conjugation invariance of `gaussianEnsemble β n` (`β ≠ 1`, in particular GUE).**
With independent `N(0, v)` coordinates, conjugating `gaussianEnsemble β n` by a unitary matrix
`U ∈ U(n)` preserves its distribution. -/
theorem identDistrib_conj_gaussianEnsemble_of_ne_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℕ} (hβ : β ≠ 1) {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    IdentDistrib
      (fun ω ↦
        (U : Matrix (Fin n) (Fin n) ℂ) *
          gaussianEnsemble β n (fun ij ↦ g ij ω) *
          (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)
      (fun ω ↦ gaussianEnsemble β n (fun ij ↦ g ij ω)) P P := by
  let coeM : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ :=
    Subtype.val
  have hG : HasLaw (fun ω ↦ gueMatrix n (fun ij ↦ g ij ω))
      ((gueMeasure n).map (Real.sqrt v • ·)) P := hasLaw_gueMatrix hg hindep
  have hR : HasLaw (fun ω ↦ gaussianEnsemble β n (fun ij ↦ g ij ω))
      (((gueMeasure n).map (Real.sqrt v • ·)).map coeM) P := by
    simpa only [Function.comp_def, coeM, coe_gueMatrix_eq_gaussianEnsemble hβ] using
      (⟨continuous_subtype_val.aemeasurable, rfl⟩ : HasLaw coeM _ _).comp hG
  have hL : HasLaw
      (fun ω ↦
        (U : Matrix (Fin n) (Fin n) ℂ) *
          gaussianEnsemble β n (fun ij ↦ g ij ω) *
          (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)
      (((gueMeasure n).map (Real.sqrt v • ·)).map coeM) P := by
    have hmap : ((gueMeasure n).map (Real.sqrt v • ·)).map (Matrix.unitaryGroup.hermitianConj U) =
        (gueMeasure n).map (Real.sqrt v • ·) := by
      rw [Measure.map_map_const_smul _ (by fun_prop) _ (map_smul _ _),
        Matrix.unitaryGroup.map_hermitianConj_gueMeasure U]
    have hconjG := (⟨by fun_prop, hmap⟩ :
      HasLaw (Matrix.unitaryGroup.hermitianConj U) _ _).fun_comp hG
    have hcomp := (⟨continuous_subtype_val.aemeasurable, rfl⟩ : HasLaw coeM _ _).fun_comp hconjG
    convert hcomp using 1
    funext ω
    simp [coeM, coe_gueMatrix_eq_gaussianEnsemble hβ]
  exact ⟨hL.aemeasurable, hR.aemeasurable, hL.map_eq.trans hR.map_eq.symm⟩

end ConjugationInvariance

/-! ### Invariant trace-square densities -/

section Densities

variable {n : ℕ}

/-- The real-valued **GOE density** against `TauCeti.symmetricLebesgue n`:
`(n / (4π))^(n / 2) * (n / (2π))^(n(n - 1) / 4) * exp (-n / 4 * tr(H ^ 2))`. -/
def goePDFReal (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ :=
  ((n : ℝ) / (4 * π)) ^ ((n : ℝ) / 2) *
    ((n : ℝ) / (2 * π)) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) *
    Real.exp (-(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace)

/-- The `ℝ≥0∞`-valued **GOE density** against `TauCeti.symmetricLebesgue n`. -/
def goePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (goePDFReal n H)

theorem goePDFReal_def (n : ℕ) :
    goePDFReal n = fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      ((n : ℝ) / (4 * π)) ^ ((n : ℝ) / 2) *
        ((n : ℝ) / (2 * π)) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) *
        Real.exp (-(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace) :=
  (rfl)

theorem goePDF_def (n : ℕ) :
    goePDF n = fun H ↦ ENNReal.ofReal (goePDFReal n H) :=
  (rfl)

@[simp]
theorem goePDFReal_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    goePDFReal 0 H = 1 := by
  simp [goePDFReal]

@[simp]
theorem goePDF_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ)) :
    goePDF 0 H = 1 := by
  simp [goePDF]

theorem goePDFReal_pos (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDFReal n H := by
  rcases n with _ | k
  · simp
  · unfold goePDFReal
    positivity

theorem goePDFReal_nonneg (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ goePDFReal n H :=
  (goePDFReal_pos H).le

theorem goePDF_pos (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDF n H :=
  ENNReal.ofReal_pos.2 (goePDFReal_pos H)

@[simp]
theorem goePDF_ne_top (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n H ≠ ⊤ :=
  ENNReal.ofReal_ne_top

@[simp]
theorem toReal_goePDF (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    (goePDF n H).toReal = goePDFReal n H :=
  ENNReal.toReal_ofReal (goePDFReal_nonneg H)

@[fun_prop]
theorem measurable_goePDFReal (n : ℕ) : Measurable (goePDFReal n) := by
  unfold goePDFReal
  fun_prop

@[fun_prop]
theorem measurable_goePDF (n : ℕ) : Measurable (goePDF n) :=
  (measurable_goePDFReal n).ennreal_ofReal

/-- The GOE density is invariant under orthogonal conjugation. -/
theorem _root_.Matrix.unitaryGroup.goePDFReal_symmetricConj (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n (Matrix.unitaryGroup.symmetricConj O H) = goePDFReal n H := by
  have htr : ((Matrix.unitaryGroup.symmetricConj O H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace =
      ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace := by
    rw [sq, ← selfAdjoint.inner_eq_trace_mul, real_inner_self_eq_norm_sq,
      LinearIsometryEquiv.norm_map, ← real_inner_self_eq_norm_sq, selfAdjoint.inner_eq_trace_mul,
      sq]
  simp only [goePDFReal, htr]

/-- The real-valued **GUE density** against `TauCeti.hermitianLebesgue n`:
`(n / (2π))^(n / 2) * (n / π)^(n(n - 1) / 2) * exp (-n / 2 * Re tr(H ^ 2))`. -/
def guePDFReal (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  ((n : ℝ) / (2 * π)) ^ ((n : ℝ) / 2) *
    ((n : ℝ) / π) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) *
    Real.exp (-(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re)

/-- The `ℝ≥0∞`-valued **GUE density** against `TauCeti.hermitianLebesgue n`. -/
def guePDF (n : ℕ) (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (guePDFReal n H)

theorem guePDFReal_def (n : ℕ) :
    guePDFReal n = fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
      ((n : ℝ) / (2 * π)) ^ ((n : ℝ) / 2) *
        ((n : ℝ) / π) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) *
        Real.exp (-(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re) :=
  (rfl)

theorem guePDF_def (n : ℕ) :
    guePDF n = fun H ↦ ENNReal.ofReal (guePDFReal n H) :=
  (rfl)

@[simp]
theorem guePDFReal_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ)) :
    guePDFReal 0 H = 1 := by
  simp [guePDFReal]

@[simp]
theorem guePDF_zero (H : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ)) :
    guePDF 0 H = 1 := by
  simp [guePDF]

theorem guePDFReal_pos (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDFReal n H := by
  rcases n with _ | k
  · simp
  · unfold guePDFReal
    positivity

theorem guePDFReal_nonneg (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 ≤ guePDFReal n H :=
  (guePDFReal_pos H).le

theorem guePDF_pos (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDF n H :=
  ENNReal.ofReal_pos.2 (guePDFReal_pos H)

@[simp]
theorem guePDF_ne_top (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n H ≠ ⊤ :=
  ENNReal.ofReal_ne_top

@[simp]
theorem toReal_guePDF (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    (guePDF n H).toReal = guePDFReal n H :=
  ENNReal.toReal_ofReal (guePDFReal_nonneg H)

@[fun_prop]
theorem measurable_guePDFReal (n : ℕ) : Measurable (guePDFReal n) := by
  unfold guePDFReal
  fun_prop

@[fun_prop]
theorem measurable_guePDF (n : ℕ) : Measurable (guePDF n) :=
  (measurable_guePDFReal n).ennreal_ofReal

/-- The GUE density is invariant under unitary conjugation. -/
theorem _root_.Matrix.unitaryGroup.guePDFReal_hermitianConj (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n (Matrix.unitaryGroup.hermitianConj U H) = guePDFReal n H := by
  have htr : ((Matrix.unitaryGroup.hermitianConj U H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re =
      ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re := by
    rw [← selfAdjoint.norm_sq_eq_re_trace_sq, LinearIsometryEquiv.norm_map,
      selfAdjoint.norm_sq_eq_re_trace_sq]
  simp only [guePDFReal, htr]

/-- **GOE density with respect to Frobenius volume.** -/
theorem goeMeasure_eq_withDensity_volume (n : ℕ) :
    goeMeasure n =
      volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
        ENNReal.ofReal
          (((n : ℝ) / (4 * π)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
            Real.exp (-(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace)) := by
  rcases n with _ | k
  · simp [volume_symmetricMatrix_eq_smul_symmetricLebesgue, symmetricLebesgue_zero]
  set n : ℕ := k + 1
  have hn : (0 : ℝ) < n := by positivity
  have hc : Real.sqrt (2 / n) ≠ 0 := by positivity
  rw [goeMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity _ hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  have hdim : (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [finrank_symmetricMatrix]
    have heven : Even (n * (n + 1)) := Nat.even_mul_succ_self n
    have hmul : (2 : ℝ) * ((n * (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by
      exact_mod_cast Nat.mul_div_cancel' heven.two_dvd
    linarith
  have hsq : Real.sqrt (2 / (n : ℝ)) ^ 2 = 2 / (n : ℝ) := Real.sq_sqrt (by positivity)
  have hnorm : ‖H‖ ^ 2 = ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace := by
    rw [← real_inner_self_eq_norm_sq, selfAdjoint.inner_eq_trace_mul, sq]
  have hbase : (2 * π * (2 / (n : ℝ))) ^ (-((n : ℝ) * ((n : ℝ) + 1) / 2) / 2) =
      ((n : ℝ) / (4 * π)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
    have hinv : (2 * π * (2 / (n : ℝ)))⁻¹ = (n : ℝ) / (4 * π) := by field_simp; ring
    have hexp : -((n : ℝ) * ((n : ℝ) + 1) / 2) / 2 = -(((n : ℝ) * ((n : ℝ) + 1)) / 4) := by ring
    rw [hexp, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), hinv]
  have hexp_arg : -((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace / (2 * (2 / (n : ℝ))) =
      -(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace := by
    field_simp; ring
  rw [hdim, hsq, hnorm, hbase, hexp_arg]

/-- **GOE invariant density with respect to `TauCeti.symmetricLebesgue n`.** -/
theorem goeMeasure_eq_withDensity_symmetricLebesgue (n : ℕ) :
    goeMeasure n = (symmetricLebesgue n).withDensity (goePDF n) := by
  rcases n with _ | k
  · have h1 : goePDF 0 = 1 := funext goePDF_zero
    simp [symmetricLebesgue_zero, h1]
  set n : ℕ := k + 1
  rw [goeMeasure_eq_withDensity_volume, volume_symmetricMatrix_eq_smul_symmetricLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, goePDF, goePDFReal]
  have h2pow : Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 4) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) := rfl
  rw [h2pow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsum : ((n : ℝ) * ((n : ℝ) + 1)) / 4 =
      (n : ℝ) / 2 + ((n : ℝ) * ((n : ℝ) - 1)) / 4 := by ring
  have hbase : (2 : ℝ) * ((n : ℝ) / (4 * π)) = (n : ℝ) / (2 * π) := by ring
  calc (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) *
        (((n : ℝ) / (4 * π)) ^ (((n : ℝ) * ((n : ℝ) + 1)) / 4) *
          Real.exp (-(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace))
      = ((n : ℝ) / (4 * π)) ^ ((n : ℝ) / 2) *
          ((2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) *
            ((n : ℝ) / (4 * π)) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4)) *
          Real.exp (-(n : ℝ) / 4 * ((H : Matrix (Fin n) (Fin n) ℝ) ^ 2).trace) := by
          rw [hsum, Real.rpow_add (by positivity)]; ring
    _ = _ := by rw [← Real.mul_rpow (by norm_num) (by positivity), hbase]

/-- **GUE density with respect to Frobenius volume.** -/
theorem gueMeasure_eq_withDensity_volume (n : ℕ) :
    gueMeasure n =
      volume.withDensity fun H : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
        ENNReal.ofReal
          (((n : ℝ) / (2 * π)) ^ (((n : ℝ) ^ 2) / 2) *
            Real.exp (-(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re)) := by
  rcases n with _ | k
  · simp [volume_hermitianMatrix_eq_smul_hermitianLebesgue, hermitianLebesgue_zero]
  set n : ℕ := k + 1
  have hn : (0 : ℝ) < n := by positivity
  have hc : (Real.sqrt n)⁻¹ ≠ 0 := by positivity
  rw [gueMeasure_eq_map_stdGaussian, map_smul_stdGaussian_eq_withDensity _ hc]
  refine withDensity_congr_ae (.of_forall fun H ↦ congrArg ENNReal.ofReal ?_)
  have hdim : (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ) =
      (n : ℝ) ^ 2 := by
    rw [finrank_hermitianMatrix]
    push_cast
    rfl
  have hsq : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hn.le]
  have hbase : (2 * π * (n : ℝ)⁻¹) ^ (-((n : ℝ) ^ 2) / 2) =
      ((n : ℝ) / (2 * π)) ^ (((n : ℝ) ^ 2) / 2) := by
    have hinv : (2 * π * (n : ℝ)⁻¹)⁻¹ = (n : ℝ) / (2 * π) := by field_simp
    have hexp : -((n : ℝ) ^ 2) / 2 = -(((n : ℝ) ^ 2) / 2) := by ring
    rw [hexp, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), hinv]
  have hexp_arg : -((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re / (2 * (n : ℝ)⁻¹) =
      -(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re := by
    field_simp
  rw [hdim, hsq, selfAdjoint.norm_sq_eq_re_trace_sq, hbase, hexp_arg]

/-- **GUE invariant density with respect to `TauCeti.hermitianLebesgue n`.** -/
theorem gueMeasure_eq_withDensity_hermitianLebesgue (n : ℕ) :
    gueMeasure n = (hermitianLebesgue n).withDensity (guePDF n) := by
  rcases n with _ | k
  · have h1 : guePDF 0 = 1 := funext guePDF_zero
    simp [hermitianLebesgue_zero, h1]
  set n : ℕ := k + 1
  rw [gueMeasure_eq_withDensity_volume, volume_hermitianMatrix_eq_smul_hermitianLebesgue,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun H ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, guePDF, guePDFReal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hcard : ((n * (n - 1) / 2 : ℕ) : ℝ) = ((n : ℝ) * ((n : ℝ) - 1)) / 2 := by
    have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
    have hmul : (2 : ℝ) * ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' heven.two_dvd
      have h2 : ((2 * (n * (n - 1) / 2) : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) :=
        congrArg Nat.cast h1
      have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simp [n]
      push_cast at h2
      rwa [hsub] at h2
    linarith
  have hpow : ((2 : ℝ) ^ (n * (n - 1) / 2)) = (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) := by
    rw [← Real.rpow_natCast, hcard]
  have hsum : ((n : ℝ) ^ 2) / 2 = (n : ℝ) / 2 + ((n : ℝ) * ((n : ℝ) - 1)) / 2 := by ring
  have hbase : (2 : ℝ) * ((n : ℝ) / (2 * π)) = (n : ℝ) / π := by ring
  calc (2 : ℝ) ^ (n * (n - 1) / 2) *
        (((n : ℝ) / (2 * π)) ^ (((n : ℝ) ^ 2) / 2) *
          Real.exp (-(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re))
      = ((n : ℝ) / (2 * π)) ^ ((n : ℝ) / 2) *
          ((2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) *
            ((n : ℝ) / (2 * π)) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2)) *
          Real.exp (-(n : ℝ) / 2 * ((H : Matrix (Fin n) (Fin n) ℂ) ^ 2).trace.re) := by
          rw [hpow, hsum, Real.rpow_add (by positivity)]; ring
    _ = _ := by rw [← Real.mul_rpow (by norm_num) (by positivity), hbase]

/-- The Radon–Nikodym derivative of `goeMeasure n` against `TauCeti.symmetricLebesgue n` is
`goePDF n`. -/
theorem rnDeriv_goeMeasure (n : ℕ) :
    (goeMeasure n).rnDeriv (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue]
  exact Measure.rnDeriv_withDensity _ (measurable_goePDF n)

/-- The Radon–Nikodym derivative of `gueMeasure n` against `TauCeti.hermitianLebesgue n` is
`guePDF n`. -/
theorem rnDeriv_gueMeasure (n : ℕ) :
    (gueMeasure n).rnDeriv (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue]
  exact Measure.rnDeriv_withDensity _ (measurable_guePDF n)

end Densities

/-! ### Equivalence of entry and invariant-density characterizations -/

section EntryCharacterization

variable {n : ℕ}

/-- Under `goeMeasure n`, the upper-triangular coordinates are independent centered Gaussians with
variance `2 / n` on the diagonal and `1 / n` off it. -/
theorem map_symmetricCoordinates_goeMeasure (n : ℕ) :
    (goeMeasure n).map (symmetricCoordinates n) =
      Measure.pi fun ij : upperTriangle n ↦
        gaussianReal 0 (if ij.1.1 = ij.1.2 then 2 / (n : ℝ≥0) else 1 / (n : ℝ≥0)) := by
  let s : upperTriangle n → ℝ := fun ij ↦
    (Real.sqrt n)⁻¹ * if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1
  have hcomp : symmetricCoordinates n ∘ goeMatrix n =
      (fun x (ij : upperTriangle n) ↦ s ij * x ij) ∘
        (fun g (ij : upperTriangle n) ↦ g ij.1) := by
    funext g ij
    simp only [Function.comp_apply, goeMatrix, ContinuousLinearEquiv.apply_symm_apply, s]
    split_ifs <;> ring
  rw [goeMeasure,
    Measure.map_map (symmetricCoordinates n).continuous.measurable measurable_goeMatrix,
    hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_restrict_upperTriangle_pi_gaussianReal, Measure.pi_map_pi fun _ ↦ by fun_prop]
  congr 1
  funext ij
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  apply NNReal.eq
  by_cases h : ij.1.1 = ij.1.2 <;> simp [h, s, mul_pow, div_eq_mul_inv, mul_comm]

/-- Under `gueMeasure n`, the real Hermitian coordinates (`(H i i).re` on the diagonal,
`(H i j).re` and `(H i j).im` above it) are independent centered Gaussians with variance `1 / n` on
the diagonal and `1 / (2n)` off it. -/
theorem map_hermitianCoordinates_gueMeasure (n : ℕ) :
    (gueMeasure n).map (hermitianCoordinates n) =
      Measure.pi fun p : Fin n × Fin n ↦
        gaussianReal 0 (if p.1 = p.2 then 1 / (n : ℝ≥0) else 1 / (2 * (n : ℝ≥0))) := by
  let s : Fin n × Fin n → ℝ := fun p ↦
    (Real.sqrt n)⁻¹ * if p.1 = p.2 then 1 else (Real.sqrt 2)⁻¹
  have hcomp : hermitianCoordinates n ∘ gueMatrix n =
      fun g (p : Fin n × Fin n) ↦ s p * g p := by
    funext g p
    simp only [Function.comp_apply, gueMatrix, ContinuousLinearEquiv.apply_symm_apply, s]
    split_ifs <;> ring
  rw [gueMeasure,
    Measure.map_map (hermitianCoordinates n).continuous.measurable measurable_gueMatrix,
    hcomp, Measure.pi_map_pi fun _ ↦ by fun_prop]
  congr 1
  funext p
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  apply NNReal.eq
  by_cases h : p.1 = p.2 <;> simp [h, s, mul_pow, mul_comm]

/-- **Entry characterization of the GOE.** A random real symmetric matrix has law `goeMeasure n`
if and only if its upper-triangular entries are independent centered Gaussians with variance
`2 / n` on the diagonal and `1 / n` strictly above it. -/
theorem hasLaw_goeMeasure_iff_entries {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      iIndepFun (fun ij : upperTriangle n ↦ fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
          P ∧
        ∀ ij : upperTriangle n,
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
            (gaussianReal 0 (if ij.1.1 = ij.1.2 then 2 / (n : ℝ≥0) else 1 / (n : ℝ≥0))) P := by
  simpa only [symmetricCoordinatesMeasurableEquiv_coe, symmetricCoordinates_apply] using
    (symmetricCoordinatesMeasurableEquiv n).hasLaw_iff_iIndepFun_and_hasLaw (H := H)
      (by simpa only [symmetricCoordinatesMeasurableEquiv_coe] using
        map_symmetricCoordinates_goeMeasure n)

/-- **Equivalence of the entry and invariant-density characterizations of the GOE** (AGZ (2.5.1)).
-/
theorem hasLaw_goe_withDensity_iff_entries {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H ((symmetricLebesgue n).withDensity (goePDF n)) P ↔
      iIndepFun (fun ij : upperTriangle n ↦ fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
          P ∧
        ∀ ij : upperTriangle n,
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
            (gaussianReal 0 (if ij.1.1 = ij.1.2 then 2 / (n : ℝ≥0) else 1 / (n : ℝ≥0))) P := by
  rw [← goeMeasure_eq_withDensity_symmetricLebesgue, hasLaw_goeMeasure_iff_entries]

/-- **Entry characterization of the GUE.** A random complex Hermitian matrix has law `gueMeasure n`
if and only if its real Hermitian coordinates (`TauCeti.hermitianCoordinates n`: diagonal entries
and real and imaginary parts of strictly upper-triangular entries) are independent centered
Gaussians with variance `1 / n` on the diagonal and `1 / (2n)` off it. -/
theorem hasLaw_gueMeasure_iff_entries {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      iIndepFun (fun p : Fin n × Fin n ↦ fun ω ↦ hermitianCoordinates n (H ω) p) P ∧
        ∀ p : Fin n × Fin n,
          HasLaw (fun ω ↦ hermitianCoordinates n (H ω) p)
            (gaussianReal 0 (if p.1 = p.2 then 1 / (n : ℝ≥0) else 1 / (2 * (n : ℝ≥0)))) P := by
  simpa only [hermitianCoordinatesMeasurableEquiv_coe] using
    (hermitianCoordinatesMeasurableEquiv n).hasLaw_iff_iIndepFun_and_hasLaw (H := H)
      (by simpa only [hermitianCoordinatesMeasurableEquiv_coe] using
        map_hermitianCoordinates_gueMeasure n)

/-- **Equivalence of the entry and invariant-density characterizations of the GUE** (AGZ (2.5.1)).
-/
theorem hasLaw_gue_withDensity_iff_entries {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H ((hermitianLebesgue n).withDensity (guePDF n)) P ↔
      iIndepFun (fun p : Fin n × Fin n ↦ fun ω ↦ hermitianCoordinates n (H ω) p) P ∧
        ∀ p : Fin n × Fin n,
          HasLaw (fun ω ↦ hermitianCoordinates n (H ω) p)
            (gaussianReal 0 (if p.1 = p.2 then 1 / (n : ℝ≥0) else 1 / (2 * (n : ℝ≥0)))) P := by
  rw [← gueMeasure_eq_withDensity_hermitianLebesgue, hasLaw_gueMeasure_iff_entries]

end EntryCharacterization

end Probability

end TauCeti

namespace ProbabilityTheory

open MeasureTheory TauCeti.Probability

/-- Orthogonal conjugation preserves the GOE law of a random real symmetric matrix. -/
theorem HasLaw.symmetricConj_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.symmetricConj O (H ω)) (goeMeasure n) P :=
  (⟨by fun_prop, Matrix.unitaryGroup.map_symmetricConj_goeMeasure O⟩ :
    HasLaw (Matrix.unitaryGroup.symmetricConj O) (goeMeasure n) (goeMeasure n)).fun_comp hH

/-- Unitary conjugation preserves the GUE law of a random complex Hermitian matrix. -/
theorem HasLaw.hermitianConj_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.hermitianConj U (H ω)) (gueMeasure n) P :=
  (⟨by fun_prop, Matrix.unitaryGroup.map_hermitianConj_gueMeasure U⟩ :
    HasLaw (Matrix.unitaryGroup.hermitianConj U) (gueMeasure n) (gueMeasure n)).fun_comp hH

/-- A random symmetric matrix with the GOE law has a density against `TauCeti.symmetricLebesgue`. -/
theorem HasLaw.hasPDF_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) : HasPDF H P (TauCeti.symmetricLebesgue n) :=
  TauCeti.Probability.hasPDF_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue])

/-- The density against `TauCeti.symmetricLebesgue` of a GOE random matrix is `goePDF`. -/
theorem HasLaw.pdf_eq_goePDF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) :
    pdf H P (TauCeti.symmetricLebesgue n) =ᵐ[TauCeti.symmetricLebesgue n] goePDF n :=
  TauCeti.Probability.pdf_eq_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue])

/-- A random Hermitian matrix with the GUE law has a density against `TauCeti.hermitianLebesgue`. -/
theorem HasLaw.hasPDF_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) : HasPDF H P (TauCeti.hermitianLebesgue n) :=
  TauCeti.Probability.hasPDF_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue])

/-- The density against `TauCeti.hermitianLebesgue` of a GUE random matrix is `guePDF`. -/
theorem HasLaw.pdf_eq_guePDF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    pdf H P (TauCeti.hermitianLebesgue n) =ᵐ[TauCeti.hermitianLebesgue n] guePDF n :=
  TauCeti.Probability.pdf_eq_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue])

end ProbabilityTheory
