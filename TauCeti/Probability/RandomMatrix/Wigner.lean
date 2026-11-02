/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.MeasureTheory.MeasurableSpace.Pi

/-!
# Wigner matrices

A Wigner matrix of size `n` is read off the top-left `n × n` corner of an infinite array of
random entries: complex entries `ξ (i, j)` at the strictly upper positions `i < j`, their complex
conjugates below the diagonal, and real entries `η i` on the diagonal. The normalised matrix
`Hₙ = Wₙ/√n` built this way is Hermitian at every sample point. Placing all sizes on one infinite
array is the coupling used by almost-sure global laws such as the semicircle law.

This file defines `TauCeti.wignerMatrix` and proves the structural facts consumed by the moment
and resolvent methods:

* the entry formulas and `wignerMatrix_isHermitian`;
* the matrix depends only on the entries in its corner (`wignerMatrix_congr`), and the top-left
  `m × m` corner of `Hₙ` is `√(m/n) Hₘ` (`submatrix_castLE_wignerMatrix`);
* measurability in the sample point;
* when the entries are independent, the minor `Hₙ` is independent of the off-diagonal entries of
  the row and column removed from `Hₙ₊₁` (`indepFun_wignerMatrix_column`), and the law of `Hₙ`
  depends only on the laws of the entries (`identDistrib_wignerMatrix`);
* the normalisation check `E trₙ Hₙ² = (σ² + (n - 1) s)/n` when the diagonal entries have second
  moment `σ²` and the off-diagonal ones second absolute moment `s`
  (`integral_re_trace_wignerMatrix_mul_self`).

Centring, the second-moment normalisation and independence of the entries are not properties of
the constructor: each theorem that uses one states it as a hypothesis.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.4.
-/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace TauCeti

/-- The strictly upper-triangular positions `(i, j)`, `i < j`, of a matrix indexed by `ℕ`. -/
abbrev StrictUpper := {ij : ℕ × ℕ // ij.1 < ij.2}

variable {Ω : Type*}

/-- The normalised Wigner matrix `Wₙ/√n` built from the top-left `n × n` corner of an infinite
array: complex entries `ξ` above the diagonal, their conjugates below it, and real entries `η` on
it. A real symmetric Wigner matrix is the case of real-valued `ξ`. -/
noncomputable def wignerMatrix (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ ((Real.sqrt n)⁻¹ : ℂ) *
    if h : i.val < j.val then ξ ⟨(i.val, j.val), h⟩ ω
    else if h' : j.val < i.val then star (ξ ⟨(j.val, i.val), h'⟩ ω)
    else (η i.val ω : ℂ)

section Deterministic

variable (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) {n : ℕ} (ω : Ω)

/-- Above the diagonal the Wigner matrix has entry `ξ (i, j)/√n`. -/
@[simp]
theorem wignerMatrix_apply_of_lt {i j : Fin n} (h : i.val < j.val) :
    wignerMatrix ξ η n ω i j = (Real.sqrt n : ℂ)⁻¹ * ξ ⟨(i.val, j.val), h⟩ ω := by
  rw [wignerMatrix, of_apply, dite_eq_left h]

/-- Below the diagonal the Wigner matrix has entry `conj (ξ (j, i))/√n`. -/
@[simp]
theorem wignerMatrix_apply_of_gt {i j : Fin n} (h : j.val < i.val) :
    wignerMatrix ξ η n ω i j = (Real.sqrt n : ℂ)⁻¹ * star (ξ ⟨(j.val, i.val), h⟩ ω) := by
  rw [wignerMatrix, of_apply, dite_eq_right h.not_gt, dite_eq_left h]

/-- On the diagonal the Wigner matrix has entry `η i/√n`. -/
@[simp]
theorem wignerMatrix_apply_self (i : Fin n) :
    wignerMatrix ξ η n ω i i = (Real.sqrt n : ℂ)⁻¹ * η i.val ω := by
  simp [wignerMatrix]

/-- The normalised Wigner matrix is Hermitian for every sample point. -/
theorem wignerMatrix_isHermitian (n : ℕ) : (wignerMatrix ξ η n ω).IsHermitian := by
  ext i j
  rw [conjTranspose_apply]
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [wignerMatrix_apply_of_lt ξ η ω h, wignerMatrix_apply_of_gt ξ η ω h]
    simp [Complex.conj_ofReal]
  · obtain rfl := Fin.ext h
    simp [Complex.conj_ofReal]
  · rw [wignerMatrix_apply_of_lt ξ η ω h, wignerMatrix_apply_of_gt ξ η ω h]
    simp [Complex.conj_ofReal]

variable {ξ η}

/-- The Wigner matrix of size `n` depends only on the entries of the top-left `n × n` corner. -/
theorem wignerMatrix_congr {Ω' : Type*} {ξ' : StrictUpper → Ω' → ℂ} {η' : ℕ → Ω' → ℝ}
    {ω' : Ω'} (hξ : ∀ ij : StrictUpper, ij.1.2 < n → ξ ij ω = ξ' ij ω')
    (hη : ∀ i < n, η i ω = η' i ω') :
    wignerMatrix ξ η n ω = wignerMatrix ξ' η' n ω' := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [wignerMatrix_apply_of_lt _ _ _ h, wignerMatrix_apply_of_lt _ _ _ h, hξ ⟨_, h⟩ j.2]
  · obtain rfl := Fin.ext h
    rw [wignerMatrix_apply_self, wignerMatrix_apply_self, hη _ i.2]
  · rw [wignerMatrix_apply_of_gt _ _ _ h, wignerMatrix_apply_of_gt _ _ _ h, hξ ⟨_, h⟩ i.2]

/-- The top-left `m × m` corner of the normalised Wigner matrix of size `n ≥ m` is `√(m/n)`
times the normalised Wigner matrix of size `m`. -/
theorem submatrix_castLE_wignerMatrix {m : ℕ} (hmn : m ≤ n) :
    (wignerMatrix ξ η n ω).submatrix (Fin.castLE hmn) (Fin.castLE hmn) =
      ((Real.sqrt m / Real.sqrt n : ℝ) : ℂ) • wignerMatrix ξ η m ω := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Subsingleton.elim _ _
  have hm' : (Real.sqrt m : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne'
  have key (x : ℂ) : (Real.sqrt n : ℂ)⁻¹ * x =
      ((Real.sqrt m / Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt m : ℂ)⁻¹ * x) := by
    rw [Complex.ofReal_div, div_mul_eq_mul_div, mul_inv_cancel_left₀ hm', div_eq_inv_mul]
  ext i j
  rw [submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact (wignerMatrix_apply_of_lt ξ η ω (i := Fin.castLE hmn i) (j := Fin.castLE hmn j) h).trans
      ((key _).trans (by rw [wignerMatrix_apply_of_lt ξ η ω h]; rfl))
  · obtain rfl := Fin.ext h
    rw [wignerMatrix_apply_self, wignerMatrix_apply_self]
    exact key _
  · exact (wignerMatrix_apply_of_gt ξ η ω (i := Fin.castLE hmn i) (j := Fin.castLE hmn j) h).trans
      ((key _).trans (by rw [wignerMatrix_apply_of_gt ξ η ω h]; rfl))

end Deterministic

section Measurability

variable [MeasurableSpace Ω] {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The Wigner matrix of size `n` as a function of the whole entry array, embedded in `ℂ`. -/
private noncomputable def wignerOfArray (n : ℕ) (g : StrictUpper ⊕ ℕ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  wignerMatrix (fun ij g ↦ g (.inl ij)) (fun i g ↦ (g (.inr i)).re) n g

private theorem measurable_wignerOfArray (n : ℕ) : Measurable (wignerOfArray n) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerOfArray, wignerMatrix_apply_of_lt _ _ _ h]
    fun_prop
  · obtain rfl := Fin.ext h
    simp only [wignerOfArray, wignerMatrix_apply_self]
    fun_prop
  · simp only [wignerOfArray, wignerMatrix_apply_of_gt _ _ _ h]
    exact measurable_const.mul (continuous_star.measurable.comp (measurable_pi_apply _))

omit [MeasurableSpace Ω] in
private theorem wignerOfArray_comp (n : ℕ) :
    wignerOfArray n ∘ (fun ω k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k ω) = wignerMatrix ξ η n := by
  ext1 ω
  exact wignerMatrix_congr ω (fun _ _ ↦ rfl) (fun _ _ ↦ by simp)

private theorem aemeasurable_array {P : Measure Ω} (hξ : ∀ ij, AEMeasurable (ξ ij) P)
    (hη : ∀ i, AEMeasurable (η i) P) (k : StrictUpper ⊕ ℕ) :
    AEMeasurable (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P := by
  cases k with
  | inl ij => exact hξ ij
  | inr i => exact Complex.measurable_ofReal.comp_aemeasurable (hη i)

/-- A Wigner matrix with measurable entries is a measurable random matrix. -/
theorem measurable_wignerMatrix (hξ : ∀ ij, Measurable (ξ ij)) (hη : ∀ i, Measurable (η i))
    (n : ℕ) : Measurable (wignerMatrix ξ η n) := by
  rw [← wignerOfArray_comp]
  refine (measurable_wignerOfArray n).comp (measurable_pi_iff.2 fun k ↦ ?_)
  cases k with
  | inl ij => exact hξ ij
  | inr i => exact Complex.measurable_ofReal.comp (hη i)

/-- A Wigner matrix with almost everywhere measurable entries is almost everywhere
measurable. -/
theorem aemeasurable_wignerMatrix {P : Measure Ω} (hξ : ∀ ij, AEMeasurable (ξ ij) P)
    (hη : ∀ i, AEMeasurable (η i) P) (n : ℕ) : AEMeasurable (wignerMatrix ξ η n) P := by
  rw [← wignerOfArray_comp]
  exact (measurable_wignerOfArray n).comp_aemeasurable
    (aemeasurable_pi_iff.2 (aemeasurable_array hξ hη))

end Measurability

section Independence

variable [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The indices of the entries of the top-left `n × n` corner. -/
private noncomputable def cornerIndices (n : ℕ) : Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ Finset.range n).subtype fun ij ↦ ij.1 < ij.2).disjSum (Finset.range n)

/-- The indices of the strictly upper entries of column `n`. -/
private noncomputable def columnIndices (n : ℕ) : Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ {n}).subtype fun ij ↦ ij.1 < ij.2).disjSum ∅

private theorem inl_mem_cornerIndices {n : ℕ} {ij : StrictUpper} (h : ij.1.2 < n) :
    Sum.inl ij ∈ cornerIndices n := by
  simp [cornerIndices, h, ij.2.trans h]

private theorem inr_mem_cornerIndices {n i : ℕ} (h : i < n) : Sum.inr i ∈ cornerIndices n := by
  simp [cornerIndices, h]

private theorem disjoint_cornerIndices_columnIndices (n : ℕ) :
    Disjoint (cornerIndices n) (columnIndices n) := by
  rw [Finset.disjoint_left]
  rintro (ij | i) h₁ h₂
  · simp only [cornerIndices, columnIndices, Finset.inl_mem_disjSum, Finset.mem_subtype,
      Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h₁ h₂
    omega
  · simp [columnIndices] at h₂

/-- For independent entries, the Wigner matrix of size `n` (the scaled top-left minor of the
matrix of size `n + 1`) is independent of the strictly upper entries `ξ (i, n)`, `i < n`, of the
row and column removed from the matrix of size `n + 1`. -/
theorem indepFun_wignerMatrix_column (hξ : ∀ ij, AEMeasurable (ξ ij) P)
    (hη : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (n : ℕ) :
    IndepFun (wignerMatrix ξ η n) (fun ω (i : Fin n) ↦ ξ ⟨(i.val, n), i.2⟩ ω) P := by
  have hcol (i : Fin n) : (Sum.inl ⟨(i.val, n), i.2⟩ : StrictUpper ⊕ ℕ) ∈ columnIndices n := by
    simp only [columnIndices, Finset.inl_mem_disjSum, Finset.mem_subtype, Finset.mem_product,
      Finset.mem_range, Finset.mem_singleton]
    exact ⟨i.2, trivial⟩
  have hφ : Measurable (wignerOfArray n ∘
      fun g : cornerIndices n → ℂ ↦ Function.extend Subtype.val g (fun _ ↦ (0 : ℂ))) :=
    (measurable_wignerOfArray n).comp (MeasureTheory.measurable_extend _ _)
  have hψ : Measurable fun (g : columnIndices n → ℂ) (i : Fin n) ↦ g ⟨_, hcol i⟩ :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  refine ((hindep.indepFun_finset₀ _ _ (disjoint_cornerIndices_columnIndices n)
    (aemeasurable_array hξ hη)).comp hφ hψ).congr (.of_forall fun ω ↦ ?_)
      (.of_forall fun ω ↦ rfl)
  simp only [Function.comp_apply, wignerOfArray]
  refine wignerMatrix_congr _ (fun ij hij ↦ ?_) (fun i hi ↦ ?_)
  · rw [Function.extend_val_apply (inl_mem_cornerIndices hij)]
    rfl
  · rw [Function.extend_val_apply (inr_mem_cornerIndices hi)]
    simp

/-- The law of a Wigner matrix with independent entries depends only on the laws of the
entries: two arrays of independent entries with identically distributed coordinates give
identically distributed Wigner matrices of every size. -/
theorem identDistrib_wignerMatrix {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {ξ' : StrictUpper → Ω' → ℂ} {η' : ℕ → Ω' → ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hindep' : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ' (fun i ω ↦ (η' i ω : ℂ)) k) P')
    (hξξ' : ∀ ij, IdentDistrib (ξ ij) (ξ' ij) P P') (hηη' : ∀ i, IdentDistrib (η i) (η' i) P P')
    (n : ℕ) : IdentDistrib (wignerMatrix ξ η n) (wignerMatrix ξ' η' n) P P' := by
  have h (k : StrictUpper ⊕ ℕ) : IdentDistrib (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k)
      (Sum.elim ξ' (fun i ω ↦ (η' i ω : ℂ)) k) P P' := by
    cases k with
    | inl ij => exact hξξ' ij
    | inr i => exact (hηη' i).comp Complex.measurable_ofReal
  rw [← wignerOfArray_comp, ← wignerOfArray_comp]
  exact (IdentDistrib.pi h hindep hindep').comp (measurable_wignerOfArray n)

end Independence

section SecondMoment

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

variable [MeasurableSpace Ω] {P : Measure Ω}

private theorem integral_norm_wignerMatrix_apply_sq {σ2 s : ℝ}
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) (hη : ∀ i, ∫ ω, η i ω ^ 2 ∂P = σ2) {n : ℕ}
    (i j : Fin n) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P = (n : ℝ)⁻¹ * if i = j then σ2 else s := by
  have hn : ‖(Real.sqrt n : ℂ)⁻¹‖ ^ 2 = (n : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, norm_mul, mul_pow, hn, integral_const_mul,
      hξ, Fin.ne_of_lt h, ↓reduceIte]
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self, norm_mul, mul_pow, hn, integral_const_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hη, ↓reduceIte]
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, norm_mul, norm_star, mul_pow, hn,
      integral_const_mul, hξ, Fin.ne_of_gt h, ↓reduceIte]

private theorem integrable_norm_wignerMatrix_apply_sq
    (hξ : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hη : ∀ i, Integrable (fun ω ↦ η i ω ^ 2) P)
    {n : ℕ} (i j : Fin n) : Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω i j‖ ^ 2) P := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, norm_mul, mul_pow]
    exact (hξ _).const_mul _
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    exact (hη _).const_mul _
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, norm_mul, norm_star, mul_pow]
    exact (hξ _).const_mul _

/-- **Normalisation of Wigner matrices.** If the diagonal entries have second moment `σ²` and
the strictly upper entries have second absolute moment `s`, then the expected normalised trace of
`Hₙ²` is `(σ² + (n - 1) s)/n`. With `s = 1` this is `E trₙ Hₙ² = (nσ² + n(n - 1))/n² → 1`; no
independence or centring is needed. -/
theorem integral_re_trace_wignerMatrix_mul_self {σ2 s : ℝ}
    (hξi : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (hηi : ∀ i, Integrable (fun ω ↦ η i ω ^ 2) P) (hη : ∀ i, ∫ ω, η i ω ^ 2 ∂P = σ2) (n : ℕ) :
    ∫ ω, ((n : ℂ)⁻¹ * (wignerMatrix ξ η n ω * wignerMatrix ξ η n ω).trace).re ∂P =
      (σ2 + (n - 1) * s) / n := by
  have hsum (i : Fin n) : ∑ j : Fin n, (n : ℝ)⁻¹ * (if i = j then σ2 else s) =
      (n : ℝ)⁻¹ * (σ2 + (n - 1) * s) := by
    have h (j : Fin n) : (if i = j then σ2 else s) = s + if i = j then σ2 - s else 0 := by
      split_ifs <;> ring
    simp only [← Finset.mul_sum, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- `trₙ Hₙ² = n⁻¹ ∑ᵢⱼ |Hᵢⱼ|²` because `Hₙ` is Hermitian.
  have htrace (ω : Ω) : (wignerMatrix ξ η n ω * wignerMatrix ξ η n ω).trace =
      ((∑ i, ∑ j, ‖wignerMatrix ξ η n ω i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [trace, diag_apply, mul_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← (wignerMatrix_isHermitian ξ η ω n).apply j i, Complex.star_def, Complex.mul_conj']
  simp_rw [htrace, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ integrable_norm_wignerMatrix_apply_sq hξi hηi i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ integrable_norm_wignerMatrix_apply_sq hξi hηi _ j,
    integral_norm_wignerMatrix_apply_sq hξ hη, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · field_simp

end SecondMoment

end TauCeti
