/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.MeasureTheory.MeasurableSpace.Pi
public import TauCeti.LinearAlgebra.Matrix.Trace.Hermitian
public import TauCeti.Analysis.Matrix.Frobenius

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
* the Hermitian trace-square identity `Matrix.IsHermitian.trace_mul_self_eq_sum_norm_sq`;
* the matrix depends only on the entries in its corner (`wignerMatrix_congr`,
  `wignerMatrix_ite_lt`), and the top-left `m × m` corner of `Hₙ` is `√(m/n) Hₘ`
  (`submatrix_castLE_wignerMatrix`);
* measurability in the sample point from corner entries (`measurable_wignerMatrix`,
  `aemeasurable_wignerMatrix`);
* the fixed-size product-law characterization `hasLaw_wignerMatrix_of_iIndepFun`;
* when the entries are independent, the minor `Hₙ` is independent of the off-diagonal entries of
  the row and column removed from `Hₙ₊₁` (`indepFun_wignerMatrix_column`); the same holds for
  the actual principal submatrix of `Hₙ₊₁` (`indepFun_submatrix_castSucc_wignerMatrix`),
  independence restricts to the `< n` corner (`iIndepFun_sumElim_ofReal_subtype_lt`), and the law
  of `Hₙ` depends only on the laws of the entries (`identDistrib_wignerMatrix`). For zero
  diagonal, deleting any index gives a minor independent of the removed off-diagonal column
  (`indepFun_submatrix_wignerMatrix_zero_column`);
* entries at distinct off-diagonal unordered positions, and their squared absolute values, are
  independent whenever the corner upper entries are (`iIndepFun_wignerMatrix_apply_of_ne`,
  `iIndepFun_norm_wignerMatrix_apply_sq_of_ne`);
* centred corner entries give centred matrix entries (`integral_wignerMatrix_apply_eq_zero`), `Lᵖ`
  corner entries give `Lᵖ` matrix entries (`memLp_wignerMatrix_apply`), and a product of `k` matrix
  entries is integrable when the corner entries lie in `Lᵏ`
  (`integrable_prod_wignerMatrix_apply`);
* the normalisation check `E trₙ Hₙ² = (σ² + (n - 1) s)/n` when the diagonal entries have second
  moment `σ²` and the off-diagonal ones second absolute moment `s`
  (`integral_re_trace_wignerMatrix_mul_self`), and its consequence that two Wigner arrays sharing
  a diagonal whose upper differences have second absolute moment `s` differ at size `n + 1` by
  expected squared Frobenius norm `n s` (`integral_norm_wignerMatrix_sub_sq`).

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
open scoped ENNReal

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

noncomputable section

/-- Strictly upper-triangular positions in a fixed finite matrix. -/
abbrev StrictUpperFin (n : ℕ) := {ij : Fin n × Fin n // ij.1.val < ij.2.val}

/-- Convert a finite upper-triangular position to the index type used by `wignerMatrix`. -/
def wignerUpperIndex {n : ℕ} (u : StrictUpperFin n) : StrictUpper :=
  ⟨(u.val.1.val, u.val.2.val), by exact_mod_cast u.property⟩

/-- Reading the row and column labels of a finite upper coordinate in the infinite array. -/
@[simp]
theorem wignerUpperIndex_val {n : ℕ} (u : StrictUpperFin n) :
    (wignerUpperIndex u).val = (u.val.1.val, u.val.2.val) :=
  (rfl)

/-- Coordinate labels for a finite Wigner matrix: upper-triangular entries and its diagonal. -/
abbrev WignerCoordinateIndex (n : ℕ) := StrictUpperFin n ⊕ Fin n

/-- The value type of a Wigner coordinate, complex above the diagonal and real on the diagonal. -/
abbrev WignerCoordinateType {n : ℕ} : WignerCoordinateIndex n → Type
  | .inl _ => ℂ
  | .inr _ => ℝ

/-- Measurable-space instance for each coordinate type. -/
instance wignerCoordinateMeasurableSpace {n : ℕ} (k : WignerCoordinateIndex n) :
    MeasurableSpace (WignerCoordinateType k) := by
  cases k <;> infer_instance

/-- The family of coordinate laws for a finite Wigner matrix. -/
def wignerCoordinateMeasures {n : ℕ} (μ : StrictUpperFin n → Measure ℂ)
    (ν : Fin n → Measure ℝ) :
    (k : WignerCoordinateIndex n) → Measure (WignerCoordinateType k)
  | .inl u => μ u
  | .inr i => ν i

/-- The coordinate law above the diagonal. -/
@[simp]
theorem wignerCoordinateMeasures_inl {n : ℕ} (μ : StrictUpperFin n → Measure ℂ)
    (ν : Fin n → Measure ℝ) (u : StrictUpperFin n) :
    wignerCoordinateMeasures μ ν (.inl u) = μ u := by
  simp [wignerCoordinateMeasures]

/-- The coordinate law on the diagonal. -/
@[simp]
theorem wignerCoordinateMeasures_inr {n : ℕ} (μ : StrictUpperFin n → Measure ℂ)
    (ν : Fin n → Measure ℝ) (i : Fin n) :
    wignerCoordinateMeasures μ ν (.inr i) = ν i := by
  simp [wignerCoordinateMeasures]

/-- The finite family of random variables used to construct a Wigner matrix. -/
def wignerCoordinates {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (k : WignerCoordinateIndex n) → WignerCoordinateType k
  | .inl u => ξ (wignerUpperIndex u) ω
  | .inr i => η i.val ω

/-- The coordinate above the diagonal comes from the infinite upper-triangular array. -/
@[simp]
theorem wignerCoordinates_inl {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (u : StrictUpperFin n) :
    wignerCoordinates ξ η n ω (.inl u) = ξ (wignerUpperIndex u) ω := by
  simp [wignerCoordinates]

/-- The diagonal coordinate comes from the diagonal array. -/
@[simp]
theorem wignerCoordinates_inr {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (i : Fin n) :
    wignerCoordinates ξ η n ω (.inr i) = η i.val ω := by
  simp [wignerCoordinates]

/-- Construct the normalized Wigner matrix from its finite vector of coordinates. -/
def wignerMatrixOfCoordinates {n : ℕ}
    (x : (k : WignerCoordinateIndex n) → WignerCoordinateType k) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ((Real.sqrt n)⁻¹ : ℂ) *
    if h : i.val < j.val then x (Sum.inl ⟨(i, j), h⟩)
    else if h' : j.val < i.val then star (x (Sum.inl ⟨(j, i), h'⟩))
    else (x (Sum.inr i) : ℂ)

/-- The entries of the finite-coordinate construction. -/
@[simp]
theorem wignerMatrixOfCoordinates_apply {n : ℕ}
    (x : (k : WignerCoordinateIndex n) → WignerCoordinateType k) (i j : Fin n) :
    wignerMatrixOfCoordinates x i j = ((Real.sqrt n)⁻¹ : ℂ) *
      if h : i.val < j.val then x (Sum.inl ⟨(i, j), h⟩)
      else if h' : j.val < i.val then star (x (Sum.inl ⟨(j, i), h'⟩))
      else (x (Sum.inr i) : ℂ) := by
  simp [wignerMatrixOfCoordinates]

/-- The coordinate construction agrees with `wignerMatrix`. -/
theorem wignerMatrix_eq_wignerMatrixOfCoordinates {Ω : Type*}
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    wignerMatrix ξ η n ω =
      wignerMatrixOfCoordinates (wignerCoordinates ξ η n ω) := by
  ext i j
  simp [wignerMatrix, wignerMatrixOfCoordinates, wignerCoordinates, wignerUpperIndex]

/-- The map from a finite vector of Wigner coordinates to its matrix is measurable. -/
theorem measurable_wignerMatrixOfCoordinates {n : ℕ} :
    Measurable (wignerMatrixOfCoordinates (n := n)) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  unfold wignerMatrixOfCoordinates
  fun_prop

/-- The law of a fixed-size Wigner matrix is the pushforward of the product of its coordinate
laws. The hypotheses allow a separate law on the real diagonal; independence is required across
both the upper-triangular and diagonal coordinates. -/
theorem hasLaw_wignerMatrix_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ)
    (μ : StrictUpperFin n → Measure ℂ) (ν : Fin n → Measure ℝ)
    (hξ : ∀ u, HasLaw (fun ω => ξ (wignerUpperIndex u) ω) (μ u) P)
    (hη : ∀ i, HasLaw (fun ω => η i.val ω) (ν i) P)
    (hind : iIndepFun (fun k ω => wignerCoordinates ξ η n ω k) P) :
    HasLaw (fun ω => wignerMatrix ξ η n ω)
      (Measure.map wignerMatrixOfCoordinates (Measure.pi (wignerCoordinateMeasures μ ν))) P := by
  have hcoordinates :
      HasLaw (fun ω k => wignerCoordinates ξ η n ω k)
        (Measure.pi (wignerCoordinateMeasures μ ν)) P := by
    apply hind.hasLaw_pi
    intro k
    cases k with
    | inl u => exact hξ u
    | inr i => exact hη i
  have hmatrix :
      HasLaw (wignerMatrixOfCoordinates (n := n))
        (Measure.map (wignerMatrixOfCoordinates (n := n))
          (Measure.pi (wignerCoordinateMeasures μ ν)))
        (Measure.pi (wignerCoordinateMeasures μ ν)) :=
    hasLaw_map (P := Measure.pi (wignerCoordinateMeasures μ ν))
      (measurable_wignerMatrixOfCoordinates (n := n)).aemeasurable
  have h := hmatrix.fun_comp hcoordinates
  exact h.congr (by
    filter_upwards with ω
    exact wignerMatrix_eq_wignerMatrixOfCoordinates ξ η n ω)

end

section Deterministic

variable (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) {n : ℕ} (ω : Ω)

/-- Subtracting two Wigner matrices subtracts their coordinate arrays, including at size zero. -/
@[simp]
theorem wignerMatrix_sub (ξ' : StrictUpper → Ω → ℂ) (η' : ℕ → Ω → ℝ) (n : ℕ) :
    wignerMatrix ξ η n ω - wignerMatrix ξ' η' n ω =
      wignerMatrix (fun ij ω ↦ ξ ij ω - ξ' ij ω) (fun i ω ↦ η i ω - η' i ω) n ω := by
  ext i j
  simp only [wignerMatrix, of_apply, Matrix.sub_apply]
  split_ifs <;> simp_all [mul_sub, -Fin.val_fin_lt]

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

/-- A Wigner matrix is its zero-diagonal version plus the original real diagonal divided by
the square root of the dimension. -/
theorem wignerMatrix_eq_add_diagonal (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    wignerMatrix ξ η n ω = wignerMatrix ξ (fun _ _ ↦ 0) n ω +
      diagonal (fun i : Fin n ↦ ((η i ω / Real.sqrt n : ℝ) : ℂ)) := by
  ext i j
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · simp [wignerMatrix_apply_of_lt _ _ _ hij, Fin.ne_of_val_ne hij.ne]
  · obtain rfl := Fin.ext hij
    simp [div_eq_mul_inv, mul_comm]
  · simp [wignerMatrix_apply_of_gt _ _ _ hij, Fin.ne_of_val_ne hij.ne']

/-- The squared absolute value of a diagonal entry is the corresponding diagonal
coordinate's square divided by the matrix size. -/
theorem norm_wignerMatrix_apply_self_sq (i : Fin n) :
    ‖wignerMatrix ξ η n ω i i‖ ^ 2 = (n : ℝ)⁻¹ * η i.val ω ^ 2 := by
  simp only [wignerMatrix_apply_self, norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, inv_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The squared absolute value of an off-diagonal entry is the corresponding upper
coordinate's squared absolute value divided by the matrix size. -/
theorem norm_wignerMatrix_apply_sq_of_ne {i j : Fin n} (h : i ≠ j) :
    ‖wignerMatrix ξ η n ω i j‖ ^ 2 = (n : ℝ)⁻¹ *
      ‖ξ ⟨(min i.val j.val, max i.val j.val), min_lt_max.mpr (Fin.val_ne_of_ne h)⟩ ω‖ ^ 2 := by
  have hn : ‖(Real.sqrt n : ℂ)⁻¹‖ ^ 2 = (n : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hij | hij
  · simp only [wignerMatrix_apply_of_lt _ _ _ hij, norm_mul, mul_pow, hn,
      min_eq_left hij.le, max_eq_right hij.le]
  · simp only [wignerMatrix_apply_of_gt _ _ _ hij, norm_mul, mul_pow, norm_star, hn,
      min_eq_right hij.le, max_eq_left hij.le]

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
    {ω' : Ω'} (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ξ ij ω = ξ' ij ω')
    (hη : ∀ i < n, η i ω = η' i ω') :
    wignerMatrix ξ η n ω = wignerMatrix ξ' η' n ω' := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [wignerMatrix_apply_of_lt _ _ _ h, wignerMatrix_apply_of_lt _ _ _ h, hξ ⟨_, h⟩ j.isLt]
  · obtain rfl := Fin.ext h
    rw [wignerMatrix_apply_self, wignerMatrix_apply_self, hη _ i.isLt]
  · rw [wignerMatrix_apply_of_gt _ _ _ h, wignerMatrix_apply_of_gt _ _ _ h, hξ ⟨_, h⟩ i.isLt]

/-- Zeroing the array coordinates outside the top-left `n × n` corner leaves the Wigner matrix of
size `n` unchanged. -/
@[simp]
theorem wignerMatrix_ite_lt (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ) :
    wignerMatrix (fun ij ↦ if ij.val.2 < n then ξ ij else 0)
      (fun i ↦ if i < n then η i else 0) n = wignerMatrix ξ η n :=
  funext fun ω' ↦ wignerMatrix_congr ω' (fun _ hij ↦ by simp [hij]) (fun _ hi ↦ by simp [hi])

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

/-- The coordinates of the entry array `Sum.elim ξ (ofReal ∘ η)`, indexed by `StrictUpper ⊕ ℕ`,
are a.e.-measurable when the entries `ξ` and `η` are. -/
theorem aemeasurable_sumElim_ofReal {P : Measure Ω} (hξ : ∀ ij, AEMeasurable (ξ ij) P)
    (hη : ∀ i, AEMeasurable (η i) P) (k : StrictUpper ⊕ ℕ) :
    AEMeasurable (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P := by
  cases k with
  | inl ij => exact hξ ij
  | inr i => exact Complex.measurable_ofReal.comp_aemeasurable (hη i)

/-- A Wigner matrix of size `n` whose corner entries are measurable is a measurable random
matrix. -/
theorem measurable_wignerMatrix {n : ℕ} (hξ : ∀ ij : StrictUpper, ij.val.2 < n → Measurable (ξ ij))
    (hη : ∀ i < n, Measurable (η i)) : Measurable (wignerMatrix ξ η n) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h]
    exact measurable_const.mul (hξ _ j.isLt)
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self]
    exact measurable_const.mul (Complex.measurable_ofReal.comp (hη _ i.isLt))
  · simp only [wignerMatrix_apply_of_gt _ _ _ h]
    exact measurable_const.mul (continuous_star.measurable.comp (hξ _ i.isLt))

/-- A Wigner matrix of size `n` whose corner entries are almost everywhere measurable is almost
everywhere measurable. -/
theorem aemeasurable_wignerMatrix {P : Measure Ω} {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n, AEMeasurable (η i) P) : AEMeasurable (wignerMatrix ξ η n) P := by
  rw [← wignerMatrix_ite_lt ξ η n, ← wignerOfArray_comp]
  refine (measurable_wignerOfArray n).comp_aemeasurable
    (aemeasurable_pi_iff.2 (aemeasurable_sumElim_ofReal (fun ij ↦ ?_) (fun i ↦ ?_)))
  · by_cases h : ij.val.2 < n
    · simpa [h] using hξ ij h
    · rw [ite_eq_right h]
      exact aemeasurable_const
  · by_cases h : i < n
    · simpa [h] using hη i h
    · rw [ite_eq_right h]
      exact aemeasurable_const

end Measurability

section Independence

variable [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The indices of the entries of the top-left `n × n` corner. -/
private noncomputable def cornerIndices (n : ℕ) : Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ Finset.range n).subtype fun ij ↦ ij.1 < ij.2).disjSum (Finset.range n)

/-- The indices of the strictly upper entries of column `n`. -/
private noncomputable def columnIndices (n : ℕ) : Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ {n}).subtype fun ij ↦ ij.1 < ij.2).disjSum ∅

private theorem inl_mem_cornerIndices {n : ℕ} {ij : StrictUpper} (h : ij.val.2 < n) :
    Sum.inl ij ∈ cornerIndices n := by
  simp [cornerIndices, h, ij.property.trans h]

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
    IndepFun (wignerMatrix ξ η n) (fun ω (i : Fin n) ↦ ξ ⟨(i.val, n), i.isLt⟩ ω) P := by
  have hcol (i : Fin n) : (Sum.inl ⟨(i.val, n), i.isLt⟩ : StrictUpper ⊕ ℕ) ∈ columnIndices n := by
    simp only [columnIndices, Finset.inl_mem_disjSum, Finset.mem_subtype, Finset.mem_product,
      Finset.mem_range, Finset.mem_singleton]
    exact ⟨i.isLt, trivial⟩
  have hφ : Measurable (wignerOfArray n ∘
      fun g : cornerIndices n → ℂ ↦ Function.extend Subtype.val g (fun _ ↦ (0 : ℂ))) :=
    (measurable_wignerOfArray n).comp (MeasureTheory.measurable_extend _ _)
  have hψ : Measurable fun (g : columnIndices n → ℂ) (i : Fin n) ↦ g ⟨_, hcol i⟩ :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  refine ((hindep.indepFun_finset₀ _ _ (disjoint_cornerIndices_columnIndices n)
    (aemeasurable_sumElim_ofReal hξ hη)).comp hφ hψ).congr (.of_forall fun ω ↦ ?_)
      (.of_forall fun ω ↦ rfl)
  simp only [Function.comp_apply, wignerOfArray]
  refine wignerMatrix_congr _ (fun ij hij ↦ ?_) (fun i hi ↦ ?_)
  · rw [Function.extend_val_apply (inl_mem_cornerIndices hij)]
    rfl
  · rw [Function.extend_val_apply (inr_mem_cornerIndices hi)]
    simp

/-- The principal minor of a Wigner matrix obtained by deleting the last row and column is
independent of the off-diagonal entries removed from that row and column. -/
theorem indepFun_submatrix_castSucc_wignerMatrix (hξ : ∀ ij, AEMeasurable (ξ ij) P)
    (hη : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (n : ℕ) :
    IndepFun
      (fun ω ↦ (wignerMatrix ξ η (n + 1) ω).submatrix Fin.castSucc Fin.castSucc)
      (fun ω (i : Fin n) ↦ ξ ⟨(i.val, n), i.isLt⟩ ω) P := by
  have h := (indepFun_wignerMatrix_column hξ hη hindep n).comp
    (measurable_const_smul (((Real.sqrt n / Real.sqrt (n + 1) : ℝ) : ℂ))) measurable_id
  convert h using 1
  · funext ω
    have hcast : Fin.castLE (Nat.le_succ n) = Fin.castSucc := by
      funext i
      exact Fin.ext rfl
    simpa only [hcast, Function.comp_apply, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      (submatrix_castLE_wignerMatrix (ξ := ξ) (η := η) ω (Nat.le_succ n))
  · rfl

/-- For a zero-diagonal Wigner matrix with independent upper entries, every principal
minor obtained by deleting an index is independent of the removed off-diagonal column. -/
theorem indepFun_submatrix_wignerMatrix_zero_column (hind : iIndepFun ξ P)
    (hm : ∀ ij, AEMeasurable (ξ ij) P) {n : ℕ} (i : Fin n) :
    IndepFun (fun ω ↦ ((wignerMatrix ξ (fun _ _ ↦ 0) n ω).submatrix (↑) (↑) :
      Matrix {j // j ≠ i} {j // j ≠ i} ℂ))
      (fun ω (j : {j // j ≠ i}) ↦ wignerMatrix ξ (fun _ _ ↦ 0) n ω j i) P := by
  classical
  let S := (Finset.univ : Finset (StrictUpperFin n)).image wignerUpperIndex
  let T := S.filter (fun ij ↦ ij.val.1 = i.val ∨ ij.val.2 = i.val)
  let U := S \ T
  let extend (V : Finset StrictUpper) (x : V → ℂ) :=
    Function.extend (Subtype.val : V → StrictUpper) x (fun _ ↦ (0 : ℂ))
  let W (V : Finset StrictUpper) :=
    wignerMatrix (fun ij x ↦ extend V x ij) (fun _ _ ↦ 0) n
  have hW (V : Finset StrictUpper) : Measurable (W V) :=
    measurable_wignerMatrix (ξ := fun ij x ↦ extend V x ij) (η := fun _ _ ↦ 0)
      (fun ij _ ↦ (measurable_pi_apply ij).comp (MeasureTheory.measurable_extend
        (Subtype.val : V → StrictUpper) (fun _ ↦ (0 : ℂ))))
      (fun _ _ ↦ measurable_const)
  have hu : Disjoint U T := Finset.sdiff_disjoint
  have h := (hind.indepFun_finset₀ U T hu hm).comp
    (φ := fun x ↦ ((W U x).submatrix (↑) (↑) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ))
    (ψ := fun x (j : {j // j ≠ i}) ↦ W T x j i)
    (.of_eval_matrix _ fun _ _ ↦ (hW U).eval_matrix)
    (measurable_pi_iff.mpr fun _ ↦ (hW T).eval_matrix)
  have hs {j k : Fin n} (hjk : j.val < k.val) :
      (⟨(j.val, k.val), hjk⟩ : StrictUpper) ∈ S :=
    Finset.mem_image.mpr ⟨⟨(j, k), hjk⟩, Finset.mem_univ _, Subtype.ext (wignerUpperIndex_val _)⟩
  refine h.congr (.of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ ?_)
  · apply Matrix.ext
    intro j k
    simp only [Function.comp_apply, Matrix.submatrix_apply, W, extend]
    have hj := Fin.val_ne_of_ne j.property
    have hk := Fin.val_ne_of_ne k.property
    rcases lt_trichotomy j.val.val k.val.val with hlt | heq | hgt
    · have hmem : (⟨(j.val.val, k.val.val), hlt⟩ : StrictUpper) ∈ U :=
        Finset.mem_sdiff.mpr ⟨hs hlt, by simp [T, hj, hk]⟩
      simp only [wignerMatrix_apply_of_lt _ _ _ hlt, Function.extend_val_apply hmem]
    · obtain rfl : j = k := Subtype.ext (Fin.ext heq)
      simp
    · have hmem : (⟨(k.val.val, j.val.val), hgt⟩ : StrictUpper) ∈ U :=
        Finset.mem_sdiff.mpr ⟨hs hgt, by simp [T, hj, hk]⟩
      simp only [wignerMatrix_apply_of_gt _ _ _ hgt, Function.extend_val_apply hmem]
  · funext j
    simp only [Function.comp_apply, W, extend]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne j.property) with hlt | hgt
    · have hmem : (⟨(j.val.val, i.val), hlt⟩ : StrictUpper) ∈ T :=
        Finset.mem_filter.mpr ⟨hs hlt, Or.inr rfl⟩
      simp only [wignerMatrix_apply_of_lt _ _ _ hlt, Function.extend_val_apply hmem]
    · have hmem : (⟨(i.val, j.val.val), hgt⟩ : StrictUpper) ∈ T :=
        Finset.mem_filter.mpr ⟨hs hgt, Or.inl rfl⟩
      simp only [wignerMatrix_apply_of_gt _ _ _ hgt, Function.extend_val_apply hmem]

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

/-- Restricting an independent `StrictUpper ⊕ ℕ`-indexed entry array to the `n × n` corner
preserves independence. -/
theorem iIndepFun_sumElim_ofReal_subtype_lt {n : ℕ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P) :
    iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P := by
  simpa only [Function.comp_def, Sum.elim_map] using
    hindep.precomp (Subtype.val_injective.sumMap Subtype.val_injective)

end Independence

section IndependentEdges

variable [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Entries at distinct unordered off-diagonal positions are independent whenever the corner
upper-triangular coordinates are independent. No condition is needed on the diagonal entries. -/
theorem iIndepFun_wignerMatrix_apply_of_ne {ι : Type*} {n : ℕ} (u v : ι → Fin n)
    (hne : ∀ i, u i ≠ v i) (hinj : Function.Injective fun i ↦ s(u i, v i))
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P) :
    iIndepFun (fun i ω ↦ wignerMatrix ξ η n ω (u i) (v i)) P := by
  let e : ι → {ij : StrictUpper // ij.val.2 < n} := fun i ↦
    ⟨⟨(min (u i).val (v i).val, max (u i).val (v i).val),
      min_lt_max.mpr (Fin.val_ne_of_ne (hne i))⟩, max_lt (u i).isLt (v i).isLt⟩
  have he : Function.Injective e := by
    intro i j hij
    apply hinj
    have hmin := congrArg (fun x : {ij : StrictUpper // ij.val.2 < n} ↦ x.val.val.1) hij
    have hmax := congrArg (fun x : {ij : StrictUpper // ij.val.2 < n} ↦ x.val.val.2) hij
    simp only [e] at hmin hmax
    rw [Sym2.eq_iff]
    simp only [Fin.ext_iff]
    omega
  let f (i : ι) (z : ℂ) :=
    (Real.sqrt n : ℂ)⁻¹ * if (u i).val < (v i).val then z else star z
  have hf (i : ι) : Measurable (f i) := by
    dsimp only [f]
    split_ifs <;> fun_prop
  refine ((iIndepFun.precomp he hindep).comp f hf).congr (fun i ↦ .of_forall fun ω ↦ ?_)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne (hne i)) with hij | hij
  · simp only [Function.comp_apply, f, ite_eq_left hij, e, min_eq_left hij.le,
      max_eq_right hij.le, wignerMatrix_apply_of_lt _ _ _ hij]
  · simp only [Function.comp_apply, f, ite_eq_right hij.not_gt, e, min_eq_right hij.le,
      max_eq_left hij.le, wignerMatrix_apply_of_gt _ _ _ hij]

/-- Squared absolute values of entries at distinct unordered off-diagonal positions are
independent whenever the corner upper-triangular coordinates are independent. No condition is
needed on the diagonal entries. -/
theorem iIndepFun_norm_wignerMatrix_apply_sq_of_ne {ι : Type*} {n : ℕ} (u v : ι → Fin n)
    (hne : ∀ i, u i ≠ v i) (hinj : Function.Injective fun i ↦ s(u i, v i))
    (hindep : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P) :
    iIndepFun (fun i ω ↦ ‖wignerMatrix ξ η n ω (u i) (v i)‖ ^ 2) P :=
  (iIndepFun_wignerMatrix_apply_of_ne u v hne hinj hindep).comp
    (fun _ z ↦ ‖z‖ ^ 2) (fun _ ↦ by fun_prop)

end IndependentEdges

section Entries

variable [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- If the corner entries of size `n` are centred, every entry of the `n × n` Wigner matrix has
expectation zero. -/
theorem integral_wignerMatrix_apply_eq_zero {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hη : ∀ i < n, ∫ ω, η i ω ∂P = 0) (i j : Fin n) :
    ∫ ω, wignerMatrix ξ η n ω i j ∂P = 0 := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [wignerMatrix_apply_of_lt _ _ _ h, integral_const_mul, hξ ⟨(i.val, j.val), h⟩ j.isLt]
  · obtain rfl := Fin.ext h
    simp [integral_const_mul, integral_complex_ofReal, hη _ i.isLt]
  · simp [wignerMatrix_apply_of_gt _ _ _ h, integral_const_mul, integral_conj,
      hξ ⟨(j.val, i.val), h⟩ i.isLt]

/-- If the corner entries of size `n` lie in `Lᵖ`, so does every entry of the `n × n` Wigner
matrix. -/
theorem memLp_wignerMatrix_apply {p : ℝ≥0∞} {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) p P)
    (hη : ∀ i < n, MemLp (η i) p P) (i j : Fin n) :
    MemLp (fun ω ↦ wignerMatrix ξ η n ω i j) p P := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h]
    exact (hξ _ j.isLt).const_mul _
  · obtain rfl := Fin.ext h
    simp only [wignerMatrix_apply_self]
    exact (hη _ i.isLt).ofReal.const_mul _
  · simp only [wignerMatrix_apply_of_gt _ _ _ h]
    exact (hξ _ i.isLt).star.const_mul _

open scoped Matrix.Norms.Frobenius in
/-- If the corner entries of size `n` are square-integrable, the squared Frobenius norm of the
`n × n` Wigner matrix is integrable. -/
theorem integrable_norm_wignerMatrix_sq {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) 2 P)
    (hη : ∀ i < n, MemLp (η i) 2 P) :
    Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω‖ ^ 2) P := by
  simp_rw [Matrix.frobenius_norm_sq_eq_sum_normSq, Complex.normSq_eq_norm_sq]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (memLp_two_iff_integrable_sq_norm
      (memLp_wignerMatrix_apply hξ hη i j).aestronglyMeasurable).mp
        (memLp_wignerMatrix_apply hξ hη i j)

/-- A product of `k` entries of an `n × n` Wigner matrix, indexed by a finite type `ι` of
cardinality `k`, is integrable when the corner entries of size `n` lie in `Lᵏ`. -/
theorem integrable_prod_wignerMatrix_apply [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) (Fintype.card ι) P)
    (hη : ∀ i < n, MemLp (η i) (Fintype.card ι) P) (u v : ι → Fin n) :
    Integrable (fun ω ↦ ∏ s, wignerMatrix ξ η n ω (u s) (v s)) P := by
  cases isEmpty_or_nonempty ι
  · simp
  have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have h := MemLp.fun_prod (s := Finset.univ) (p := fun _ ↦ (Fintype.card ι : ℝ≥0∞))
    fun s _ ↦ memLp_wignerMatrix_apply hξ hη (u s) (v s)
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _), inv_one, memLp_one_iff_integrable]
    at h

end Entries

section SecondMoment

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

variable [MeasurableSpace Ω] {P : Measure Ω}

private theorem integral_norm_wignerMatrix_apply_sq {σ2 s : ℝ}
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) (hη : ∀ i, ∫ ω, η i ω ^ 2 ∂P = σ2) {n : ℕ}
    (i j : Fin n) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P = (n : ℝ)⁻¹ * if i = j then σ2 else s := by
  by_cases hij : i = j
  · subst j
    simp only [norm_wignerMatrix_apply_self_sq, integral_const_mul, hη, ↓reduceIte]
  · simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hij, integral_const_mul,
      hξ, hij, ↓reduceIte]

private theorem integrable_norm_wignerMatrix_apply_sq
    (hξ : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P) (hη : ∀ i, Integrable (fun ω ↦ η i ω ^ 2) P)
    {n : ℕ} (i j : Fin n) : Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω i j‖ ^ 2) P := by
  by_cases hij : i = j
  · subst j
    simp only [norm_wignerMatrix_apply_self_sq]
    exact (hη _).const_mul _
  · simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hij]
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
  simp_rw [(wignerMatrix_isHermitian ξ η _ _).trace_mul_self_eq_sum_norm_sq,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ integrable_norm_wignerMatrix_apply_sq hξi hηi i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ integrable_norm_wignerMatrix_apply_sq hξi hηi _ j,
    integral_norm_wignerMatrix_apply_sq hξ hη, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · field_simp

open scoped Matrix.Norms.Frobenius in
/-- Keeping the same diagonal, a common second absolute moment `s` of the upper-coordinate
differences gives expected squared Frobenius error `n * s` at size `n + 1`. -/
theorem integral_norm_wignerMatrix_sub_sq {ξ' : StrictUpper → Ω → ℂ}
    (hξ : ∀ ij, MemLp (fun ω ↦ ξ ij ω - ξ' ij ω) 2 P)
    {s : ℝ} (hs : ∀ ij, ∫ ω, ‖ξ ij ω - ξ' ij ω‖ ^ 2 ∂P = s) (n : ℕ) :
    ∫ ω, ‖wignerMatrix ξ η (n + 1) ω - wignerMatrix ξ' η (n + 1) ω‖ ^ 2 ∂P = n * s := by
  let d (ij : StrictUpper) (ω : Ω) := ξ ij ω - ξ' ij ω
  have heq (ω : Ω) : wignerMatrix ξ η (n + 1) ω - wignerMatrix ξ' η (n + 1) ω =
      wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω := by
    simp only [wignerMatrix_sub, sub_self, d]
  have hn (ω : Ω) :
      (((n + 1 : ℂ)⁻¹ *
        (wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω *
          wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω).trace).re) =
        (n + 1 : ℝ)⁻¹ * ‖wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω‖ ^ 2 := by
    rw [(wignerMatrix_isHermitian d (fun _ _ ↦ 0) ω _).trace_mul_self_eq_sum_norm_sq,
      Matrix.frobenius_norm_sq_eq_sum_normSq]
    simp only [Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := integral_re_trace_wignerMatrix_mul_self (ξ := d) (η := fun _ _ ↦ 0) (σ2 := 0)
    (fun ij ↦ (memLp_two_iff_integrable_sq_norm (hξ ij).aestronglyMeasurable).mp (hξ ij))
    hs (fun _ ↦ by simp) (fun _ ↦ by simp) (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp only [hn, integral_const_mul] at h
  simp_rw [heq]
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [add_sub_cancel_right, zero_add] at h
  field_simp at h
  exact h

end SecondMoment

end TauCeti
