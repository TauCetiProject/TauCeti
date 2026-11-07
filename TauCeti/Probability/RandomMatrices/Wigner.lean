/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Wigner matrices

The normalized Wigner matrix built from the upper-triangular entries of an infinite array. Its
entrywise definition makes each matrix Hermitian: the diagonal is real, and the two off-diagonal
entries are complex conjugates.

## Main declarations

* `TauCeti.Probability.wignerMatrix`: the normalized Wigner matrix from an infinite array.
* `TauCeti.Probability.wignerMatrix_apply`: the entrywise characterization of the constructor.
* `TauCeti.Probability.isHermitian_wignerMatrix`: every realization is Hermitian.
* `TauCeti.Probability.hasLaw_wignerMatrix_of_iIndepFun`: the law of a fixed-size Wigner matrix
  from independent upper-triangular entries and diagonal entries with separate laws.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

/-- Index set of the strictly upper-triangular positions of an infinite matrix. -/
abbrev StrictUpper := {ij : ℕ × ℕ // ij.1 < ij.2}

/-- The normalized Wigner matrix `Wₙ / √n` built from the top-left `n × n` corner of an infinite
array: complex entries above the diagonal, their conjugates below it, and real entries on it. -/
def wignerMatrix {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ ((Real.sqrt n)⁻¹ : ℂ) *
    if h : i.val < j.val then ξ ⟨(i.val, j.val), h⟩ ω
    else if h' : j.val < i.val then star (ξ ⟨(j.val, i.val), h'⟩ ω)
    else (η i.val ω : ℂ)

/-- The entries of the normalized Wigner matrix are given by its upper-triangular data. -/
@[simp]
theorem wignerMatrix_apply {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) (i j : Fin n) :
    wignerMatrix ξ η n ω i j = ((Real.sqrt n)⁻¹ : ℂ) *
      if h : i.val < j.val then ξ ⟨(i.val, j.val), h⟩ ω
      else if h' : j.val < i.val then star (ξ ⟨(j.val, i.val), h'⟩ ω)
      else (η i.val ω : ℂ) :=
  by simp [wignerMatrix]

/-- The normalized Wigner matrix is Hermitian for every sample point. -/
theorem isHermitian_wignerMatrix {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : (wignerMatrix ξ η n ω).IsHermitian := by
  ext i j
  simp only [wignerMatrix, conjTranspose_apply, of_apply, star_mul', star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [h, h.not_gt]
  · simp [Fin.ext h]
  · simp [h, h.not_gt]

/-- Strictly upper-triangular positions in a fixed finite matrix. -/
abbrev StrictUpperFin (n : ℕ) := {ij : Fin n × Fin n // ij.1.val < ij.2.val}

/-- Convert a finite upper-triangular position to the index type used by `wignerMatrix`. -/
def wignerUpperIndex {n : ℕ} (u : StrictUpperFin n) : StrictUpper :=
  ⟨(u.1.1.val, u.1.2.val), by exact_mod_cast u.2⟩

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

end Probability

end TauCeti
