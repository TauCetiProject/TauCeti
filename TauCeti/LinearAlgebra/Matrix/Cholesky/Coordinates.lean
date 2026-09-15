/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinates on positive-diagonal lower-triangular matrices

A lower-triangular matrix is determined by its on-or-below-diagonal entries. Reading off these
entries identifies the positive-diagonal lower-triangular matrices with the functions on the
lower-triangular positions whose diagonal values are positive. This file packages that
identification as a homeomorphism for the subtype topologies on both sides, and as a measurable
equivalence for the corresponding Borel structures. These are the product coordinates in which
the Jacobian of Cholesky reconstruction is computed. The file also reads the determinant of a
lower-triangular matrix and the trace of its Gram matrix `L * Lᵀ` off these coordinates, and
records how a product over the lower-triangular positions splits into a product over the rows.

## Main declarations

* `TauCeti.lowerTriangle` — the index type of on-or-below-diagonal positions.
* `TauCeti.lowerTriangleMatrix` — the lower-triangular matrix with prescribed entries there.
* `TauCeti.PosDiagLowerCoordinates` — the coordinate functions with positive diagonal values.
* `TauCeti.lowerTriangleCoordinatesHomeomorph` — the coordinate homeomorphism.
* `TauCeti.lowerTriangleCoordinates` — its measurable-equivalence form.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- The on-or-below-diagonal positions `(i, j)`, `j ≤ i`, of a `p × p` matrix. -/
abbrev lowerTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.2 ≤ ij.1}

/-- A product over the lower-triangular positions of a quantity that depends only on the row
index, and only through whether the position is diagonal, collapses to a product over the rows:
row `i` has one diagonal position and `i` strictly lower ones. -/
theorem prod_lowerTriangle_ite {M : Type*} [CommMonoid M] {p : ℕ} (F G : Fin p → M) :
    ∏ ij : lowerTriangle p, (if ij.1.1 = ij.1.2 then F ij.1.1 else G ij.1.1) =
      ∏ i : Fin p, F i * G i ^ (i : ℕ) := by
  classical
  rw [← Finset.prod_subtype (p := fun q : Fin p × Fin p ↦ q.2 ≤ q.1)
      {q : Fin p × Fin p | q.2 ≤ q.1} (fun q ↦ by simp)
      fun q ↦ if q.1 = q.2 then F q.1 else G q.1, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hsplit : ∀ j : Fin p, (if j ≤ i then (if i = j then F i else G i) else 1) =
      (if j = i then F i else 1) * (if j < i then G i else 1) := by
    intro j
    rcases lt_trichotomy j i with h | h | h
    · simp [h.le, h.ne, h.ne', h]
    · simp [h]
    · simp [not_le.2 h, h.ne', asymm h]
  rw [Finset.prod_congr rfl fun j _ ↦ hsplit j, Finset.prod_mul_distrib, ← Finset.prod_filter,
    ← Finset.prod_filter, Finset.filter_gt_eq_Iio]
  simp [Finset.filter_eq']

/-- Real functions on the lower-triangular positions whose diagonal values are positive: the
coordinate space of `TauCeti.PosDiagLowerTriangular p`. -/
abbrev PosDiagLowerCoordinates (p : ℕ) :=
  {x : lowerTriangle p → ℝ // ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩}

variable (p : ℕ)

/-- The lower-triangular matrix whose on-or-below-diagonal entries are prescribed by `x` and whose
entries above the diagonal vanish. -/
def lowerTriangleMatrix : (lowerTriangle p → ℝ) →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ where
  toFun x := Matrix.of fun i j ↦ if h : j ≤ i then x ⟨(i, j), h⟩ else 0
  map_add' x y := by ext i j; by_cases h : j ≤ i <;> simp [h]
  map_smul' c x := by ext i j; by_cases h : j ≤ i <;> simp [h]

variable {p}

@[simp]
theorem lowerTriangleMatrix_apply_of_le (x : lowerTriangle p → ℝ) {i j : Fin p} (h : j ≤ i) :
    lowerTriangleMatrix p x i j = x ⟨(i, j), h⟩ :=
  dite_eq_left h

@[simp]
theorem lowerTriangleMatrix_apply_of_lt (x : lowerTriangle p → ℝ) {i j : Fin p} (h : i < j) :
    lowerTriangleMatrix p x i j = 0 :=
  dite_eq_right (not_le.2 h)

theorem isLowerTriangular_lowerTriangleMatrix (x : lowerTriangle p → ℝ) :
    (lowerTriangleMatrix p x).IsLowerTriangular :=
  fun _ _ h ↦ lowerTriangleMatrix_apply_of_lt x (by simpa using h)

/-- A lower-triangular matrix is rebuilt from its on-or-below-diagonal entries. -/
@[simp]
theorem lowerTriangleMatrix_entries {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.IsLowerTriangular) :
    lowerTriangleMatrix p (fun ij ↦ A ij.1.1 ij.1.2) = A := by
  refine Matrix.ext fun i j ↦ ?_
  by_cases h : j ≤ i
  · exact lowerTriangleMatrix_apply_of_le _ h
  · rw [lowerTriangleMatrix_apply_of_lt _ (not_le.1 h)]
    exact (hA (by simpa using not_le.1 h)).symm

/-- A lower-triangular matrix has determinant the product of its diagonal entries, which in
coordinates are the values at the diagonal positions. -/
@[simp]
theorem det_lowerTriangleMatrix (x : lowerTriangle p → ℝ) :
    (lowerTriangleMatrix p x).det = ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ := by
  rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_lowerTriangleMatrix x)]
  exact Finset.prod_congr rfl fun i _ ↦ lowerTriangleMatrix_apply_of_le x le_rfl

/-- The trace of the Gram matrix `L * Lᵀ` of a lower-triangular `L` is the sum of the squares of
the on-or-below-diagonal coordinates of `L`: the entries above the diagonal contribute nothing. -/
theorem trace_lowerTriangleMatrix_mul_transpose (x : lowerTriangle p → ℝ) :
    (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace =
      ∑ ij : lowerTriangle p, x ij ^ 2 := by
  classical
  have hzero : ∀ q : Fin p × Fin p, lowerTriangleMatrix p x q.1 q.2 ^ 2 =
      if h : q.2 ≤ q.1 then x ⟨q, h⟩ ^ 2 else 0 := by
    rintro ⟨i, j⟩
    by_cases h : j ≤ i
    · simp [h]
    · simp [lowerTriangleMatrix_apply_of_lt x (not_le.1 h), h]
  calc (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace
      = ∑ q : Fin p × Fin p, lowerTriangleMatrix p x q.1 q.2 ^ 2 := by
        simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, sq]
    _ = ∑ q : Fin p × Fin p, if h : q.2 ≤ q.1 then x ⟨q, h⟩ ^ 2 else 0 :=
        Finset.sum_congr rfl fun q _ ↦ hzero q
    _ = ∑ q ∈ {q : Fin p × Fin p | q.2 ≤ q.1}, if h : q.2 ≤ q.1 then x ⟨q, h⟩ ^ 2 else 0 :=
        (Finset.sum_subset (Finset.filter_subset _ _) fun q _ hq ↦ by simp_all).symm
    _ = ∑ ij : lowerTriangle p, x ij ^ 2 := by
        rw [Finset.sum_subtype (p := fun q : Fin p × Fin p ↦ q.2 ≤ q.1) _ (fun q ↦ by simp)
          fun q ↦ if h : q.2 ≤ q.1 then x ⟨q, h⟩ ^ 2 else 0]
        exact Finset.sum_congr rfl fun ij _ ↦ dite_eq_left ij.2

theorem continuous_lowerTriangleMatrix :
    Continuous fun x : lowerTriangle p → ℝ ↦ lowerTriangleMatrix p x :=
  (lowerTriangleMatrix p).continuous_of_finiteDimensional

variable (p)

/-- Reading off the on-or-below-diagonal entries is a homeomorphism from the positive-diagonal
lower-triangular matrices to their coordinate space. Its inverse fills the positions above the
diagonal with zeros. -/
def lowerTriangleCoordinatesHomeomorph :
    PosDiagLowerTriangular p ≃ₜ PosDiagLowerCoordinates p where
  toFun L := ⟨fun ij ↦ L.1 ij.1.1 ij.1.2, L.2.2⟩
  invFun x :=
    ⟨lowerTriangleMatrix p x.1, isLowerTriangular_lowerTriangleMatrix x.1,
      fun i ↦ by simpa using x.2 i⟩
  left_inv L := Subtype.ext (lowerTriangleMatrix_entries L.2.1)
  right_inv x := Subtype.ext (funext fun ij ↦ lowerTriangleMatrix_apply_of_le x.1 ij.2)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun ij ↦ ?_) _
    exact continuous_subtype_val.matrix_elem ij.1.1 ij.1.2
  continuous_invFun :=
    Continuous.subtype_mk (continuous_lowerTriangleMatrix.comp continuous_subtype_val) _

@[simp]
theorem lowerTriangleCoordinatesHomeomorph_apply_coe (L : PosDiagLowerTriangular p)
    (ij : lowerTriangle p) :
    (lowerTriangleCoordinatesHomeomorph p L).1 ij = L.1 ij.1.1 ij.1.2 :=
  (rfl)

@[simp]
theorem lowerTriangleCoordinatesHomeomorph_symm_apply_coe (x : PosDiagLowerCoordinates p) :
    ((lowerTriangleCoordinatesHomeomorph p).symm x).1 = lowerTriangleMatrix p x.1 :=
  (rfl)

@[simp]
theorem lowerTriangleMatrix_lowerTriangleCoordinatesHomeomorph (L : PosDiagLowerTriangular p) :
    lowerTriangleMatrix p (lowerTriangleCoordinatesHomeomorph p L).1 = L.1 :=
  lowerTriangleMatrix_entries L.2.1

/-- The measurable equivalence induced by `TauCeti.lowerTriangleCoordinatesHomeomorph`. -/
def lowerTriangleCoordinates : PosDiagLowerTriangular p ≃ᵐ PosDiagLowerCoordinates p :=
  (lowerTriangleCoordinatesHomeomorph p).toMeasurableEquiv

@[simp]
theorem lowerTriangleCoordinates_coe :
    (lowerTriangleCoordinates p : PosDiagLowerTriangular p → PosDiagLowerCoordinates p) =
      lowerTriangleCoordinatesHomeomorph p :=
  (rfl)

@[simp]
theorem lowerTriangleCoordinates_symm_coe :
    ((lowerTriangleCoordinates p).symm : PosDiagLowerCoordinates p → PosDiagLowerTriangular p) =
      (lowerTriangleCoordinatesHomeomorph p).symm :=
  (rfl)

end TauCeti
