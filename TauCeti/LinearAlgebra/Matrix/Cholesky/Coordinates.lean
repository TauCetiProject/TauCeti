/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic

/-!
# Coordinates on positive-diagonal lower-triangular matrices

A lower-triangular matrix is determined by its on-or-below-diagonal entries. Reading off these
entries identifies the positive-diagonal lower-triangular matrices with the functions on the
lower-triangular positions whose diagonal values are positive. This file packages that
identification as a homeomorphism for the subtype topologies on both sides, and as a measurable
equivalence for the corresponding Borel structures. These are the product coordinates in which
the Jacobian of Cholesky reconstruction is computed.

## Main declarations

* `TauCeti.lowerTriangle` — the index type of on-or-below-diagonal positions.
* `TauCeti.lowerTriangleMatrix` — the lower-triangular matrix with prescribed entries there.
* `TauCeti.PosDiagLowerCoordinates` — the coordinate functions with positive diagonal values.
* `TauCeti.lowerTriangleCoordinatesHomeomorph` — the coordinate homeomorphism.
* `TauCeti.lowerTriangleCoordinates` — its measurable-equivalence form.
-/

public section

noncomputable section

namespace TauCeti

/-- The on-or-below-diagonal positions `(i, j)`, `j ≤ i`, of a `p × p` matrix. -/
abbrev lowerTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.2 ≤ ij.1}

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
theorem lowerTriangleMatrix_entries {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.IsLowerTriangular) :
    lowerTriangleMatrix p (fun ij ↦ A ij.1.1 ij.1.2) = A := by
  refine Matrix.ext fun i j ↦ ?_
  by_cases h : j ≤ i
  · exact lowerTriangleMatrix_apply_of_le _ h
  · rw [lowerTriangleMatrix_apply_of_lt _ (not_le.1 h)]
    exact (hA (by simpa using not_le.1 h)).symm

theorem continuous_lowerTriangleMatrix :
    Continuous fun x : lowerTriangle p → ℝ ↦ lowerTriangleMatrix p x := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  by_cases h : j ≤ i
  · simpa only [lowerTriangleMatrix_apply_of_le _ h] using
      continuous_apply (⟨(i, j), h⟩ : lowerTriangle p)
  · simpa only [lowerTriangleMatrix_apply_of_lt _ (not_le.1 h)] using continuous_const

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
