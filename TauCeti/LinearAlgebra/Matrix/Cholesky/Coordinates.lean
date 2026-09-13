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

/-- Reading off the on-or-below-diagonal entries is a homeomorphism from the positive-diagonal
lower-triangular matrices to their coordinate space. Its inverse fills the positions above the
diagonal with zeros. -/
def lowerTriangleCoordinatesHomeomorph :
    PosDiagLowerTriangular p ≃ₜ PosDiagLowerCoordinates p where
  toFun L := ⟨fun ij ↦ L.1 ij.1.1 ij.1.2, L.2.2⟩
  invFun x :=
    ⟨Matrix.of fun i j ↦ if h : j ≤ i then x.1 ⟨(i, j), h⟩ else 0,
      fun i j hij ↦ dite_eq_right (not_le.2 hij), fun i ↦ by simpa using x.2 i⟩
  left_inv L := by
    refine Subtype.ext (Matrix.ext fun i j ↦ ?_)
    by_cases h : j ≤ i
    · exact dite_eq_left h
    · exact (dite_eq_right h).trans (L.2.1 (not_le.1 h)).symm
  right_inv x := Subtype.ext (funext fun ij ↦ dite_eq_left ij.2)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun ij ↦ ?_) _
    exact continuous_subtype_val.matrix_elem ij.1.1 ij.1.2
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_) _
    by_cases h : j ≤ i
    · simp only [Matrix.of_apply, dite_eq_left h]
      exact (continuous_apply _).comp continuous_subtype_val
    · simpa only [Matrix.of_apply, dite_eq_right h] using continuous_const

@[simp]
theorem lowerTriangleCoordinatesHomeomorph_apply_coe (L : PosDiagLowerTriangular p)
    (ij : lowerTriangle p) :
    (lowerTriangleCoordinatesHomeomorph p L).1 ij = L.1 ij.1.1 ij.1.2 :=
  (rfl)

@[simp]
theorem lowerTriangleCoordinatesHomeomorph_symm_apply_coe_of_le (x : PosDiagLowerCoordinates p)
    {i j : Fin p} (h : j ≤ i) :
    ((lowerTriangleCoordinatesHomeomorph p).symm x).1 i j = x.1 ⟨(i, j), h⟩ :=
  dite_eq_left h

@[simp]
theorem lowerTriangleCoordinatesHomeomorph_symm_apply_coe_of_lt (x : PosDiagLowerCoordinates p)
    {i j : Fin p} (h : i < j) :
    ((lowerTriangleCoordinatesHomeomorph p).symm x).1 i j = 0 :=
  dite_eq_right (not_le.2 h)

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
