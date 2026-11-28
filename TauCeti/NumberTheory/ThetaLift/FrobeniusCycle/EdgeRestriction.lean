/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Saturation

/-!
# Edge restrictions and their saturated images

An edge sees the vector at its source after a change of basis and a diagonal depth scaling.
If each source occurs, select one of its edges to obtain a square minor that is block diagonal.
Over a valuation domain this splits off the origin functions, namely the vectors on edges that
become restrictions after multiplication by a power of the depth parameter.

The restriction and splitting follow the statements of `New.FrobeniusCycle.edgeRestriction` and
`New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd` in
[grh-lean](https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/UpperBound/ElementaryDivisors/Edges.lean).
Here the changes of basis can be any invertible matrices, including the twisted actions of the
letters of a Frobenius cycle. The determinant budget counts all coordinate depths before any
refinement using the dimensions of the deep forms.
-/

public section

open Matrix
open scoped BigOperators

namespace TauCeti.FrobeniusCycle

variable {O I X E : Type*} [Semiring O] [Fintype I] [DecidableEq I] [DecidableEq X]

/-- The matrix restricting a family on sources to edges. At edge `e`, apply the change of
basis `g e` to the vector at `src e`, then multiply its `i`-th coordinate by `w ^ depth i`. -/
def edgeRestriction (src : E → X) (g : E → GL I O) (w : O) (depth : I → ℕ) :
    Matrix (I × E) (I × X) O :=
  Matrix.of fun (i, e) (j, x) ↦ if src e = x then w ^ depth i * (g e).val i j else 0

/-- The block from source `x` to edge `e` is zero unless `src e = x`. -/
@[simp] theorem edgeRestriction_apply (src : E → X) (g : E → GL I O) (w : O) (depth : I → ℕ)
    (i j : I) (e : E) (x : X) :
    edgeRestriction src g w depth (i, e) (j, x) =
      if src e = x then w ^ depth i * (g e).val i j else 0 := (rfl)

/-- Evaluate an edge restriction using only the vector at the source of the edge. -/
@[simp] theorem edgeRestriction_mulVec [Fintype X] (src : E → X) (g : E → GL I O)
    (w : O) (depth : I → ℕ) (v : I × X → O) (i : I) (e : E) :
    (edgeRestriction src g w depth *ᵥ v) (i, e) =
      w ^ depth i * ((g e).val *ᵥ fun j ↦ v (j, src e)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc]

/-- If every source has an edge, the origin functions form the image of a split inclusion `Q`.
The edge restriction factors as `Q * D`, and the determinant of the square factor `D` divides
`w` to the sum of all coordinate depths over the sources. -/
theorem exists_originFunctions_factorization {O I X E : Type*} [CommRing O] [IsDomain O]
    [PreValuationRing O] [Fintype I] [Fintype X] [Fintype E] [DecidableEq I] [DecidableEq X]
    (src : E → X) (hs : Function.Surjective src) (g : E → GL I O)
    {w : O} (hw : w ≠ 0) (depth : I → ℕ) :
    ∃ (Q : Matrix (I × E) (I × X) O) (R : Matrix (I × X) (I × E) O)
      (D : Matrix (I × X) (I × X) O),
      R * Q = 1 ∧ edgeRestriction src g w depth = Q * D ∧
      D.det ∣ w ^ (Fintype.card X * ∑ i, depth i) ∧
      ∀ y : I × E → O, (∃ z, Q *ᵥ z = y) ↔
        ∃ j : ℕ, ∃ x, edgeRestriction src g w depth *ᵥ x = w ^ j • y := by
  choose t ht using hs
  let e : I × X ↪ I × E := (Function.Embedding.refl I).prodMap
    ⟨t, Function.LeftInverse.injective ht⟩
  apply Matrix.exists_split_factorization_of_det_submatrix_dvd_pow _ e hw
  have hblock : (edgeRestriction src g w depth).submatrix e id =
      blockDiagonal (fun x ↦ diagonal (fun i ↦ w ^ depth i) * (g (t x)).val) := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [e, ht, blockDiagonal_apply]
  rw [hblock, det_blockDiagonal]
  simp_rw [det_mul, det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]
  have hu : IsUnit (∏ x, ((g (t x)).val).det) :=
    IsUnit.prod_univ_iff.mpr fun x ↦ isUnits_det_units (g (t x))
  rw [mul_comm]
  exact hu.mul_left_dvd.mpr dvd_rfl

end TauCeti.FrobeniusCycle
