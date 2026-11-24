/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.CrossProduct

/-!
# Rotations of `R³` as oriented orthonormal frames

Over a commutative ring `R`, call `u, v ∈ R³` orthonormal when `u ⬝ᵥ u = v ⬝ᵥ v = 1` and
`u ⬝ᵥ v = 0`. A rotation `A ∈ SO(3, R)`, that is, a matrix with `Aᵀ * A = 1` and `det A = 1`, is
determined by its first two columns `u = A e₀` and `v = A e₁`, which are orthonormal, and its third
column is their cross product `u ⨯₃ v`. Conversely, for any orthonormal pair the matrix
`TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame u v` with columns `u`, `v` and `u ⨯₃ v` lies in
`SO(3, R)`. So `SO(3, R)` is the set of orthonormal pairs of `R³`. Multiplying a frame matrix on
the left by `g ∈ SO(3, R)` multiplies both vectors of the pair by `g`, since such matrices preserve
the cross product (`Matrix.mulVec_cross_mulVec_of_mem_specialOrthogonalGroup`).

For `R = ℝ` the dot product is the Euclidean inner product: `(u, v, u ⨯₃ v)` is then the unique
positively oriented orthonormal basis starting with `u` and `v`, and an orthonormal pair is a unit
tangent vector `v` at the point `u` of the unit sphere. The topological form of this identification
is `TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup`.

## Main declarations

* `TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame`: the matrix with columns `u`, `v`, `u ⨯₃ v`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame_mem_iff`: it lies in `SO(3, R)` exactly when
  `u` and `v` are orthonormal.
* `TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame_col_zero_col_one`: every rotation is the matrix
  of the frame of its first two columns.
* `TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame_mulVec_mulVec`: rotating the frame by `g`
  multiplies its matrix by `g`.
-/

public section

open Matrix

namespace TauCeti.Matrix.SpecialOrthogonalGroup

variable {R : Type*} [CommRing R]

attribute [local instance] starRingOfComm

/-- The `3 × 3` matrix whose columns are `u`, `v` and `u ⨯₃ v`. When `u` and `v` are orthonormal
for the dot product it lies in `SO(3, R)` and carries the standard basis to `(u, v, u ⨯₃ v)`
(`TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame_mem_iff`). -/
def ofFrame (u v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  (of ![u, v, u ⨯₃ v])ᵀ

/-- The entries of `ofFrame u v`: its `j`th column is the `j`th vector of `(u, v, u ⨯₃ v)`. -/
theorem ofFrame_apply (u v : Fin 3 → R) (i j : Fin 3) :
    ofFrame u v i j = ![u, v, u ⨯₃ v] j i :=
  (rfl)

/-- The first column of `ofFrame u v` is `u`. -/
@[simp]
theorem ofFrame_col_zero (u v : Fin 3 → R) : (ofFrame u v).col 0 = u :=
  (rfl)

/-- The second column of `ofFrame u v` is `v`. -/
@[simp]
theorem ofFrame_col_one (u v : Fin 3 → R) : (ofFrame u v).col 1 = v :=
  (rfl)

/-- The third column of `ofFrame u v` is `u ⨯₃ v`. -/
@[simp]
theorem ofFrame_col_two (u v : Fin 3 → R) : (ofFrame u v).col 2 = u ⨯₃ v :=
  (rfl)

/-- The transpose of `ofFrame u v` times `ofFrame u v` is the Gram matrix of `(u, v, u ⨯₃ v)`. -/
theorem transpose_ofFrame_mul_ofFrame (u v : Fin 3 → R) :
    (ofFrame u v)ᵀ * ofFrame u v = of fun i j ↦ ![u, v, u ⨯₃ v] i ⬝ᵥ ![u, v, u ⨯₃ v] j := by
  ext i j
  rw [mul_apply', ofFrame, transpose_transpose]
  rfl

/-- The determinant of `ofFrame u v` is the dot product of `u ⨯₃ v` with itself (over `ℝ`, the
squared norm of `u ⨯₃ v`). -/
theorem det_ofFrame (u v : Fin 3 → R) : (ofFrame u v).det = (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
  have h := triple_product_eq_det u v (u ⨯₃ v)
  rw [triple_product_permutation, triple_product_permutation] at h
  rw [ofFrame, det_transpose]
  exact h.symm

/-- **A frame matrix lies in `SO(3, R)` exactly when the frame starts with two orthonormal
vectors**, that is, `u ⬝ᵥ u = v ⬝ᵥ v = 1` and `u ⬝ᵥ v = 0`. The third vector `w = u ⨯₃ v` then
automatically satisfies `w ⬝ᵥ w = 1` and `u ⬝ᵥ w = v ⬝ᵥ w = 0`, and the matrix has determinant
one; over `ℝ` this says the frame is orthonormal and positively oriented. -/
theorem ofFrame_mem_iff {u v : Fin 3 → R} :
    ofFrame u v ∈ specialOrthogonalGroup (Fin 3) R ↔
      u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff', transpose_ofFrame_mul_ofFrame,
    det_ofFrame]
  refine ⟨fun ⟨h, _⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨hu, hv, huv⟩ ↦ ?_⟩
  · simpa using congrFun₂ h 0 0
  · simpa using congrFun₂ h 1 1
  · simpa using congrFun₂ h 0 1
  have hcross : (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = 1 := by
    rw [cross_dot_cross, hu, hv, dotProduct_comm v u, huv]
    ring
  refine ⟨?_, hcross⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hu, hv, huv, dotProduct_comm v u, hcross, dot_self_cross, dot_cross_self,
      dotProduct_comm (u ⨯₃ v)]

/-- **A rotation is the frame matrix of its first two columns**: its third column is the cross
product of the first two. -/
theorem ofFrame_col_zero_col_one {A : Matrix (Fin 3) (Fin 3) R}
    (hA : A ∈ specialOrthogonalGroup (Fin 3) R) : ofFrame (A.col 0) (A.col 1) = A := by
  have h2 : A.col 0 ⨯₃ A.col 1 = A.col 2 := by
    rw [← mulVec_single_one, ← mulVec_single_one, ← mulVec_single_one,
      mulVec_cross_mulVec_of_mem_specialOrthogonalGroup hA]
    congr 1
    ext i
    fin_cases i <;> simp [cross_apply]
  refine ext_col fun j ↦ ?_
  fin_cases j <;> simp [h2]

/-- **Rotating a frame rotates its matrix**: `ofFrame (g u) (g v) = g * ofFrame u v` for a
rotation `g`. -/
theorem ofFrame_mulVec_mulVec {g : Matrix (Fin 3) (Fin 3) R}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) R) (u v : Fin 3 → R) :
    ofFrame (g *ᵥ u) (g *ᵥ v) = g * ofFrame u v := by
  have h2 : (g *ᵥ u) ⨯₃ (g *ᵥ v) = g *ᵥ (u ⨯₃ v) :=
    mulVec_cross_mulVec_of_mem_specialOrthogonalGroup hg u v
  refine ext_col fun j ↦ ?_
  fin_cases j <;> simp [col_mul_eq_mulVec_col, h2]

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The frame matrix depends continuously on the frame. -/
@[fun_prop]
theorem continuous_ofFrame : Continuous fun p : (Fin 3 → R) × (Fin 3 → R) ↦ ofFrame p.1 p.2 := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases j
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd
  · fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, ofFrame_apply,
        Nat.succ_eq_add_one, Nat.reduceAdd, cross_apply, cons_val', cons_val_zero, cons_val_one,
        cons_val_fin_one, cons_val] <;>
      fun_prop

end TauCeti.Matrix.SpecialOrthogonalGroup
