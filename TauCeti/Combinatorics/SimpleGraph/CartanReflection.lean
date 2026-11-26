/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Simple reflection matrices of the generalized Cartan matrix of a simple graph

For a simple graph `G` on `V` and a ring `R`, subtracting the `r`-th row of
`SimpleGraph.graphCartanMatrix G R = (2 : R) • 1 - G.adjMatrix R` in the `r`-th coordinate defines
the reflection matrix `SimpleGraph.graphCartanReflectionMatrix G R r`. Built as a rank-one
perturbation `1 - Matrix.vecMulVec (Pi.single r 1) (G.graphCartanMatrix R r)` via
`TauCeti.oneSubVecMulVecGL`, these matrices are involutions of determinant `-1` satisfying
commutation at non-adjacent vertices and the length-three Artin–Tits braid relation at adjacent
vertices, with explicit `2 × 2` matrix evaluations on `SimpleGraph.pathGraph 2` (`A₂`).

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2d.
* V. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 3.
-/

public section

namespace SimpleGraph

open Matrix

section General

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The simple Cartan reflection matrix `1 - e_r ⊗ (G.graphCartanMatrix R r)` at vertex `r : V`,
representing `x ↦ x - (G.graphCartanMatrix R r ⬝ᵥ x) • e_r` under `Matrix.mulVec`. -/
def graphCartanReflectionMatrix (R : Type*) [Ring R] (r : V) : Matrix V V R :=
  1 - vecMulVec (Pi.single r 1) (G.graphCartanMatrix R r)

/-- Entry `(i, j)` of `SimpleGraph.graphCartanReflectionMatrix`. -/
@[simp]
theorem graphCartanReflectionMatrix_apply {R : Type*} [Ring R] (r i j : V) :
    G.graphCartanReflectionMatrix R r i j =
      (if i = j then 1 else 0) - if i = r then G.graphCartanMatrix R r j else 0 := by
  simp only [graphCartanReflectionMatrix, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, ite_mul, one_mul, zero_mul]

section Fintype

variable [Fintype V]

/-- On the coordinate vector `Pi.single j 1`, `G.graphCartanReflectionMatrix R r` subtracts
`G.graphCartanMatrix R r j` in coordinate `r`. -/
theorem graphCartanReflectionMatrix_mulVec_single {R : Type*} [Ring R] (r j : V) :
    (G.graphCartanReflectionMatrix R r).mulVec (Pi.single j 1) =
      Pi.single j 1 - G.graphCartanMatrix R r j • Pi.single r 1 := by
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, graphCartanReflectionMatrix_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    eq_comm]

/-- Every simple Cartan reflection matrix is an involution. -/
@[simp]
theorem graphCartanReflectionMatrix_mul_self {R : Type*} [Ring R] (r : V) :
    G.graphCartanReflectionMatrix R r * G.graphCartanReflectionMatrix R r = 1 := by
  simpa [graphCartanReflectionMatrix] using
    TauCeti.one_sub_vecMulVec_mul_inv (1 : Rˣ) (u := Pi.single r 1) (v := G.graphCartanMatrix R r)
      (by simp [one_add_one_eq_two])

/-- Over a commutative ring, every simple Cartan reflection matrix has determinant `-1`. -/
@[simp]
theorem det_graphCartanReflectionMatrix {R : Type*} [CommRing R] (r : V) :
    (G.graphCartanReflectionMatrix R r).det = -1 := by
  rw [graphCartanReflectionMatrix, TauCeti.det_one_sub_vecMulVec]
  simp only [dotProduct_single_one, graphCartanMatrix_apply, ↓reduceIte]
  ring

/-- Simple Cartan reflection matrices at non-adjacent vertices commute. -/
theorem graphCartanReflectionMatrix_mul_comm_of_not_adj {R : Type*} [Ring R] {r s : V}
    (hnadj : ¬ G.Adj r s) :
    G.graphCartanReflectionMatrix R r * G.graphCartanReflectionMatrix R s =
      G.graphCartanReflectionMatrix R s * G.graphCartanReflectionMatrix R r := by
  by_cases hrs : r = s
  · subst s; rfl
  · have hnadj' : ¬ G.Adj s r := fun h ↦ hnadj h.symm
    exact TauCeti.one_sub_vecMulVec_mul_comm (by simp [hrs, hnadj]) (by simp [Ne.symm hrs, hnadj'])

/-- Simple Cartan reflection matrices at adjacent vertices satisfy the length-three braid
relation. -/
theorem graphCartanReflectionMatrix_braid_of_adj {R : Type*} [Ring R] {r s : V}
    (hadj : G.Adj r s) :
    G.graphCartanReflectionMatrix R r * G.graphCartanReflectionMatrix R s *
        G.graphCartanReflectionMatrix R r =
      G.graphCartanReflectionMatrix R s * G.graphCartanReflectionMatrix R r *
        G.graphCartanReflectionMatrix R s :=
  TauCeti.one_sub_vecMulVec_braid
    (by simp [G.ne_of_adj hadj, (G.ne_of_adj hadj).symm, hadj, hadj.symm, one_add_one_eq_two])
    (by simp [G.ne_of_adj hadj, (G.ne_of_adj hadj).symm, hadj, hadj.symm, one_add_one_eq_two])

end Fintype

end General

/-- On `A₂ = SimpleGraph.pathGraph 2`, the Cartan reflection at vertex `0` is `!![-1, 1; 0, 1]`. -/
theorem graphCartanReflectionMatrix_pathGraph_two_zero (R : Type*) [Ring R] :
    (pathGraph 2).graphCartanReflectionMatrix R 0 = !![(-1 : R), 1; 0, 1] := by
  have h12 : (1 : R) - 2 = -1 := by
    rw [← one_add_one_eq_two, sub_add_eq_sub_sub, sub_self, zero_sub]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [graphCartanReflectionMatrix_apply, pathGraph_adj, h12]

/-- On `A₂ = SimpleGraph.pathGraph 2`, the Cartan reflection at vertex `1` is `!![1, 0; 1, -1]`. -/
theorem graphCartanReflectionMatrix_pathGraph_two_one (R : Type*) [Ring R] :
    (pathGraph 2).graphCartanReflectionMatrix R 1 = !![(1 : R), 0; 1, -1] := by
  have h12 : (1 : R) - 2 = -1 := by
    rw [← one_add_one_eq_two, sub_add_eq_sub_sub, sub_self, zero_sub]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [graphCartanReflectionMatrix_apply, pathGraph_adj, h12]

/-- Seidel–Thomas Check (`A₂`): both `R₀ * R₁ * R₀` and `R₁ * R₀ * R₁` equal `!![0, -1; -1, 0]`. -/
theorem graphCartanReflectionMatrix_pathGraph_two_braid (R : Type*) [Ring R] :
    (pathGraph 2).graphCartanReflectionMatrix R 0 *
        (pathGraph 2).graphCartanReflectionMatrix R 1 *
        (pathGraph 2).graphCartanReflectionMatrix R 0 = !![(0 : R), -1; -1, 0] ∧
      (pathGraph 2).graphCartanReflectionMatrix R 1 *
        (pathGraph 2).graphCartanReflectionMatrix R 0 *
        (pathGraph 2).graphCartanReflectionMatrix R 1 = !![(0 : R), -1; -1, 0] := by
  have hbraid := (pathGraph 2).graphCartanReflectionMatrix_braid_of_adj (R := R)
    (by simp [pathGraph_adj] : (pathGraph 2).Adj 0 1)
  have hABA : (pathGraph 2).graphCartanReflectionMatrix R 0 *
      (pathGraph 2).graphCartanReflectionMatrix R 1 *
      (pathGraph 2).graphCartanReflectionMatrix R 0 = !![(0 : R), -1; -1, 0] := by
    rw [graphCartanReflectionMatrix_pathGraph_two_zero,
      graphCartanReflectionMatrix_pathGraph_two_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hABA, hbraid.symm.trans hABA⟩

end SimpleGraph
