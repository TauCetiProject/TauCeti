/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.A2.Graded
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BettiPoincare

/-!
# The Betti Poincaré matrix of the one-arrow quiver

Give the path algebra of the `1 ⟶ 2` quiver (`TauCeti.Quiver.Kronecker` with a unique arrow) its
path-length grading and order the vertices source-first (`![src, tgt]`). For the graded vertex
simples `S₁, S₂`:

* `S₂` is already projective (`P₂ ≅ S₂`), so its Betti Poincaré column is `[0, 1]ᵀ`;
* `S₁` has the linear first-arrow resolution `0 ⟶ P₂{1} ⟶ P₁ ⟶ S₁ ⟶ 0`, so its Betti Poincaré
  column is `[1, q t]ᵀ`.

The resulting `2 × 2` Betti Poincaré matrix in the vertex-projective basis is

```text
B(q, t) = [1, 0; q t, 1],
```

matching the transpose of the bigraded Ext Poincaré matrix of `S₁, S₂`, supported entirely on the
Koszul diagonal `d = n`, and specializing at `q = 1` to `[1, 0; t, 1]`.

## Main definitions

* `TauCeti.Quiver.Kronecker.bettiPoincareMatrixA2`: the `2 × 2` Betti Poincaré matrix
  `!![1, 0; q t, 1]`.

## Main results

* `TauCeti.Quiver.Kronecker.submatrix_bettiPoincarePowerSeriesMatrix_eq_bettiPoincareMatrixA2`:
  identifies the categorical Betti Poincaré matrix of `1 ⟶ 2` with `bettiPoincareMatrixA2`.
* `TauCeti.Quiver.Kronecker.coeff_coeff_bettiPoincareMatrixA2_eq_zero_of_ne`: every entry of
  `bettiPoincareMatrixA2` vanishes off the diagonal `d = n`.
* `TauCeti.Quiver.Kronecker.map_laurentEval_one_bettiPoincareMatrixA2`: specializing `q = 1` yields
  `!![1, 0; t, 1]`.
-/

public section

noncomputable section

namespace TauCeti.Quiver.Kronecker

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v

/-- The `2 × 2` Betti Poincaré matrix `!![1, 0; q t, 1]` of the `1 ⟶ 2` path algebra in
source-first vertex order, with projectives indexing rows and resolved vertex simples indexing
columns. -/
def bettiPoincareMatrixA2 : Matrix (Fin 2) (Fin 2) (PowerSeries (LaurentPolynomial ℤ)) :=
  !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1]

/-- Entrywise formula for `TauCeti.Quiver.Kronecker.bettiPoincareMatrixA2`. -/
@[simp]
theorem bettiPoincareMatrixA2_apply (i j : Fin 2) :
    bettiPoincareMatrixA2 i j = !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1] i j := by
  rw [bettiPoincareMatrixA2]

/-- Every entry of `bettiPoincareMatrixA2` is supported on the Koszul diagonal `d = n`. -/
theorem coeff_coeff_bettiPoincareMatrixA2_eq_zero_of_ne (i j : Fin 2) {n : ℕ} {d : ℤ}
    (hnd : (n : ℤ) ≠ d) :
    (PowerSeries.coeff n (bettiPoincareMatrixA2 i j)).coeff d = 0 := by
  have hone : (PowerSeries.coeff n (1 : PowerSeries (LaurentPolynomial ℤ))).coeff d = 0 := by
    rw [PowerSeries.coeff_one]
    split_ifs with hn
    · subst hn
      rw [coeff_one, ite_eq_right_iff]
      exact fun hd ↦ absurd hd.symm hnd
    · simp
  fin_cases i <;> fin_cases j <;>
    simp only [bettiPoincareMatrixA2_apply, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact hone
  · simp
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs with hn
    · subst hn
      rw [mul_one, T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right_iff]
      exact fun hd ↦ absurd hd hnd
    · simp
  · exact hone

/-- Setting `q = 1` in `bettiPoincareMatrixA2` gives the ungraded Poincaré matrix
`!![1, 0; t, 1]`. -/
@[simp]
theorem map_laurentEval_one_bettiPoincareMatrixA2 :
    bettiPoincareMatrixA2.map
        (PowerSeries.map (laurentEval (R := ℤ) (1 : ℤˣ) : LaurentPolynomial ℤ →+* ℤ)) =
      !![1, 0; PowerSeries.X, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bettiPoincareMatrixA2]

variable {A : Type v} [Unique A] (k : Type u) [Field k]

/-- **The categorical Betti Poincaré matrix of the `1 ⟶ 2` path algebra is `!![1, 0; q t, 1]`.** -/
theorem submatrix_bettiPoincarePowerSeriesMatrix_eq_bettiPoincareMatrixA2 :
    (bettiPoincarePowerSeriesMatrix
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (PathAlgebra.gradedVertexSimple k (Kronecker A))
      (fun j ↦ PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A) j)).submatrix
        ![src, tgt] ![src, tgt] = bettiPoincareMatrixA2 := by
  classical
  let _ : Fintype A := Unique.fintype
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PathAlgebra.bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution,
      bettiPoincareMatrixA2, Nat.card_eq_fintype_card]

end TauCeti.Quiver.Kronecker
