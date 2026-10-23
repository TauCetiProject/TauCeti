/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
public import TauCeti.RingTheory.MvPolynomial.Trace

/-!
# Diagonal contributions to the level-one trace formula

A diagonal integral matrix with entries `a` and `d` acts on homogeneous binary forms of degree
`w` with eigenvalues `aⁱdʷ⁻ⁱ`, for `0 ≤ i ≤ w`. Their sum is the Dickson value
`P_{w+2}(a+d,ad)`. This supplies the diagonal trace calculation used in the split semisimple
case of the Eichler–Selberg trace formula. The formula also covers scalar matrices (`a = d`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

/-- The trace of a diagonal determinant matrix on binary forms is the Eichler–Selberg weight
polynomial evaluated at its trace and determinant. -/
@[simp]
theorem trace_binaryFormRep_diagonal_eq_dickson_eval {R : Type*} [CommRing R]
    (w : ℕ) (a d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op (Matrix.diagonal ![a, d]))) =
      (Polynomial.dickson 2 ((a * d : ℤ) : R) w).eval ((a + d : ℤ) : R) := by
  have hm : (Matrix.diagonal ![a, d]).map (Int.castRingHom R) =
      !![(a : R), 0; 0, (d : R)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [binaryFormRep_op, hm]
  simpa only [Int.cast_add, Int.cast_mul] using
    trace_linearSubstRep_upperTriangular w (a : R) 0 (d : R)

namespace TraceFormulaMatrixModule

-- These action formulas are not simp lemmas: `binaryFormAction_mk` and `periodAction_single`
-- simplify their left-hand sides first, so `simpNF` rejects either attribute here.
/-- The projective diagonal class has the same Dickson trace on even-degree binary forms. -/
theorem trace_binaryFormAction_diagonal_eq_dickson_eval {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (a d : ℤ) (h : a * d = n) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormAction (R := R) hw (mk (TraceFormulaMatrix.diagonal a d h))) =
      (Polynomial.dickson 2 (n : R) w).eval ((a + d : ℤ) : R) := by
  have hm : (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal ![a, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [binaryFormAction_mk, TraceFormulaMatrix.val_diagonal, hm,
    trace_binaryFormRep_diagonal_eq_dickson_eval, ← h]

/-- A diagonal basis element of the determinant-matrix module contributes its coefficient
times the Dickson trace to the ambient binary-form space. -/
theorem trace_periodAction_single_diagonal_eq_dickson_eval {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (a d : ℤ) (h : a * d = n) (c : R) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (periodAction (R := R) hw (single (mk (TraceFormulaMatrix.diagonal a d h)) c)) =
      c * (Polynomial.dickson 2 (n : R) w).eval ((a + d : ℤ) : R) := by
  rw [periodAction_single, map_smul, smul_eq_mul,
    trace_binaryFormAction_diagonal_eq_dickson_eval w hw a d h]

end TraceFormulaMatrixModule

end TauCeti
