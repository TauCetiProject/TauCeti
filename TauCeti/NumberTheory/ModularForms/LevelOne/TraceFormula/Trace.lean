/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
public import TauCeti.RingTheory.MvPolynomial.Trace

/-!
# Binary-form traces for arbitrary determinant matrices

Every integral matrix acts on binary forms over any commutative ring with trace
`P_{w+2}(trace M, det M)`, expressed using the Dickson polynomial `dickson 2 (det M) w`.
This applies to elliptic and nonsplit hyperbolic matrices, as well as to triangular and scalar
matrices. On even-degree forms it descends to the projective determinant-matrix module.

The linear extension expresses the ambient trace of any finite determinant-matrix sum as the
sum of its coefficients times these weight polynomials. This permits grouping the trace by
conjugacy classes, without a rational diagonalization assumption.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, Section 4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

/-- The trace of an integral matrix on binary forms is its Dickson weight polynomial. -/
theorem trace_binaryFormRep_eq_dickson_eval {K : Type*} [CommRing K] (w : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w) (binaryFormRep K w (op M)) =
      (Polynomial.dickson 2 (M.det : K) w).eval (M.trace : K) := by
  have hd : (M.map (Int.castRingHom K)).det = (M.det : K) := (Int.cast_det M).symm
  have ht : (M.map (Int.castRingHom K)).trace = (M.trace : K) :=
    (AddMonoidHom.map_trace (Int.castRingHom K) M).symm
  rw [binaryFormRep_op]
  simpa only [hd, ht] using
    trace_linearSubstRep_eq_dickson_eval w (M.map (Int.castRingHom K))

namespace TraceFormulaMatrixModule

variable {n : ℤ}

/-- A projective matrix has Dickson trace on even-degree binary forms over any commutative
ring. -/
theorem trace_binaryFormAction_eq_dickson_eval {K : Type*} [CommRing K]
    (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (binaryFormAction (R := K) hw (mk A)) =
      (Polynomial.dickson 2 (n : K) w).eval (A.1.trace : K) := by
  rw [binaryFormAction_mk, trace_binaryFormRep_eq_dickson_eval w A.1, A.2]

/-- A determinant-matrix basis element contributes its coefficient times the Dickson weight
polynomial to the trace of its action. -/
theorem trace_periodAction_single_eq_dickson_eval {K : Type*} [CommRing K]
    (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) (c : K) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction (R := K) hw (single (mk A) c)) =
      c * (Polynomial.dickson 2 (n : K) w).eval (A.1.trace : K) := by
  rw [periodAction_single, map_smul, smul_eq_mul,
    trace_binaryFormAction_eq_dickson_eval w hw A]

/-- The trace of a finite sum of determinant-matrix basis elements is the corresponding
coefficient-weighted sum of Dickson polynomials. Representatives need not be distinct modulo
sign. -/
theorem trace_periodAction_sum_eq_dickson_eval {K : Type*} [CommRing K]
    (w : ℕ) (hw : Even w) (s : Finset (TraceFormulaMatrix n))
    (c : TraceFormulaMatrix n → K) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction hw (∑ A ∈ s, single (mk A) (c A))) =
      ∑ A ∈ s, c A * (Polynomial.dickson 2 (n : K) w).eval (A.1.trace : K) := by
  simp only [map_sum, trace_periodAction_single_eq_dickson_eval w hw _]

end TraceFormulaMatrixModule

end TauCeti
