/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Diagonal
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Basic

/-!
# Upper-triangular contributions to the level-one trace formula

For an upper-triangular matrix `M = (a b; 0 d)`, substitution on degree-`w` binary forms is
triangular in the monomial basis. Its diagonal entries are `aⁱdʷ⁻ⁱ`, independently of `b`, so
its trace is the Eichler--Selberg weight polynomial `P_{w+2}(a+d,ad)`.

This file also evaluates Popa--Zagier's explicit Hecke element on the canonical
upper-triangular representatives `FixedDetMatrices.reps n`. Its coefficient is `1` in the
interior of the interval `0 ≤ b ≤ d-a`, `1/2` at a non-scalar endpoint, `1/6` at a scalar
matrix, and `0` outside the interval. Combining the coefficient and trace calculations gives
the contribution of each representative to the ambient binary-form trace.

## Main results

* `TauCeti.trace_binaryFormRep_upperTriangular_eq_dickson_eval`: the binary-form trace of an
  upper-triangular matrix.
* `TauCeti.TraceFormulaMatrixModule.trace_binaryFormAction_upperTriangular_eq_dickson_eval`:
  the corresponding statement for a projective determinant matrix.
* `TauCeti.PopaZagier.weight_upperTriangular`: the unnormalised Popa--Zagier weight.
* `TauCeti.PopaZagier.upperTriangularCoeff`: the normalised coefficient of `(a b; 0 d)`.
* `TauCeti.TraceFormulaMatrixModule.coeff_popaZagierElement_upperTriangular`: the coefficient
  of a positive-diagonal upper-triangular matrix.
* `TauCeti.TraceFormulaMatrixModule.trace_popaZagierElement_single_upperTriangularRep`: the
  contribution of one canonical representative.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, §4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

/-- The trace of an upper-triangular determinant matrix on degree-`w` binary forms is the
Eichler--Selberg weight polynomial evaluated at its trace and determinant. In particular, the
trace is independent of the upper-right entry. -/
@[simp]
theorem trace_binaryFormRep_upperTriangular_eq_dickson_eval {R : Type*} [CommRing R]
    (w : ℕ) (a b d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op !![a, b; 0, d])) =
      (Polynomial.dickson 2 ((a * d : ℤ) : R) w).eval ((a + d : ℤ) : R) := by
  have hm : (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R) =
      !![(a : R), (b : R); 0, (d : R)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [binaryFormRep_op, hm]
  simpa only [Int.cast_add, Int.cast_mul] using
    trace_linearSubstRep_upperTriangular w (a : R) (b : R) (d : R)

namespace PopaZagier

/-- The unnormalised Popa--Zagier weight of a positive-diagonal upper-triangular matrix. The
four cases give weights `12`, `2`, `6`, and `0`; division by `12` produces the coefficient of
the explicit Hecke element. -/
theorem weight_upperTriangular (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) :
    weight !![a, b; 0, d] =
      if 0 < b ∧ b < d - a then 12
      else if a = d ∧ b = 0 then 2
      else if 0 ≤ b ∧ b ≤ d - a then 6 else 0 := by
  rw [weight]
  simp only [Matrix.of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one,
    Fin.isValue]
  grind [weight₁, weight₂, weight₃, weight₄, chainWeight₃]

/-- The coefficient of the positive-diagonal upper-triangular matrix `(a b; 0 d)` in
Popa--Zagier's explicit Hecke element: `1` in the interior of the interval `0 ≤ b ≤ d - a`,
`1/6` at a scalar matrix, `1/2` at a non-scalar endpoint, and `0` outside the interval. -/
def upperTriangularCoeff (a b d : ℤ) : ℚ :=
  if 0 < b ∧ b < d - a then 1
  else if a = d ∧ b = 0 then 1 / 6
  else if 0 ≤ b ∧ b ≤ d - a then 1 / 2
  else 0

/-- The defining equation for `upperTriangularCoeff`. -/
theorem upperTriangularCoeff_def (a b d : ℤ) :
    upperTriangularCoeff a b d =
      if 0 < b ∧ b < d - a then 1
      else if a = d ∧ b = 0 then 1 / 6
      else if 0 ≤ b ∧ b ≤ d - a then 1 / 2
      else 0 := (rfl)

end PopaZagier

namespace TraceFormulaMatrixModule

/-- A projective upper-triangular determinant matrix has the Dickson trace determined by its
matrix trace and determinant. -/
theorem trace_binaryFormAction_upperTriangular_eq_dickson_eval {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) (hA : A.1 1 0 = 0) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormAction (R := R) hw (mk A)) =
      (Polynomial.dickson 2 (n : R) w).eval ((A.1 0 0 + A.1 1 1 : ℤ) : R) := by
  rw [binaryFormAction_mk]
  have hm : A.1 = !![A.1 0 0, A.1 0 1; 0, A.1 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA]
  conv_lhs =>
    rw [hm, trace_binaryFormRep_upperTriangular_eq_dickson_eval]
  have had : A.1 0 0 * A.1 1 1 = n :=
    FixedDetMatrices.apply_zero_zero_mul_apply_one_one hA
  congr 2
  exact congrArg (Int.castRingHom R) had

/-- A single upper-triangular basis element contributes its coefficient times the Dickson trace
to the ambient binary-form space. -/
theorem trace_periodAction_single_upperTriangular_eq_dickson_eval {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) (hA : A.1 1 0 = 0) (c : R) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (periodAction (R := R) hw (single (mk A) c)) =
      c * (Polynomial.dickson 2 (n : R) w).eval ((A.1 0 0 + A.1 1 1 : ℤ) : R) := by
  rw [periodAction_single, map_smul, smul_eq_mul,
    trace_binaryFormAction_upperTriangular_eq_dickson_eval w hw A hA]

/-- The coefficient of a positive-diagonal upper-triangular matrix in Popa--Zagier's explicit
Hecke element. Interior matrices have coefficient `1`, non-scalar endpoints have coefficient
`1/2`, a scalar matrix has coefficient `1/6`, and all other matrices have coefficient `0`. -/
theorem coeff_popaZagierElement_upperTriangular {n : ℤ} (A : TraceFormulaMatrix n)
    (hc : A.1 1 0 = 0) (ha : 0 < A.1 0 0) (hd : 0 < A.1 1 1) :
    (popaZagierElement ℚ n).coeff (mk A) =
      PopaZagier.upperTriangularCoeff (A.1 0 0) (A.1 0 1) (A.1 1 1) := by
  rw [coeff_popaZagierElement_mk_of_pos A (Or.inr ⟨hc, ha⟩)]
  have hm : A.1 = !![A.1 0 0, A.1 0 1; 0, A.1 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  conv_lhs =>
    rw [hm, PopaZagier.weight_upperTriangular _ _ _ ha hd]
  rw [PopaZagier.upperTriangularCoeff_def]
  split_ifs <;> norm_num

/-- The contribution of one canonical upper-triangular representative to the trace of
Popa--Zagier's explicit element on the ambient binary-form space. -/
theorem trace_popaZagierElement_single_upperTriangularRep {n : ℤ} (hn : 0 < n)
    (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) (hA : A ∈ FixedDetMatrices.reps n) :
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
        (periodAction hw
          (single (mk A) ((popaZagierElement ℚ n).coeff (mk A)))) =
      PopaZagier.upperTriangularCoeff (A.1 0 0) (A.1 0 1) (A.1 1 1) *
        (Polynomial.dickson 2 (n : ℚ) w).eval ((A.1 0 0 + A.1 1 1 : ℤ) : ℚ) := by
  obtain ⟨hc, ha, -, -⟩ := hA
  have had : A.1 0 0 * A.1 1 1 = n :=
    FixedDetMatrices.apply_zero_zero_mul_apply_one_one hc
  have hd : 0 < A.1 1 1 := by nlinarith
  rw [trace_periodAction_single_upperTriangular_eq_dickson_eval w hw A hc,
    coeff_popaZagierElement_upperTriangular A hc ha hd]

end TraceFormulaMatrixModule

end TauCeti
