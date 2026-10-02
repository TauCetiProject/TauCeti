/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Diagonal
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Basic
import TauCeti.RingTheory.MvPolynomial.Finrank

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

private theorem binaryFormRep_upperTriangular_basis_repr {R : Type*} [CommRing R] (w : ℕ)
    (a b d : ℤ) (s : {s : Fin 2 →₀ ℕ // s.degree = w}) :
    (TauCeti.homogeneousMonomialBasis (R := R) w).repr
        (binaryFormRep R w (op !![a, b; 0, d])
          (TauCeti.homogeneousMonomialBasis (R := R) w s)) s =
      (a : R) ^ s.1 0 * (d : R) ^ s.1 1 := by
  rw [homogeneousMonomialBasis_repr_apply]
  simp only [coe_binaryFormRep_apply, coe_homogeneousMonomialBasis]
  have hm : (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) =
      !![(a : R), (b : R); 0, (d : R)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hm]
  exact coeff_linearSubst_upperTriangular_monomial (a : R) (b : R) (d : R) s.1

private theorem trace_binaryFormRep_upperTriangular_eq_sum {R : Type*} [CommRing R]
    (w : ℕ) (a b d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op !![a, b; 0, d])) =
      ∑ s ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag w,
        (a : R) ^ s 0 * (d : R) ^ s 1 := by
  classical
  have : Fintype {s : Fin 2 →₀ ℕ // s.degree = w} :=
    Fintype.ofFinset (p := {s : Fin 2 →₀ ℕ | s.degree = w})
      ((Finset.univ : Finset (Fin 2)).finsuppAntidiag w) (fun s ↦ by
        simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  rw [LinearMap.trace_eq_matrix_trace R
    (TauCeti.homogeneousMonomialBasis (R := R) w), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
    binaryFormRep_upperTriangular_basis_repr]
  exact (Finset.sum_subtype ((Finset.univ : Finset (Fin 2)).finsuppAntidiag w)
    (by simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
    (fun s ↦ (a : R) ^ s 0 * (d : R) ^ s 1)).symm

/-- The trace of an upper-triangular determinant matrix on degree-`w` binary forms is the
Eichler--Selberg weight polynomial evaluated at its trace and determinant. In particular, the
trace is independent of the upper-right entry. -/
@[simp]
theorem trace_binaryFormRep_upperTriangular_eq_dickson_eval {R : Type*} [CommRing R]
    (w : ℕ) (a b d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op !![a, b; 0, d])) =
      (Polynomial.dickson 2 ((a * d : ℤ) : R) w).eval ((a + d : ℤ) : R) := by
  rw [trace_binaryFormRep_upperTriangular_eq_sum]
  let e : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ :=
    Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)
  have hs :
      (∑ s ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag w,
        (a : R) ^ s 0 * (d : R) ^ s 1) =
      ∑ p ∈ Finset.antidiagonal w, (a : R) ^ p.1 * (d : R) ^ p.2 := by
    apply Finset.sum_equiv e
    · intro s
      simp [e, Finset.mem_finsuppAntidiag, Finset.mem_antidiagonal]
    · intro s _
      rfl
  rw [hs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ (a : R) ^ i * (d : R) ^ j) w]
  simpa only [Int.cast_add, Int.cast_mul] using
    (Polynomial.dickson_two_eval_add (x := (a : R)) (y := (d : R))
      (a := (a : R) * (d : R)) rfl w).symm

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
      if 0 < A.1 0 1 ∧ A.1 0 1 < A.1 1 1 - A.1 0 0 then 1
      else if A.1 0 0 = A.1 1 1 ∧ A.1 0 1 = 0 then 1 / 6
      else if 0 ≤ A.1 0 1 ∧ A.1 0 1 ≤ A.1 1 1 - A.1 0 0 then 1 / 2
      else 0 := by
  rw [coeff_popaZagierElement_mk_of_pos A (Or.inr ⟨hc, ha⟩)]
  have hm : A.1 = !![A.1 0 0, A.1 0 1; 0, A.1 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  conv_lhs =>
    rw [hm, PopaZagier.weight_upperTriangular _ _ _ ha hd]
  split_ifs <;> norm_num

/-- The contribution of one canonical upper-triangular representative to the trace of
Popa--Zagier's explicit element on the ambient binary-form space. -/
theorem trace_popaZagierElement_single_upperTriangularRep {n : ℤ} (hn : 0 < n)
    (w : ℕ) (hw : Even w) (A : TraceFormulaMatrix n) (hA : A ∈ FixedDetMatrices.reps n) :
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
        (periodAction hw
          (single (mk A) ((popaZagierElement ℚ n).coeff (mk A)))) =
      (if 0 < A.1 0 1 ∧ A.1 0 1 < A.1 1 1 - A.1 0 0 then 1
        else if A.1 0 0 = A.1 1 1 ∧ A.1 0 1 = 0 then 1 / 6
        else if 0 ≤ A.1 0 1 ∧ A.1 0 1 ≤ A.1 1 1 - A.1 0 0 then 1 / 2
        else 0) *
        (Polynomial.dickson 2 (n : ℚ) w).eval ((A.1 0 0 + A.1 1 1 : ℤ) : ℚ) := by
  obtain ⟨hc, ha, -, -⟩ := hA
  have had : A.1 0 0 * A.1 1 1 = n :=
    FixedDetMatrices.apply_zero_zero_mul_apply_one_one hc
  have hd : 0 < A.1 1 1 := by nlinarith
  rw [trace_periodAction_single_upperTriangular_eq_dickson_eval w hw A hc,
    coeff_popaZagierElement_upperTriangular A hc ha hd]

end TraceFormulaMatrixModule

end TauCeti
