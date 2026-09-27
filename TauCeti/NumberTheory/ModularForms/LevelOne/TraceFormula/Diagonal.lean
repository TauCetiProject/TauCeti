/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.DoubleCoset
public import TauCeti.RingTheory.Polynomial.Dickson
public import Mathlib.LinearAlgebra.Trace
import TauCeti.RingTheory.MvPolynomial.Finrank

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

private theorem linearSubst_diagonal_monomial {R : Type*} [CommRing R]
    (a d : R) (s : Fin 2 →₀ ℕ) :
    linearSubst (Matrix.diagonal ![a, d]) (monomial s 1) =
      (a ^ s 0 * d ^ s 1) • monomial s 1 := by
  rw [linearSubst_eq_aeval, aeval_monomial, monomial_eq]
  simp only [Fin.sum_univ_two, Matrix.diagonal_apply]
  rw [s.prod_fintype (fun i k =>
    (C (if i = 0 then ![a, d] i else 0) * X 0 +
      C (if i = 1 then ![a, d] i else 0) * X 1) ^ k) (by simp)]
  rw [s.prod_fintype (fun i k => X i ^ k) (by simp)]
  simp [Fin.prod_univ_two, smul_eq_C_mul, mul_pow, mul_comm, mul_left_comm, mul_assoc]

private noncomputable def binaryFormMonomialBasis (R : Type*) [CommRing R] (w : ℕ) :
    Module.Basis {s : Fin 2 →₀ ℕ // s.degree = w} R
      (homogeneousSubmodule (Fin 2) R w) :=
  (basisRestrictSupport R {s : Fin 2 →₀ ℕ | s.degree = w}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) R w).symm)

private theorem coe_binaryFormMonomialBasis {R : Type*} [CommRing R] (w : ℕ)
    (s : {s : Fin 2 →₀ ℕ // s.degree = w}) :
    ((binaryFormMonomialBasis R w s : homogeneousSubmodule (Fin 2) R w) :
      MvPolynomial (Fin 2) R) = monomial s.1 1 := by
  let x : restrictSupport R {d : Fin 2 →₀ ℕ | d.degree = w} :=
    ⟨monomial s.1 1, (monomial_mem_restrictSupport R).2 (Or.inl s.2)⟩
  have hb : (basisRestrictSupport R {d : Fin 2 →₀ ℕ | d.degree = w}) s = x := by
    apply (Module.Basis.apply_eq_iff).2
    ext t
    -- The restricted monomial basis represents a polynomial by its coefficient function.
    change (monomial s.1 (1 : R)).coeff t.1 = (Finsupp.single s (1 : R)) t
    simp [coeff_monomial, Finsupp.single_apply, Subtype.ext_iff]
  simp only [binaryFormMonomialBasis, Module.Basis.map_apply]
  exact congrArg Subtype.val hb

private theorem binaryFormRep_diagonal_basis {R : Type*} [CommRing R] (w : ℕ)
    (a d : ℤ) (s : {s : Fin 2 →₀ ℕ // s.degree = w}) :
    binaryFormRep R w (op (Matrix.diagonal ![a, d])) (binaryFormMonomialBasis R w s) =
      ((a : R) ^ s.1 0 * (d : R) ^ s.1 1) • binaryFormMonomialBasis R w s := by
  apply Subtype.ext
  simp only [coe_binaryFormRep_apply, coe_binaryFormMonomialBasis, Submodule.coe_smul]
  have hm : (Matrix.diagonal ![a, d]).map (Int.cast : ℤ → R) =
      Matrix.diagonal ![(a : R), (d : R)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hm]
  exact linearSubst_diagonal_monomial (a : R) (d : R) s.1

/-- The trace of diagonal substitution on degree-`w` binary forms is the sum of its monomial
eigenvalues. This form of the result is useful before identifying the sum with a Dickson value. -/
private theorem trace_binaryFormRep_diagonal_eq_sum {R : Type*} [CommRing R]
    (w : ℕ) (a d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op (Matrix.diagonal ![a, d]))) =
      ∑ s ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag w,
        (a : R) ^ s 0 * (d : R) ^ s 1 := by
  classical
  have : Fintype {s : Fin 2 →₀ ℕ // s.degree = w} :=
    Fintype.ofFinset (p := {s : Fin 2 →₀ ℕ | s.degree = w})
      ((Finset.univ : Finset (Fin 2)).finsuppAntidiag w) (fun s => by
        simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  rw [LinearMap.trace_eq_matrix_trace R (binaryFormMonomialBasis R w), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, binaryFormRep_diagonal_basis,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  exact (Finset.sum_subtype ((Finset.univ : Finset (Fin 2)).finsuppAntidiag w)
    (by simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
    (fun s => (a : R) ^ s 0 * (d : R) ^ s 1)).symm

/-- The trace of a diagonal determinant matrix on binary forms is the Eichler–Selberg weight
polynomial evaluated at its trace and determinant. -/
theorem trace_binaryFormRep_diagonal_eq_dickson {R : Type*} [CommRing R]
    (w : ℕ) (a d : ℤ) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormRep R w (op (Matrix.diagonal ![a, d]))) =
      (Polynomial.dickson 2 ((a * d : ℤ) : R) w).eval ((a + d : ℤ) : R) := by
  rw [trace_binaryFormRep_diagonal_eq_sum]
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
    (fun i j => (a : R) ^ i * (d : R) ^ j) w]
  simpa only [Int.cast_add, Int.cast_mul] using
    (Polynomial.dickson_two_eval_add (x := (a : R)) (y := (d : R))
      (a := (a : R) * (d : R)) rfl w).symm

namespace TraceFormulaMatrixModule

/-- The projective diagonal class has the same Dickson trace on even-degree binary forms. -/
theorem trace_binaryFormAction_diagonal_eq_dickson {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (a d : ℤ) (h : a * d = n) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (binaryFormAction (R := R) hw (mk (TraceFormulaMatrix.diagonal a d h))) =
      (Polynomial.dickson 2 (n : R) w).eval ((a + d : ℤ) : R) := by
  have hm : (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal ![a, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [binaryFormAction_mk, TraceFormulaMatrix.val_diagonal, hm,
    trace_binaryFormRep_diagonal_eq_dickson, ← h]

/-- A diagonal basis element of the determinant-matrix module contributes its coefficient
times the Dickson trace to the ambient binary-form space. -/
theorem trace_periodAction_single_diagonal_eq_dickson {R : Type*} [CommRing R]
    {n : ℤ} (w : ℕ) (hw : Even w) (a d : ℤ) (h : a * d = n) (c : R) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w)
        (periodAction (R := R) hw (single (mk (TraceFormulaMatrix.diagonal a d h)) c)) =
      c * (Polynomial.dickson 2 (n : R) w).eval ((a + d : ℤ) : R) := by
  rw [periodAction_single, map_smul, smul_eq_mul,
    trace_binaryFormAction_diagonal_eq_dickson w hw a d h]

end TraceFormulaMatrixModule

end TauCeti
