/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Contribution

/-!
# The total upper-triangular contribution

The upper-triangular representatives of determinant `n > 0` are the matrices
`(a b; 0 d)` with `ad = n`, `a, d > 0`, and `0 ≤ b < d`.  The trace of such a matrix on
degree-`w` binary forms depends only on `(a, d)`, while its coefficient in Popa--Zagier's
explicit Hecke element is supported on `0 ≤ b ≤ d - a`.

This file sums the individual contribution computed in
`UpperTriangular/Contribution.lean`.  For a fixed factor pair `ad = n`, the coefficients sum
to `d - a` when `a < d`, to `1/6` when `a = d`, and to zero when `d < a`.  Thus the full
upper-triangular contribution is a divisor sum weighted by the Eichler--Selberg polynomial
`P_{w+2}(a+d,n)`.  This is the hyperbolic/parabolic part that enters the level-one trace
formula; the other conjugacy types are assembled separately.

## Main result

* `TauCeti.TraceFormulaMatrixModule.sum_trace_popaZagierElement_single_upperTriangularRep`:
  the sum over all canonical upper-triangular representatives as an explicit sum over the
  positive factor pairs of `n`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, §4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti.TraceFormulaMatrixModule

/-- The coefficient of the representative `(a b; 0 d)` in the positive-diagonal case, written
with natural-number indices. The extra condition `a ≤ d` in the endpoint branch records that
the corresponding integral interval is empty when `d < a`. -/
private def upperTriangularCoefficient (a b d : ℕ) : ℚ :=
  if 0 < b ∧ b < d - a then 1
  else if a = d ∧ b = 0 then 1 / 6
  else if a ≤ d ∧ b ≤ d - a then 1 / 2
  else 0

/-- For a fixed positive factor pair `(a, d)`, summing the Popa--Zagier coefficients over
`0 ≤ b < d` gives `d - a`, except that the scalar pair `a = d` has weight `1/6`. -/
private theorem sum_upperTriangularCoefficient (a d : ℕ) (ha : 0 < a) :
    ∑ b ∈ Finset.range d, upperTriangularCoefficient a b d =
      if a < d then ((d - a : ℕ) : ℚ) else if a = d then 1 / 6 else 0 := by
  rcases lt_trichotomy a d with had | rfl | hda
  · simp only [had, ↓reduceIte]
    have hr : 0 < d - a := Nat.sub_pos_of_lt had
    obtain ⟨r, hr'⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have hsub : Finset.range (d - a + 1) ⊆ Finset.range d := by
      intro b hb
      simp only [Finset.mem_range] at hb ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · rw [hr', Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [upperTriangularCoefficient]
      have hmiddle : ∀ b ∈ Finset.range r,
          (if 0 < b + 1 ∧ b + 1 < r + 1 then (1 : ℚ)
            else if a = d ∧ b + 1 = 0 then 1 / 6
            else if a ≤ d ∧ b + 1 ≤ r + 1 then 1 / 2 else 0) = 1 := by
        intro b hb
        simp only [Finset.mem_range] at hb
        simp [show b + 1 < r + 1 by omega]
      simp only [hr']
      rw [Finset.sum_eq_card_nsmul hmiddle, Finset.card_range]
      simp [had.ne, had.le, Nat.cast_add, Nat.cast_one]
      ring
    · intro b hbd hbr
      simp only [Finset.mem_range] at hbd hbr
      simp [upperTriangularCoefficient, had.ne, show ¬b < d - a by omega,
        show ¬b ≤ d - a by omega]
  · simp only [lt_self_iff_false, ↓reduceIte]
    rw [Finset.sum_eq_single 0]
    · simp [upperTriangularCoefficient]
    · intro b hb hb0
      simp [upperTriangularCoefficient, hb0]
    · simp [ha]
  · have hnotlt : ¬a < d := by omega
    have hne : a ≠ d := by omega
    have hnad : ¬a ≤ d := by omega
    simp only [hnotlt, hne, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro b hb
    simp [upperTriangularCoefficient, Nat.sub_eq_zero_of_le hda.le, hne, hnad]

/-- **The summed upper-triangular contribution.** Let `n > 0` and let `w` be even. Summing the
trace contributions of Popa--Zagier's explicit element over the canonical representatives
`(a b; 0 d)` gives

`Σ_{ad=n} c(a,d) P_{w+2}(a+d,n)`,

where `c(a,d) = d-a` for `a<d`, `c(a,a)=1/6`, and `c(a,d)=0` for `d<a`.

The scalar coefficient `1/6` is deliberately retained: the scalar conjugacy class is combined
with the other conjugacy types only in the final trace formula. -/
theorem sum_trace_popaZagierElement_single_upperTriangularRep (n w : ℕ) (hn : 0 < n)
    (hw : Even w) :
    ∑ A : ↥(FixedDetMatrices.reps (n : ℤ)),
        LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
          (periodAction hw
            (single (mk A.1) ((popaZagierElement ℚ n).coeff (mk A.1)))) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℚ)
          else if p.1 = p.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1 + p.2 : ℕ) : ℚ) := by
  classical
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let e := FixedDetMatrices.repsEquiv hnZ
  let contribution (A : ↥(FixedDetMatrices.reps (n : ℤ))) : ℚ :=
    LinearMap.trace ℚ (homogeneousSubmodule (Fin 2) ℚ w)
      (periodAction hw (single (mk A.1) ((popaZagierElement ℚ n).coeff (mk A.1))))
  calc
    ∑ A : ↥(FixedDetMatrices.reps (n : ℤ)), contribution A =
        ∑ x : Σ p : ↥n.divisorsAntidiagonal, Fin p.1.2, contribution (e.symm x) :=
      Fintype.sum_equiv e contribution (fun x ↦ contribution (e.symm x)) fun A ↦ by simp [e]
    _ = ∑ x : Σ p : ↥n.divisorsAntidiagonal, Fin p.1.2,
        upperTriangularCoefficient x.1.1.1 x.2 x.1.1.2 *
          (Polynomial.dickson 2 (n : ℚ) w).eval ((x.1.1.1 + x.1.1.2 : ℕ) : ℚ) := by
      apply Fintype.sum_congr
      intro x
      dsimp only [contribution]
      rw [trace_popaZagierElement_single_upperTriangularRep (by exact_mod_cast hn) w hw
        (e.symm x).1 (e.symm x).2]
      have hmatrix : (e.symm x).1.1 =
          !![(x.1.1.1 : ℤ), (x.2 : ℕ); 0, (n : ℤ).sign * x.1.1.2] := by
        simpa only [e] using FixedDetMatrices.coe_repsEquiv_symm_apply hnZ x
      have hsign : (n : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hn)
      rw [hmatrix, hsign]
      simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Int.natCast_pos, Int.natCast_eq_zero,
        one_div, Nat.cast_nonneg, true_and, Int.cast_add, Int.cast_natCast,
        ite_mul, one_mul, zero_mul, Nat.cast_add, upperTriangularCoefficient]
      by_cases had : x.1.1.1 ≤ x.1.1.2
      · have hsub : (x.1.1.2 : ℤ) - x.1.1.1 = (x.1.1.2 - x.1.1.1 : ℕ) :=
          (Int.ofNat_sub had).symm
        rw [hsub]
        norm_cast
        simp [had]
      · have hda : x.1.1.2 < x.1.1.1 := Nat.lt_of_not_ge had
        have hne : x.1.1.1 ≠ x.1.1.2 := Nat.ne_of_gt hda
        have hnotlt : ¬(x.2 : ℤ) < (x.1.1.2 : ℤ) - x.1.1.1 := by omega
        have hnotle : ¬(x.2 : ℤ) ≤ (x.1.1.2 : ℤ) - x.1.1.1 := by omega
        simp [had, hne, hnotlt, hnotle, Nat.sub_eq_zero_of_le hda.le]
    _ = ∑ p : ↥n.divisorsAntidiagonal,
        (if p.1.1 < p.1.2 then ((p.1.2 - p.1.1 : ℕ) : ℚ)
          else if p.1.1 = p.1.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) := by
      rw [Fintype.sum_sigma' (fun (p : ↥n.divisorsAntidiagonal) (b : Fin p.1.2) ↦
        upperTriangularCoefficient p.1.1 b p.1.2 *
          (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ))]
      apply Fintype.sum_congr
      intro p
      have ha : 0 < p.1.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal p.2)
      calc
        ∑ b : Fin p.1.2, upperTriangularCoefficient p.1.1 b p.1.2 *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) =
            ∑ b ∈ Finset.range p.1.2, upperTriangularCoefficient p.1.1 b p.1.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) :=
          by simpa using Fin.sum_univ_eq_sum_range (fun b : ℕ ↦
            upperTriangularCoefficient p.1.1 b p.1.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ)) p.1.2
        _ = _ := by
          rw [← Finset.sum_mul, sum_upperTriangularCoefficient p.1.1 p.1.2 ha]
    _ = _ := by
      simpa using n.divisorsAntidiagonal.sum_coe_sort (fun p ↦
        (if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℚ)
          else if p.1 = p.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1 + p.2 : ℕ) : ℚ))

end TauCeti.TraceFormulaMatrixModule
