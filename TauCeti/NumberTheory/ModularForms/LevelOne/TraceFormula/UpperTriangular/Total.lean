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
`P_{w+2}(a+d,n)`.  This is an intermediate sum over canonical upper-triangular
representatives, not over conjugacy classes; it is one ingredient of the assembly of the
level-one trace formula, in which the conjugacy-type contributions are combined separately.

## Main result

* `TauCeti.PopaZagier.sum_upperTriangularCoeff`: the coefficient sum for one positive factor
  pair.
* `TauCeti.TraceFormulaMatrixModule.sum_trace_popaZagierElement_single_upperTriangularRep`:
  the sum over all canonical upper-triangular representatives as an explicit sum over the
  positive factor pairs of `n`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, §4.
-/

public section

open Matrix MvPolynomial MulOpposite MonoidAlgebra

namespace TauCeti

namespace PopaZagier

/-- For a fixed positive factor pair `(a, d)`, summing the Popa--Zagier coefficients over
`0 ≤ b < d` gives `d - a`, except that the scalar pair `a = d` has weight `1/6`. -/
theorem sum_upperTriangularCoeff (a d : ℕ) (ha : 0 < a) :
    ∑ b ∈ Finset.range d, upperTriangularCoeff a b d =
      if a < d then ((d - a : ℕ) : ℚ) else if a = d then 1 / 6 else 0 := by
  rcases lt_trichotomy a d with had | rfl | hda
  · simp only [had, ↓reduceIte]
    obtain ⟨r, hr⟩ : ∃ r, d = a + r + 1 := ⟨d - a - 1, by omega⟩
    have hsub : Finset.range (r + 2) ⊆ Finset.range d := by
      intro b hb
      simp only [Finset.mem_range] at hb ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · -- the two endpoints `b = 0` and `b = d - a` have coefficient `1/2`, the interior `1`
      have hmiddle : ∀ b ∈ Finset.range r,
          upperTriangularCoeff a ((b + 1 : ℕ) : ℤ) d = 1 := by
        intro b hb
        rw [Finset.mem_range] at hb
        grind [upperTriangularCoeff_def]
      have hfirst : upperTriangularCoeff a ((0 : ℕ) : ℤ) d = 1 / 2 := by
        grind [upperTriangularCoeff_def]
      have hlast : upperTriangularCoeff a ((r + 1 : ℕ) : ℤ) d = 1 / 2 := by
        grind [upperTriangularCoeff_def]
      have hda : d - a = r + 1 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_congr rfl hmiddle,
        hfirst, hlast, hda]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add,
        Nat.cast_one]
      ring
    · intro b hbd hbr
      simp only [Finset.mem_range] at hbd hbr
      grind [upperTriangularCoeff_def]
  · simp only [lt_irrefl, ↓reduceIte]
    rw [Finset.sum_eq_single 0]
    · grind [upperTriangularCoeff_def]
    · intro b _ hb0
      grind [upperTriangularCoeff_def]
    · intro h
      exact absurd (Finset.mem_range.mpr ha) h
  · simp only [hda.not_gt, hda.ne', ↓reduceIte]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    grind [upperTriangularCoeff_def]

end PopaZagier

namespace TraceFormulaMatrixModule

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
        PopaZagier.upperTriangularCoeff x.1.1.1 (x.2 : ℕ) x.1.1.2 *
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
      simp
    _ = ∑ p : ↥n.divisorsAntidiagonal,
        (if p.1.1 < p.1.2 then ((p.1.2 - p.1.1 : ℕ) : ℚ)
          else if p.1.1 = p.1.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) := by
      rw [Fintype.sum_sigma' (fun (p : ↥n.divisorsAntidiagonal) (b : Fin p.1.2) ↦
        PopaZagier.upperTriangularCoeff p.1.1 b p.1.2 *
          (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ))]
      apply Fintype.sum_congr
      intro p
      have ha : 0 < p.1.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal p.2)
      calc
        ∑ b : Fin p.1.2, PopaZagier.upperTriangularCoeff p.1.1 b p.1.2 *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) =
            ∑ b ∈ Finset.range p.1.2, PopaZagier.upperTriangularCoeff p.1.1 b p.1.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ) :=
          by simpa using Fin.sum_univ_eq_sum_range (fun b : ℕ ↦
            PopaZagier.upperTriangularCoeff p.1.1 b p.1.2 *
              (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1.1 + p.1.2 : ℕ) : ℚ)) p.1.2
        _ = _ := by
          rw [← Finset.sum_mul, PopaZagier.sum_upperTriangularCoeff p.1.1 p.1.2 ha]
    _ = _ := by
      simpa using n.divisorsAntidiagonal.sum_coe_sort (fun p ↦
        (if p.1 < p.2 then ((p.2 - p.1 : ℕ) : ℚ)
          else if p.1 = p.2 then 1 / 6 else 0) *
            (Polynomial.dickson 2 (n : ℚ) w).eval ((p.1 + p.2 : ℕ) : ℚ))

end TraceFormulaMatrixModule

end TauCeti
